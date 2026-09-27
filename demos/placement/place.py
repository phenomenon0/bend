#!/usr/bin/env python3
"""Measure a run's energy on both rails, and route a run by the measured table.

  place.py measure OUT UNIT M REPS [TABLE]
                                     run $BIN/main --gpu UNIT REPS times back
                                     to back at PLACE_COLS=M; append a row to
                                     OUT/TABLE (table.jsonl), samples to OUT/
  place.py route OUT M               predict J/run on each unit from the table,
                                     print the decision, print the unit

CPU rail: /run/power-sampler/latest.json (package-0 energy_uj, written once a
second). GPU: `nvidia-smi -lms 100` power.draw.instant, stamped on arrival and
integrated by trapezoid. One window serves both rails: it opens on a sampler
tick, closes on the first tick after the GPU is back near idle (its clocks stay
up for seconds after a run, and that tail is the run's). Idle draw on both
rails is measured for ~4 s just before each batch and subtracted over the
whole window. Every run's four lines must equal the twin's, or it fails.
"""

import json, math, os, subprocess, sys, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
RAIL = "/run/power-sampler/latest.json"
WRAP = int(open("/sys/class/powercap/intel-rapl:0/max_energy_range_uj").read())
ROWS = 16384


def rail():
    while True:
        try:
            d = json.load(open(RAIL))
            return d["ts"], d["energy_uj"]
        except (ValueError, KeyError):
            time.sleep(0.01)


def tick():  # the next sampler write
    t0, _ = rail()
    while True:
        time.sleep(0.01)
        t, e = rail()
        if t != t0:
            return t, e


def joules(e0, e1):
    return ((e1 - e0) % WRAP) / 1e6


class Gpu:
    def __init__(self):
        self.s = []
        self.p = subprocess.Popen(
            [
                "nvidia-smi",
                "--query-gpu=power.draw.instant",
                "--format=csv,noheader,nounits",
                "-lms",
                "100",
            ],
            stdout=subprocess.PIPE,
            text=True,
        )
        threading.Thread(target=self.read, daemon=True).start()

    def read(self):
        for line in self.p.stdout:
            self.s.append((time.time(), float(line)))

    def within(self, t0, t1):
        return [(t, w) for t, w in self.s if t0 <= t <= t1]

    def integral(self, t0, t1):  # trapezoid; the edges hold the nearest sample
        xs = self.within(t0, t1)
        pts = [(t0, xs[0][1])] + xs + [(t1, xs[-1][1])]
        return sum((b[0] - a[0]) * (a[1] + b[1]) / 2 for a, b in zip(pts, pts[1:]))


def idle(g):  # ~4 s of both rails at rest, between two sampler ticks
    ta, ea = tick()
    time.sleep(3.5)
    tb, eb = tick()
    xs = [w for _, w in g.within(ta, tb)]
    return joules(ea, eb) / (tb - ta), sum(xs) / len(xs)


def measure(out, unit, m, reps, table="table.jsonl"):
    bin = os.environ["BIN"]
    env = dict(os.environ, PLACE_COLS=str(m))
    want = f"{bin}/twin_{m}.txt"  # the twin runs once per size
    if not os.path.exists(want):
        open(want, "w").write(
            subprocess.run(
                [f"{bin}/twin"], env=env, capture_output=True, text=True, check=True
            ).stdout
        )
    twin = open(want).read()
    g = Gpu()
    pre_c, pre_g = idle(g)
    t0, e0 = tick()
    walls = []
    for _ in range(reps):
        s = time.time()
        got = subprocess.run(
            [f"{bin}/main", "--gpu", unit], env=env, capture_output=True, text=True
        ).stdout
        walls.append(time.time() - s)
        if got != twin:
            sys.exit(
                f"FAIL m={m} --gpu {unit}: printed {got.split()} but the twin printed {twin.split()}"
            )
    end = time.time()
    while time.time() - end < 15:  # settle: 1 s of GPU samples under idle + 4 W
        time.sleep(0.2)
        last = g.within(time.time() - 1, time.time())
        if time.time() - end > 1 and last and max(w for _, w in last) < pre_g + 4:
            break
    t1, e1 = tick()
    post_c, post_g = idle(g)
    g.p.kill()
    win = t1 - t0
    idle_c, idle_g = (pre_c + post_c) / 2, (pre_g + post_g) / 2
    cpu = joules(e0, e1) - idle_c * win
    gpu = g.integral(t0, t1) - idle_g * win
    err = (abs(pre_c - post_c) + abs(pre_g - post_g)) / 2 * win / reps
    row = dict(
        unit=unit,
        m=m,
        reps=reps,
        macs=ROWS * m,
        wall_s=sorted(walls)[len(walls) // 2],
        window_s=round(win, 3),
        idle_cpu_w=[round(pre_c, 2), round(post_c, 2)],
        idle_gpu_w=[round(pre_g, 2), round(post_g, 2)],
        cpu_j=round(cpu, 2),
        gpu_j=round(gpu, 2),
        j_run=round((cpu + gpu) / reps, 3),
        err_j=round(err, 3),
        gpu_samples=len(g.within(t0, t1)),
        load=open("/proc/loadavg").read().split()[0],
        four=got.split(),
        twin=twin.split(),
        rail=[t0, e0, t1, e1],
    )
    row["nj_mac"] = round(row["j_run"] / row["macs"] * 1e9, 3)
    with open(f"{out}/{table}", "a") as f:
        f.write(json.dumps(row) + "\n")
    with open(f"{out}/gpu_{unit}_{m}.csv", "w") as f:
        f.writelines(f"{t:.3f},{w}\n" for t, w in g.s)
    print(
        f"{m:>8} {unit:>4} {reps:>4} {row['wall_s']:>8.3f} {win:>7.2f} {idle_c:>6.1f} {idle_g:>5.1f}"
        f" {cpu:>8.1f} {gpu:>8.1f} {row['j_run']:>9.3f} {err:>7.3f} {row['nj_mac']:>8.3f}"
    )


def predict(rows, m):  # log-log linear through the two nearest measured sizes
    pts = sorted((r["m"], r["j_run"]) for r in rows)
    lo = max([p for p in pts if p[0] <= m] or pts[:1])
    hi = min([p for p in pts if p[0] >= m and p != lo] or pts[-1:])
    if lo[0] == hi[0]:
        return lo[1]
    if (
        min(lo[1], hi[1]) <= 0
    ):  # net J at or under the noise floor: interpolate linearly
        return lo[1] + (hi[1] - lo[1]) * (m - lo[0]) / (hi[0] - lo[0])
    f = (math.log(m) - math.log(lo[0])) / (math.log(hi[0]) - math.log(lo[0]))
    return math.exp(math.log(lo[1]) + f * (math.log(hi[1]) - math.log(lo[1])))


def route(out, m):
    rows = [json.loads(l) for l in open(f"{out}/table.jsonl")]
    j = {u: predict([r for r in rows if r["unit"] == u], m) for u in ("off", "on")}
    pick = min(j, key=j.get)
    name = {"off": "CPU (16 threads)", "on": "GPU (RTX 3090)"}
    print(
        f"route m={m} ({ROWS * m:,} MACs): predicted J/run  CPU {j['off']:.3f}  GPU {j['on']:.3f}"
        f"  -> {name[pick]}",
        file=sys.stderr,
    )
    print(pick)


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == "measure":
        measure(a[1], a[2], int(a[3]), int(a[4]), *a[5:])
    elif a[0] == "route":
        route(a[1], int(a[2]))
