#!/usr/bin/env python3
# bench/net/room.py -- what a WebSocket room costs: a message's way to
# every member, and the server's CPU while nobody talks.
#
#   python3 bench/net/room.py ./room [--members 50] [--msgs 200] [--idle 10]
#
# ./room is net/examples/chat_server.bend built (`bend ... -o room`). It is
# started alone, on one thread. `members` clients join; one of them says
# `msgs` messages, 20 ms apart, each carrying its send time, and every
# member's arrival is timed: the latency is send to the last member's
# arrival (the room's p50 and p99 over the messages), and the mean over
# members. Then everyone stays joined and quiet for `idle` seconds, and
# the server's CPU in that time (utime + stime from /proc) is the idle
# cost.
import argparse
import asyncio
import os
import statistics
import subprocess
import sys
import time

import websockets

ap = argparse.ArgumentParser()
ap.add_argument("room")
ap.add_argument("--members", type=int, default=50)
ap.add_argument("--msgs", type=int, default=200)
ap.add_argument("--idle", type=float, default=10.0)
ap.add_argument("--port", type=int, default=18900)
a = ap.parse_args()

TICK = os.sysconf("SC_CLK_TCK")


def cpu(pid):
    with open(f"/proc/{pid}/stat") as f:
        fs = f.read().rsplit(")", 1)[1].split()
    return (int(fs[11]) + int(fs[12])) / TICK


async def member(url, seen, n):
    ws = await websockets.connect(url, max_size=None, ping_interval=None)
    async def listen():
        async for m in ws:
            t = time.perf_counter()
            k = int(m.split(" ", 1)[0])
            seen.setdefault(k, []).append(t)
    return ws, asyncio.create_task(listen())


async def main():
    srv = subprocess.Popen([a.room, "--port", str(a.port), "--threads", "1"],
                           stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
    try:
        url = f"ws://127.0.0.1:{a.port}/room"
        for _ in range(100):
            try:
                ws, _l = await member(url, {}, 0)
                await ws.close()
                break
            except OSError:
                await asyncio.sleep(0.05)
        seen = {}
        ms = [await member(url, seen, i) for i in range(a.members)]
        await asyncio.sleep(0.5)
        sent = {}
        say = ms[0][0]
        for k in range(a.msgs):
            sent[k] = time.perf_counter()
            await say.send(f"{k} x")
            await asyncio.sleep(0.02)
        await asyncio.sleep(1.0)
        last, mean, lost = [], [], 0
        for k in range(a.msgs):
            ts = seen.get(k, [])
            lost += a.members - len(ts)
            if ts:
                last.append((max(ts) - sent[k]) * 1000)
                mean.append((statistics.fmean(ts) - sent[k]) * 1000)
        c0 = cpu(srv.pid)
        await asyncio.sleep(a.idle)
        c1 = cpu(srv.pid)
        q = statistics.quantiles(last, n=100)
        print(f"members {a.members}, messages {a.msgs}: to the last member p50 {q[49]:.1f} ms,"
              f" p99 {q[98]:.1f} ms; mean member {statistics.fmean(mean):.1f} ms;"
              f" lost {lost}; idle CPU {100 * (c1 - c0) / a.idle:.1f}% of a core")
        for ws, t in ms:
            t.cancel()
            await ws.close()
    finally:
        srv.terminate()
        srv.wait()


asyncio.run(main())
