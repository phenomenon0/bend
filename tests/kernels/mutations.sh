#!/usr/bin/env bash
# Isolated copies keep a failed probe from contaminating the shipped implementation.
set -euo pipefail
cd "$(dirname "$0")/../.."
python3 - "$@" <<'PY'
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

root = Path.cwd()
anchors = [
    ('sha256', 'initial state', '1779033703, 3144134277', '1779033702, 3144134277', 'sha_abc'),
    ('sha256', 'rotation', 'rotr(x, 6n)', 'rotr(x, 5n)', 'sha_abc'),
    ('sha256', 'padding marker', 'bs, 128 <>', 'bs, 0 <>', 'sha_empty'),
    ('sha256', 'padding boundary', 'Nat.is_ge(n, 56n)', 'Nat.is_ge(n, 57n)', 'sha_448'),
    ('chacha20', 'rotation', 'rotl(U32.xor(d, a1), 16n)', 'rotl(U32.xor(d, a1), 15n)', 'chacha_quarter'),
    ('chacha20', 'round count', 'rounds(10n, s)', 'rounds(9n, s)', 'chacha_block'),
    ('chacha20', 'constant', '1634760805, 857760878', '1634760804, 857760878', 'chacha_zero'),
    ('chacha20', 'counter advance', 'U32.add(counter, 1)', 'U32.add(counter, 2)', 'chacha_65'),
]

def battery(directory):
    return subprocess.run(['bash', 'tests/kernels/run.sh'], cwd=root,
        env={**os.environ, 'KERNELS_DIR': str(directory)}, capture_output=True,
        text=True, timeout=600)

# A stale pin or broken compiler must fail the control, not earn a killed mutant.
control = battery(root / 'tests/kernels')
if control.returncode:
    raise SystemExit('control battery failed\n' + control.stdout + control.stderr)
print(control.stdout, end='', flush=True)
rows = []
for kernel, name, before, after, fixture in anchors:
    with tempfile.TemporaryDirectory(prefix='bend-kernel-mutation-') as tmp:
        tree = Path(tmp)
        shutil.copytree(root / 'demos/kernels', tree / 'demos/kernels')
        cases = tree / 'tests/kernels'
        cases.mkdir(parents=True)
        shutil.copy2(root / f'tests/kernels/{fixture}.bend', cases)
        source = tree / f'demos/kernels/{kernel}.bend'
        original = source.read_text()
        if original.count(before) != 1:
            raise SystemExit(f'non-unique mutation anchor: {kernel}/{name}')
        source.write_text(original.replace(before, after))
        start = time.monotonic()
        result = battery(cases)
        log = result.stdout + result.stderr
        if result.returncode != 1 or f'ok   {fixture} [check]' not in log:
            raise SystemExit(f'{kernel}/{name}: mutant not strictly well-typed\n{log}')
        for lane in ('interpret', 'js', 'c'):
            if f'FAIL {fixture} [{lane}] status=0\n' not in log:
                raise SystemExit(f'{kernel}/{name}: no clean output mismatch in {lane}\n{log}')
        rows.append(dict(kernel=kernel, mutation=name, fixture=fixture,
            strict_check=True, rejected_lanes=['interpret', 'js', 'c'],
            seconds=time.monotonic()-start, log=log))
        print(f'killed {kernel}/{name}: strict-valid, 3 output mismatches', flush=True)
if len(sys.argv) == 2:
    Path(sys.argv[1]).write_text(json.dumps(rows, indent=2) + '\n')
print(f'Mutations PASS: {len(rows)}/{len(anchors)}')
PY
