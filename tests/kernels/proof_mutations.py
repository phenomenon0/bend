#!/usr/bin/env python3
"""Falsify the public proof contract with well-typed implementation and statement mutations."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
CHECK = """
import * as B from './bend2/bend.ts';
try {
  const book = B.book_nil();
  await B.book_load(book, process.argv[1], '', new Map());
  B.book_valid(book);
  if (book.hols || book.open) throw Error('unclosed implementation');
  console.log('All terms check.');
} catch(e) {
  console.error(e?.$ === 'Err' ? B.err_show(e) : String(e));
  process.exit(1);
}
"""
MUTATIONS = [
    ('seven actual digest leaves', 'sha256.bend', 'ANode{ALeaf{g}, ALeaf{h}}', 'ALeaf{g}'),
    ('reject exact capacity', 'buffer.bend', 'Nat.is_le(length, Nat.mul(4n, U32.to_nat(capacity)))',
     'Nat.is_lt(length, Nat.mul(4n, U32.to_nat(capacity)))'),
    ('accept oversize', 'buffer.bend', 'Nat.is_le(length, Nat.mul(4n, U32.to_nat(capacity)))', 'True{}'),
    ('wrong initialization', 'sha256.bend', '1779033703, 3144134277', '1779033702, 3144134277'),
]
# A weakened or falsified public statement must also be rejected: the gate is
# sensitive to the law text, not only to the implementation the text constrains.
STATEMENTS = [
    ('digest size claimed seven', 'List.length(&2, U32, O.words(S.digest(msg))) == 8n',
     'List.length(&2, U32, O.words(S.digest(msg))) == 7n'),
    ('rejection claims nothing', 'O.too_long(length, Array.size(U32, a))', 'False{}'),
]


def run(command):
    return subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=60)


def gate(entry):
    return run(['bun', 'tests/kernels/proof.ts', str(entry)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    control = gate(ROOT / 'demos/kernels/PROOF.bend')
    if control.returncode or 'Proof PASS:' not in control.stdout:
        raise SystemExit('control proof failed\n' + control.stdout + control.stderr)
    rows = []
    for name, file, before, after in MUTATIONS:
        with tempfile.TemporaryDirectory(prefix='kernels-proof-mutation-') as temporary:
            directory = Path(temporary)
            shutil.copytree(ROOT / 'demos/kernels', directory / 'kernels')
            source = directory / 'kernels' / file
            original = source.read_text()
            if original.count(before) != 1:
                raise SystemExit('non-unique anchor: ' + name)
            source.write_text(original.replace(before, after))
            checked = run(['bun', '-e', CHECK, str(directory / 'kernels/buffer.bend')])
            if checked.returncode or checked.stdout != 'All terms check.\n':
                raise SystemExit('ill-typed mutant: ' + name + '\n' + checked.stderr)
            started = time.monotonic()
            result = gate(directory / 'kernels/PROOF.bend')
            log = result.stdout + result.stderr
            if result.returncode != 1 or not all(s in log for s in ('Error:', 'Location:', '- expected :', 'Proof FAIL')):
                raise SystemExit('not a theorem rejection: ' + name + '\n' + log)
            rows.append(dict(mutation=name, strict_valid=True, verdict='proof rejected',
                             seconds=time.monotonic()-started, log=log))
            print(name + ': strict-valid, proof rejected', flush=True)
    for name, before, after in STATEMENTS:
        with tempfile.TemporaryDirectory(prefix='kernels-proof-statement-') as temporary:
            directory = Path(temporary)
            shutil.copytree(ROOT / 'demos/kernels', directory / 'kernels')
            source = directory / 'kernels/LAWS.bend'
            original = source.read_text()
            if original.count(before) != 1:
                raise SystemExit('non-unique statement anchor: ' + name)
            source.write_text(original.replace(before, after))
            # Laws are unproved here by construction, so only holes disqualify a statement.
            checked = run(['bun', '-e', CHECK.replace('book.hols || book.open', 'book.hols'),
                           str(source)])
            if checked.returncode or checked.stdout != 'All terms check.\n':
                raise SystemExit('ill-typed statement: ' + name + '\n' + checked.stderr)
            result = gate(directory / 'kernels/PROOF.bend')
            log = result.stdout + result.stderr
            if result.returncode != 1 or 'Error:' not in log or 'Proof FAIL' not in log:
                raise SystemExit('statement not rejected: ' + name + '\n' + log)
            rows.append(dict(statement=name, well_typed=True, verdict='proof rejected', log=log))
            print(name + ': well-typed statement, proof rejected', flush=True)
    # These test the gate boundary separately, not theorem sensitivity.
    for name, injection in [('unsafe', '@unsafe\ndef poison(x: U32) -> U32:\n  x\n'),
                            ('open', 'law unfinished:\n  {0 == 1 : U32}\n'),
                            ('hole', 'def unfinished() -> U32:\n  ?unfilled_value\n')]:
        with tempfile.TemporaryDirectory(prefix='kernels-proof-gate-') as temporary:
            directory = Path(temporary) / 'kernels'
            shutil.copytree(ROOT / 'demos/kernels', directory)
            entry = directory / 'PROOF.bend'
            entry.write_text(entry.read_text() + '\n' + injection)
            result = gate(entry)
            log = result.stdout + result.stderr
            # A named hole never reaches the hole counter: checking rejects it first.
            expected = {'unsafe': 'unsafe dependency', 'open': 'open=1',
                        'hole': '?unfilled_value'}[name]
            if result.returncode != 1 or expected not in log:
                raise SystemExit('gate did not reject as expected: ' + name + '\n' + log)
            rows.append(dict(gate_probe=name, verdict='gate rejected', log=log))
            print(name + ': gate rejected', flush=True)
    args.output.write_text(json.dumps(rows, indent=2) + '\n')
    print('Proof mutations PASS: 4 theorem probes, 2 statement probes, 3 gate probes')


if __name__ == '__main__':
    main()
