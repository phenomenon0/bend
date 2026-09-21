# vm-methods brief — builder: google/gemini-3.8-flash

Worktree: `~/Documents/Project/bend-work-vmstr-b` (branch `lane-vm-methods`).

Mission: implement the VM's curated string-methods set as **pure functions**
in ONE new file `demos/python/vm_methods.bend`. Do NOT edit any existing
`.bend` file — another lane owns `demos/python/vm.bend`. These functions become
the VM's method table when the wire-in slice lands (not yours).

Implement over the house `String` and `List<String>` APIs — grep
`bend2/base.bend` for the real names (`grep "def String\." bend2/base.bend`)
before using anything; do not invent names.

Functions to provide:
- `strip(s)`, `lstrip(s)`, `rstrip(s)` — whitespace trim
- `upper(s)`, `lower(s)`
- `split(s, sep) -> List<String>` — CPython: consecutive seps give empty
  fields; empty sep is an error (document it, don't handle it)
- `join(parts: List<String>, sep) -> String`
- `replace(s, a, b) -> String`
- `find(s, sub) -> Nat` — the index, or the length of `s` when absent (the
  VM has no negatives; document the -1 gap in a comment), plus
  `has(s, sub) -> Bool`
- `startswith(s, p) -> Bool`, `endswith(s, p) -> Bool`
- `count(s, sub) -> Nat`

Deliverables:
1. `demos/python/vm_methods.bend` — implementations; `All terms check.` clean
   (`bun -e 'import * as B from "./bend2/bend.ts"; const book = B.book_nil();
   await B.book_load(book, process.argv[1], "", new Map()); B.book_valid(book);' demos/python/vm_methods.bend`).
2. `demos/python/vm_methods_check.bend` — a program printing one line per
   fixed case. Invent your own case list (do NOT go looking in other
   directories — sibling worktrees are off-limits; stay inside THIS one).
   Run the same cases through `python3` and embed the CPython-verified
   expected text as the house `#|` block at the bottom of the check file.

## Rules that cost a compile round each (read first)

1. Defs are read top-to-bottom: no forward references; self-recursion only.
2. The shrinking argument goes FIRST; everything before it passes unchanged.
3. A `match` may not scrutinize computed values or locals — give the value
   its own def, or use multi-scrutinee `match a b:`.
4. Matching consumes the scrutinee; rebuild what you need.
5. `++` on a pattern binding / `+` on a param = reusable; unmarked values are
   single-use (affine).
6. No nested matches; flatten with multi-scrutinee matches, `_` per column.
7. No bare operators (`(1n + x : Nat)`); check every name against base.bend
   (there is no `Nat.inc`).
8. Big literals unary-expand: compose from small ones.

## Process (hard rules)

- NEVER write outside the repo: no `/tmp`, no `~/.local/share/opencode`;
  scratch under `tests/vm/_out/` (mkdir -p it).
- `BEND_NO_TELEMETRY=1` on every bend command. No push.
- **Build lock:** before ANY build, run `pgrep -f "bend2/main.ts"` — if another
  build is running (a different lane shares this machine), sleep 60 and
  re-check. NEVER two builds at once. A build takes minutes; a cap that fires
  under load is the box, not your code.
- Commit in slices, house voice, as you go. When done, write the exact state
  (commits, check status, what remains) into `tests/vm/_out/NEXT.md` and
  print DONE.
