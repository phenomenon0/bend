# Evidence review: davidawad/bend-mode.el — compatibility pass

Date: 2026-09-20/21 (overnight session)
Reviewer context: omen fork working tree (`/home/omen/Documents/Project/bend`), tip `8f9b4105`
("native I64"), i.e. 2.0.17 sync + apple-stream perf lanes, upstream through 2.0.21.
Repo under review: github.com/davidawad/bend-mode.el (created 2026-09-20T23:26Z, MIT,
David Awad; src/bend-mode.el 286 lines + src/bend-mode-flymake.el ~200 lines).

## Verdict: GREEN — nothing broken; no issue warranted.
## Deliverable instead: verification sign-off + one doc nit (draft comment, below).

## Method (all mechanical)
1. All six `examples/` fetched and run through the tip CLI:
   `bun bend2/main.ts <file> --check-only` → **6/6 "All terms check."**
   (01-hello, 02-parallel-pow2 (fork/join + import Base), 03-shapes, 04-arrays,
   05-lists, 06-law-and-proof).
2. Error-format contract: captured the two real checker shapes from tip —
   parse error (`Location:` + `N>|` marker + context lines) and type error
   (`Location: main` name-variant + `N>|`). Their flymake parser's regexes
   (`(group (1+ digit)) ">" "|"`, `- expected/- observed` joining, line-1
   fallback for location-less blocks) match both exactly.
3. Keyword diff vs `bend2/bend.ts:80` (parser reserved list):
   def, type, law, match, case, do, return, for, exs, where, is, import,
   Type, Data, Kind, Quant. Mode's list is 1:1; extras `as` (import-only
   contextual) and `@unsafe` (attribute) — both defensible, not bugs.
4. Syntax table vs grammar: `#` line + depth-aware nested `#{ }#` (their
   propertize rescans whole buffer, self-documented tradeoffs; string-interior
   limitation documented with the ERT-hang root cause); `.`/`_` identifier
   chars; `K{x,y}` brace classes preserved.
5. Invocation contract: flymake runs `bend FILE --check-only`; uses a
   same-directory temp copy for unsaved buffers (imports are path-relative —
   correct awareness of `import ./x` semantics); discards stale results on
   supersession (standard idiom). `--check-only`: exists in main.ts (f194617b,
   "checks a file and its imports; run nothing"), present by v2.0.17, absent
   in 2.0.5.
6. Eglot wiring targets `bend2-fmt-lsp` — real, ships in the repo's
   `tools/bend-fmt-lsp/`. Matches their README's claim that upstream ships
   only a Sublime grammar (bend2/docs/bend.sublime-syntax) + formatting LSP.

## Honest residuals
- Not executed inside live Emacs (none installed on this host). Font-lock/
  indent verified by reading + their own ERT suite (canned `--check-only`
  outputs — no Emacs needed for those tests either).
- Indentation is "first-cut" by the file's own comments — the known soft spot.
- One diagnostic per check: their comment states this is the checker stopping
  at the first error (true of the CLI) — a design constraint, not a mode bug.
- Their README targets bend 2.0.22; our tree's newest tag is v2.0.21
  (upstream may have released 2.0.22 past our snapshot).

## Ecosystem takeaway for us
- The mode + #865 ("Expand to a compiler-backed Bend 2 LSP" by don2e4,
  closed with "publish as its own project") = the diagnostics-LSP door is
  open for ALL editors; nothing fills it today.
- Their flymake is explicitly a placeholder "to replace the day a real
  Bend 2 LSP reports diagnostics itself."

## Draft comment (NOT POSTED — awaiting go)
For https://github.com/davidawad/bend-mode.el (new issue or a comment):

---
Verified this against a current tree before it gets cold — nice work.

Checks run against a tip build (2.0.21-line): all six `examples/` pass
`bend FILE --check-only` ("All terms check.", including the fork/join and
law/proof ones), and the flymake parser's shape matches the current checker's
real output — the `N>|` marker, `- expected/- observed`, and the
`Location: <name>` variant all line up. The keyword set is 1:1 with
`bend2/bend.ts`'s reserved list at this tip (`as` and `@unsafe` are your two
additions — both defensible: `as` only reads on import lines, `@unsafe` is an
attribute).

One nit for the flymake section: a minimum-version note would help — the flag
isn't in bend 2.0.5 (a stale install here answered `unknown option
--check-only`) and is present by 2.0.17, so anyone on an older CLI would see a
confusing failure rather than diagnostics.

(Eglot wiring to `bend2-fmt-lsp` checks out too — it ships in the repo's
`tools/`.)
---
