# The House Style — proposal v2

One voice for every surface: commits, reports, PRs, docs, and the Chronicles.
v2 answers the review: claim clearly, footnote honestly, tell the story, pack
the evidence at the bottom, garnish a little.

## The rules

1. **The line tells the story.** Each headline carries the claim, the number,
   how it was implemented — and, whenever one exists, **the comparison with
   C** and **what it enables at the product layer** (one clause each). The
   reader should learn what just became possible, not only what it measured.
   Raw: `native I64, at 3,450× the old lowering, implemented as a second call
   site of the U64 template — one machine compare signs it.` →
   Dressed: `I64 is native — signed math is real now: crypto and hashes get
   machine-word arithmetic, and a signed compare is one machine compare, the
   same instruction C emits. ⚡3,450× the old lowering, net of the floor.`
   If a C comparison does not exist yet, say so in the footnote — never imply
   one.

2. **Claim it clearly. Caveat in the footnote.** The main line asserts what is
   true, plainly. Anything that needs a hedge gets an asterisk and a line at
   the bottom: `✱ subset: ints and control; strings are the next lane.`
   Never pre-soften the claim; never hide the caveat.

3. **Evidence goes underneath, not inside.** The prose stays readable; the
   receipt is appendable — a table, a script, a notebook, a lane report path.
   "Pack as much evidence as you want at the bottom."

4. **Numbers carry units, yardsticks, and provenance when cited.** `4.88 ms
   per 10M on C`, `1.02× of C at single core`, `against CPython 3.11.15`.
   Unmeasured → says *aimed*; measured → says where the measurement lives.

5. **Adjectives either resolve to a number or get cut.** `fast` is `0.62 ms`.
   `small` is `+82 −8`. If an adjective survives, it has earned its sentence
   with a receipt.

6. **Definite articles for shared things.** *the word, the floor, the lane,
   the battery, the gate, the cap.*

7. **Why, what it enables, what it traded away.** Any substantial piece says:
   why this was built, what it unlocks next, and which future trade-off it
   buys. The chronicle's job is exactly this story, in order.

8. **Format skeleton, in order:** The claim — the story (why/how) — the
   footnote line(s) — the evidence appendix. Reports keep their Verdict /
   Mechanism / Ledger bones inside this shape.

9. **Dry wit once per piece**, never at a fact's expense.

11. **Write like a person who did the work.** Vary the rhythm: a short
    sentence, then one that actually runs. Contractions are fine, fragments
    are fine. Em dashes: one per paragraph, tops. No parallel triads, no
    "not X but Y", no "here's the thing", no "genuinely/quietly/remarkably".
    Concrete nouns; verbs that do the work. An opinion is allowed when a
    fact pays for it.

    **Registers — two voices, one honesty.** *Front office* (reports, PRs,
    docs, headlines): the ruled shape, footnotes, garnish. *The Chronicles*
    (daily entries, chapter prose): written like a letter to a smart friend —
    looser, warmer, garnish only when a number deserves a spotlight.

    Not: "U64 is native — crypto and hashes run at machine speed, on CPU and
    device alike." (fine for a headline, claudism in a chapter)
    Better: "U64 is a machine number now. Crypto and hashes run at the speed
    the hardware always wanted; the old lowering is gone."

10. **Yield to the reviewer in five minutes.** Every sentence must be
    confirmable or falsifiable from the repo, fast. Otherwise: cut, or measure.

## Garnish — the A+C blend (RULED)

Footnotes always; capital-number caps when the number IS the story; glyphs
sparingly — one per piece, never a pattern.

Worked examples, in the ruled style:

> **U64 is native — crypto and hashes run at machine speed, on CPU and device
> alike.** ⚡3,363× the old lowering; on the increment loop it sits at the
> process floor, C's own volatile-fenced twin measuring 2.49 ms.
> ✅ gate 55/55 · 📐 add_comm, cited from the width-generic proof.

> **I64 is native — signed math is real now; one machine compare signs it,
> the same instruction C emits.** ⚡3,450× the old lowering, net of the floor.
>
> **3,450×.**
> ✱ no dedicated hand-C twin for the signed loop yet — the comparison is
> structural (same instruction) until one is run.

> **🐍 A Python subset, hosted in Bend** — 20/20 against CPython 3.11.15 on
> four lanes; fib(24) in 0.24 s, 12× the reference.
> ✱ subset: ints, control, defs; strings are the next lane.

Glyphs are seasoning — one or two per line. A capital number may stand alone
as its own line when the number IS the story.

## Not house style

- Marketing register: revolutionary, seamless, industry-leading.
- Hedged claims: "should be faster" without a number.
- Naked superlatives with no receipt.
- Logs-as-prose: narrating the work instead of stating what is true.
- Asterisk abuse: more than two caveat lines means the claim is wrong —
  rewrite the claim.
