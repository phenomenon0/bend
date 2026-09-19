# Text demos

Four small tools over Bend's first-class strings. Each reads the file named by
`$FILE` once (`File.read`), does its work on views of that one string, prints
its result on stdout and its own clock (`IO.now`, milliseconds) on stderr.
Every number below was measured; nothing is printed that was not.

| Run | Does |
|---|---|
| `demos/text/run_md_to_html.sh` | `md2html.bend`: Markdown to HTML, on this repo's `README.md` and a generated 20 MiB document; diffs both against `md2html.py`, an independent Python oracle |
| `demos/text/run_topwords.sh` | `topwords.bend`: total / unique / top-20 words, on `/usr/share/dict/linux.words` and a generated 200 MiB prose corpus |
| `demos/text/run_bendgrep.sh` | `bendgrep.bend`: count lines containing `$NEEDLE`, show the first 5 with line numbers, on a generated 500 MiB log; checks the count against `grep -c` |
| `demos/text/run_slices.sh` | `slices.bend`: the instant-slice tour of a 256 MiB string, then 1,000,000 scattered slice+parse visits |
| `demos/text/lanes.sh` | self-test: all four on small inputs, CLI = emitted JS = emitted C, plus the oracles |

Each script generates its input on first use into `$CORPUS` (default
`~/videokit-corpus`, about 1 GB for all four; `rm -r` it when done), builds the
C binary into `$BIN` (default `/tmp/bend-text-demos`) when the source is newer,
runs it under `/usr/bin/time -v`, and prints wall time and peak RSS. Knobs:
`MIB=` (input size), `NEEDLE=`, `N=` (visits). By hand:

```sh
bun bend2/main.ts demos/text/bendgrep.bend -o /tmp/bendgrep
FILE=/var/log/messages NEEDLE=error /tmp/bendgrep --gpu off
```

## Measured

C lane, `--gpu off`, Ryzen 7 7700X (8 cores, 16 threads), Linux, busy with other work
(load average 14 to 20) during every run: two runs each, quiet-ish and loaded.

| Demo | Input | Wall | Program's own clock | Peak RSS |
|---|---|---|---|---|
| md2html | README.md, 9.5 KB | 0.00 s | read 0 to 2 ms, render+print 0 to 1 ms | 2 MB |
| md2html | big-20.md, 20 MiB, 504,499 lines out | 0.76 to 1.33 s | read 49 to 90 ms, render+print 696 to 1192 ms | 472 MB |
| topwords | linux.words, 4.8 MB, 480,374 words, 461,717 unique | 4.85 to 6.11 s | count+rank 4825 to 6080 ms | 136 MB |
| topwords | prose-200.txt, 200 MiB, 20,211,498 words, 70,852 unique | 16.28 to 20.85 s | read 683 to 843 ms, count+rank 15448 to 19822 ms | 2.8 GB |
| bendgrep | app-500.log, 500 MiB, 9,010,000 lines, 180,512 hits | 3.36 to 4.36 s | read 1281 to 1603 ms, search 1961 to 2592 ms | 2.5 GB |
| slices | records-256.txt, 256 MiB, 16,777,216 records | 0.89 to 1.13 s | load 620 to 782 ms, tour 0 ms, 1,000,000 deep slices 212 to 274 ms | 1.3 GB |

For scale, same machine: the Python oracle renders big-20.md in 1.12 s,
`collections.Counter` does prose-200 in 9.35 s, `grep -c` does the log in 0.1 s.
Bend's md2html is ahead of Python; topwords and bendgrep are not ahead of the
C tools. A character is a 4-byte cell, so RSS is about 4x the file plus the
read buffer.

## What to say on camera

- **md2html**: "A real Markdown renderer, 185 lines of Bend. It renders this
  repo's README, then a 20-megabyte document in about a second, and the output
  is byte-identical to a Python implementation of the same spec."
- **topwords**: "Lowercase, split into words, count in a Map, sort. Twenty
  million words in about twenty seconds, and the counting is a fork-join: `x y
  = fork(..) fork(..)` spreads it over every core, no threads, no locks."
- **bendgrep**: "Nine million log lines, half a gigabyte. Every line is a view
  into the one string that was read, never a copy. Same count as grep."
- **slices**: "The file spells its own offsets, so you can see the deep reads
  are right. Loading 256 MB takes most of a second, because that is the only
  step that touches every character. After that: length, get, take, drop, slice
  from either end, anywhere in the string, do not register on a millisecond
  clock, and a million scattered slices, each parsed and checked, take a
  quarter of a second: about 250 nanoseconds each."

## Limits found

- A view counts a reference on its string and counts are 24-bit: 16.7M live
  views of one string fail-stop. topwords therefore takes `words` line by line.
- The JS lane slices by walking code points (O(offset)) and recurses on the
  machine stack (overflows ranking about 30k unique words), so `lanes.sh` uses
  small inputs and `N=200`. The C lane has neither limit.
- `Map` is a bitwise trie written in Bend; it is 94% of topwords' time.
