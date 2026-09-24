# std: CSV, JSON, text, dates and gzip for Bend

`std/` is a small standard library that runs on **released Bend** (the
`bend` that bend-lang.com installs, canon's stock runtime) and on this
repo's runtime alike. Copy the `std/` directory next to your program and
import what you need by path:

    import ./std/csv.bend as Csv
    import ./std/json_value.bend as Json

| file | what it gives you |
|---|---|
| `csv.bend` | RFC 4180 reader and writer: dialects (comma, tab, CRLF-only, header), streaming over reads, `read_file`, `fold_file` (one record at a time, in bounded memory), `show` |
| `json_value.bend` | JSON as a tree: `parse` under depth and byte budgets, `get`, `at`, `path`, `to_nat`, `to_f32`, `show` (canonical text) |
| `json.bend` | JSON as a stream of events, for documents too big to hold as a tree; `skip`, `raw` |
| `text.bend` | UTF-8 `decode`/`encode`/`valid`, `nat`/`u32`/`f32` from text, `pad_start`, `pad_end`, `split_on`, `replace`, `hash` |
| `time.bend` | UTC dates: `iso`, `iso.ms`, `http` (IMF-fixdate), `date`, `day`, `from`, `weekday`, `iso.read` |
| `gzip.bend`, `deflate.bend` | RFC 1952 and 1951, both ways, with an output cap against bombs |
| `bytes.bend` | the byte interface everything above is written against, plus `read_file` and `write_file` |
| `reader.bend` | the reader kit: a byte machine fed any split of its input, and the laws every such reader gets |

Everything works on byte strings: a `String` whose every `Char` is below
256, which is what a file read hands back. Text you print is code points
(`IO.print` writes each `Char` as UTF-8), so decode bytes before you print
them: `Text.decode(field)`. Base's own `String` functions (`String.eq`,
`String.split`, `String.join`, `String.trim`, ...) work on both.

## Quick start

The examples live in `std/examples/` and run from the directory that holds
`std/` (so they import `../csv.bend`; your own program next to `std/`
writes `./std/csv.bend`). Every snippet below is copied from its example
file, and every example runs on released Bend in the interpreter, the JS
lane and the C lane (`tests/std/readme.py` checks both):

    bend std/examples/csv_rows.bend                  # interpreted
    bend std/examples/csv_rows.bend -o rows && ./rows  # compiled to C

### Read a CSV file into rows

From `std/examples/csv_rows.bend`:

```bend
def table(o: Csv.Out) -> String:
  match o:
    case Csv.Read{h, rs}:
      head(h) ++ rows(rs)
    case Csv.Refused{at, why}:
      "refused at byte " ++ Nat.show(at) ++ ": " ++ Csv.why.show(why)
```

```bend
def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    # excel(): RFC 4180 as CPython reads it; with_header: the first row is the header
    r : Result<&1, &1, U32 & String, Csv.Out> <- Csv.read_file(path(args), Csv.with_header(Csv.excel()))
    IO.print(show(r))
```

A record is a `List<&2, String>` of its fields. For a file too big to keep,
`Csv.fold_file(~A, ~f, path, dialect, chunk, a)` hands each record to `f`
as it completes and keeps nothing.

### Parse JSON and get fields

From `std/examples/json_fields.bend`:

```bend
def fields(+j: Json.Json) -> String:
  "name: " ++ str(Json.string(Json.get(j, "name"))) ++
  "\nowner: " ++ str(Json.string(Json.path(j, ["owner", "login"]))) ++
  " in " ++ str(Json.string(Json.path(j, ["owner", "city"]))) ++
  "\nstars: " ++ num(Json.nat(Json.get(j, "stars"))) ++
  "\nsecond tag: " ++ str(Json.string(Json.index(Json.get(j, "tags"), 1n))) ++
  "\nlicense: " ++ str(Json.string(Json.get(j, "license")))
```

```bend
      # lim(n): at most 64 containers deep, n bytes of budget
      parsed(Json.parse(doc, Json.lim(U32.from_nat(By.len(doc)))))
```

`Json.get`, `path` and `at` answer `Maybe`; `key`, `index`, `nat` and
`string` take a `Maybe`, so they chain. A number keeps its exact text
(`Json.Num{"1e400"}`); `to_nat` and `to_f32` read it when you ask.

### Format a date

From `std/examples/date.bend` (seconds since 1970-01-01, UTC):

```bend
    IO.print(Time.iso(1727222400n))
    IO.print(Time.http(1727222400n))
    IO.print(Time.iso.ms(Nat.add(Nat.mul(1727222400n, 1000n), 123n)))
    IO.print(ymd(Time.date(19991n)))
    IO.print(secs(Time.from(2024n, 9n, 25n, 0n, 0n, 0n)))
    IO.print(secs(Time.iso.read("2024-02-29T12:00:00Z")))
```

prints `2024-09-25T00:00:00Z`, `Wed, 25 Sep 2024 00:00:00 GMT`,
`2024-09-25T00:00:00.123Z`, `2024/9/25`, `1727222400` and `1709208000`.
Released Bend has no wall clock (`IO.now` is monotonic), so the time to
format comes from your data.

### Gunzip a file

From `std/examples/gunzip.bend`:

```bend
# the output is capped (here at 1 MB): a gzip bomb is refused, not obeyed
def unzip(+gz: String) -> Result<&2, &2, Gzip.Err, String>:
  Gzip.gunzip(1048576n, gz)

def show(r: Result<&2, &2, Gzip.Err, String>) -> String:
  match r:
    case Done{+b}:
      Nat.show(By.len(b)) ++ " bytes:\n" ++ Text.decode(b)
    case Fail{e}:
      "not a gzip file, or a damaged one"
```

`Gzip.gzip(bytes, level)` writes a member, and `By.write_file` puts it on
disk (the example does both).

## One interface, two implementations

Our runtime packs a byte string a byte a cell and reads any offset in one
load; released Bend's `String` is a list, a cell a byte. So the code in
`std/` never touches bytes except through `std/bytes.bend`, which has two
implementations:

    bytes_list.bend    plain Bend over canon's Base: released Bend and ours
    bytes_packed.bend  this repo's Base natives (Bytes.get, find_byte, views)

Bend has no conditional compilation and an import names a file, so the
choice is **one line** in `std/bytes.bend`:

    import ./bytes_list.bend as Impl      # the default: runs everywhere
    import ./bytes_packed.bend as Impl    # this repo's runtime only: fast

Every other file imports `./bytes.bend` and nothing else of the two.
The interface is: `get`, `len`, `slice`, `cut`, `find`, `find_byte`,
`find_any`, `span`, `word_le`, `push`, `from_list`, `to_list`; a reader
(`Buf`, `open`, `at`, `take`, `size`) for scanners that read by offset (on
the list, a cursor that remembers where the last read landed, so a forward
scan pays a cell a byte); a writer (`Out`, `out.add`, `out.push`,
`out.done`, linear on both); and `read_chunk`, `read_file`, `write_file`
(`File.read_bytes` on released Bend, `File.read_buf` on ours).

## The laws

The proofs check against the interface, so they hold of whichever file the
switch names. Each prints exactly `All terms check.`:

    bend std/csv_proof.bend       # csv: fast path = byte machine, chunking, RFC 4180 spec, round trip
    bend std/reader.bend          # the reader kit's laws (feed_split, bad_feeds, reads_is, drain_reads)
    bend std/json_value.bend      # closed laws: round trip, canonical text, RFC 8259 refusals, limits
    bend std/time.bend            # calendar vectors: leap days, 2100, the last U32 second, iso.read
    bend std/text.bend            # UTF-8 round trip, encode's bytes, U+FFFD, split and replace
    bend std/bytes_packed.bend    # (ours only) Base's scans count what bytes_spec.bend says
    python3 tests/std/csv_mutants.py [--packed] [--bend canon/bend2/main.ts]   # 11 of 11 killed

The scans' specification is `bytes_spec.bend`; each implementation proves
its scans count what it says (`find_byte.is`, `find_any.is`), and the CSV
proof uses only those laws, `cut`, `to_list` and Base's `String`
definitions, never how bytes are stored.

## Speed

Measured on one Linux x86_64 box (4 cores), C lane, one run's median of
three, by `tests/std/bench/run.py` (answers checked against CPython first):

| | released Bend (canon 95317d95), list | this repo, list | this repo, packed |
|---|---|---|---|
| CSV, 10 MB | 7.3 MB/s | 10 MB/s | 24 MB/s |
| JSON, 26 MB (GitHub event archive) | 3.0 MB/s | 1.3 MB/s | 20 MB/s |
| gunzip, 30 KB out | 0.002 MB/s | | 2.6 MB/s (1 MB out) |

Released Bend's JS lane is slower still (CSV 0.34 MB/s). Gzip on released
Bend is correct but quadratic: inflate reads its window by offset, and a
list is walked to the offset, so keep it to files of tens of kilobytes
there. CSV and JSON scan forward and are linear on both.
