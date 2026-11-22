# Phase 0: how a Bend program does input and output (harness spike)

All commands ran after `source .nix/env.sh` (bend 2.0.40, repo root). Scratch files lived in `$TMPDIR`;
only the programs in `bend/io/` are in the repo. Timings are `hyperfine --runs 3 -N` unless noted
(3 runs: read them as rough). Sources are copied from the guide ("IO and Concurrency", "Monads",
"Syntax Reference") and Base (`IO.args` base:220, `File.*` base:335-397, `U32.read` base:2467,
`String.split` base:2295, `List.foldl` base:1130).

Question: the conformance harness will run one seeded event sequence through the Go core `Step` and through the
Bend port, then compare final states. How do events get into the Bend program and the state out?

## 1. Summary

| Need | Works? | Where |
|---|---|---|
| Print a computed value | Yes, `IO.print` | `bend/io/print.bend` |
| Read argv | Yes, `IO.args()`; interpreted and compiled | `bend/io/args.bend`, `bend/io/record.bend` |
| Read stdin | **No Base stdin effect.** `File.open("/dev/stdin", "r")` + `File.read` works (Linux) | `bend/io/stdin.bend` |
| Print a structured state | Yes, one `key=value ...` line built with `++` and `U32.show` | `bend/io/record.bend` |
| Embed events in a generated `.bend` | Only in chunks: one list literal breaks between 2,500 and 3,000 elements; 10,000 in 500-element chunks works | section 6 |
| Call from JS (`-o x.mjs`) | Yes, non-IO defs; Node 24 and Bun 1.3 are on PATH (not in the Nix devShell) | section 7 |

## 2. print.bend

```python
import Base

# Computes a value purely, then prints it through the Base IO.print effect.
def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(U32.show((6 * 7 : U32)))
```
```
$ bend bend/io/print.bend
42
```

## 3. args.bend: IO.args, U32.read, fold, print

`bend/io/args.bend` (26 lines): `IO.args()` answers `List<String>` whose head is the program as invoked (guide, "IO and
Concurrency"), so `total` drops the head; `parse` is `Maybe.default(&2, U32, U32.read(s), 0)`; `sum` folds.

Interpreted:
```
$ bend bend/io/args.bend 1 2 3
6
$ bend bend/io/args.bend 4 x 5
9
```
Compiled (clang is on PATH through the wrapper):
```
$ bend bend/io/args.bend -o $TMPDIR/args && $TMPDIR/args 1 2 3
6
$ $TMPDIR/args
0
$ $TMPDIR/args 4 x 5
9
```
Both work. `-o args.js` also builds and runs: `node args.js 1 2 3` prints `6`, `bun args.js 1 2 3` prints `6`.
`-o args.mjs` builds (non-IO defs only, see section 7).

Authoring friction (the checker rejected these first, so the working forms are worth copying):

- `IO.args()` is `List<&1, String>` (affine). A helper declared `List<&2, String>` is refused
  (`expected : List<&2, String>  observed : List<&1, String>`). Declare helpers over `List<String>`.
- `match` inside a `do` block is refused (`expected : a term (a match heads a def body, not a term)`). Move it to a helper def.
- `(f, r) = v` inside a `do` block is refused (`expected : a do-block let with its type`). Destructure in a def body.
- A recursive def whose first argument is the accumulator is refused ("arguments are read left to right: each
  passed unchanged until one shrinks"). Put the shrinking list first, accumulator last.
- A `U32` used twice needs `+e`.
- Plain runs of these files print no proof banner; the output is just the program's output.

## 4. stdin: no dedicated effect, file read of /dev/stdin works

Search for a stdin effect:
```
$ grep -n -i -E 'stdin|read_line|Stdin|IO\.read|IO\.input|IO\.get_line' docs/bend-base.txt
359:def File.read_line(file: File, max: U32) ->
```
The only hit is `File.read_line`. Base has no `IO.stdin`, `IO.read` or `IO.input`. (`Process.run`'s `input` argument feeds a child's stdin; that is not ours.) The `File` doc comment for `read_line` says a pipe "answers each line as
it comes", so a descriptor-backed File can be a pipe. `File.open(path, mode)` takes a path, so I opened `/dev/stdin`
(Linux only; no `IO.stdin` handle exists).

`bend/io/stdin.bend` (37 lines): `File.open("/dev/stdin", "r")` via `IO.try`, `File.read(f, 16777216)` (up to 16 MiB, one
read until EOF), `IO.pass` to unwrap the `Result`, `File.close`, then `String.lines`, `String.split(l, ' ')`,
`U32.read` per word (non-numbers skipped), sum.
```
$ printf '1 2 3' | bend bend/io/stdin.bend
6
$ printf '10 20\n30\n\n5 x 7\n' | bend bend/io/stdin.bend
72
$ printf '' | bend bend/io/stdin.bend
0
$ bend bend/io/stdin.bend -o $TMPDIR/stdin && printf '1 2 3' | $TMPDIR/stdin
6
$ echo 4 5 | $TMPDIR/stdin
9
$ $TMPDIR/stdin < in.txt     # file redirect also works, interpreted and compiled
6
```
Caveat found at scale (section 5): the interpreted run overflows its stack on larger stdin; the compiled binary does not.

## 5. Structured output and scale of option A (argv and stdin)

`bend/io/record.bend` (40 lines) folds events from argv into a record `type State is Data: St{balance, ops, last}` with an
order-dependent step (`balance*31 + e`, wrapping U32) and prints one parseable line:
```
$ bend bend/io/record.bend 1 2 3
balance=1026 ops=3 last=3
$ bend bend/io/record.bend 3 2 1
balance=2946 ops=3 last=1
$ bend bend/io/record.bend
balance=0 ops=0 last=0
$ bend bend/io/record.bend -o $TMPDIR/record && $TMPDIR/record 1 2 3
balance=1026 ops=3 last=3
```
Independent check of the arithmetic (Python, mod 2^32): `[1,2,3]` gives 1026 and `[3,2,1]` gives 2946, so order matters and
wrapping matches uint32.

A Go harness can parse that line with `strings.Fields` + `strings.Cut(f, "=")` and `strconv.ParseUint`.

10,000 and 100,000 random U32 events (seed fixed, values up to 4294967295; generated in `$TMPDIR/ev10k.txt`, 107 KB, and
`ev100k.txt`, 1.07 MB). Expected values computed independently in Python and equal in every run below:
```
$ bend bend/io/record.bend $(cat ev10k.txt)         # interpreted, 10,000 argv
balance=2703090106 ops=10000 last=3342794914        # Python: same
$ ./rec.bin $(cat ev10k.txt)                         # compiled
balance=2703090106 ops=10000 last=3342794914
$ ./rec.bin $(cat ev100k.txt)                        # compiled, 100,000 argv (1.07 MB; ARG_MAX is 2097152)
balance=242041390 ops=100000 last=148273166          # Python: same
$ bend bend/io/record.bend $(cat ev100k.txt)         # interpreted, 100,000 argv
balance=242041390 ops=100000 last=148273166
$ ./stdin.bin < ev10k.txt                            # sum, compiled stdin
3807239814                                           # Python: same
$ ./stdin.bin < ev100k.txt
2157487122                                           # Python: same
$ bend bend/io/stdin.bend < ev10k.txt                # sum, interpreted stdin
bend: memory fault (machine stack overflow?)
```

| Run | Mean | Range |
|---|---|---|
| `bend record.bend <10k args>` (interpreted) | 521.9 ms +/- 35.4 | 481.3 to 546.8 |
| `./rec.bin <10k args>` (compiled) | 4.9 ms +/- 0.1 | 4.8 to 5.0 |
| `./stdin.bin < ev10k.txt` (compiled) | 7.2 ms +/- 0.5 | 6.9 to 7.8 |
| `./stdin.bin < ev100k.txt` (compiled) | 63.2 ms +/- 0.9 | 62.5 to 64.2 |
| `bend record.bend -o rec2.bin` (compile) | 1.499 s +/- 0.085 | 1.444 to 1.597 |
| `bend stdin.bend < ev_1000.txt` (interpreted, 1,000 numbers) | 473.5 ms +/- 27.9 | 453.8 to 505.4 |

Interpreted stdin (`bend bend/io/stdin.bend < file`): the limit is in **bytes of input, roughly 20 KB**, not in the number
of events. It is soft near the edge. Measured with `seq 1 N | tr '\n' ' '` (short numbers) and with the random 10-digit
events (each size tried 6 times, `ok`/`FAIL` = prints a result / prints the memory fault):
```
seq N=3000  ( 13,893 B): 4501500
seq N=3500  ( 16,393 B): 6126750
seq N=4000  ( 18,893 B): 8002000          x6: ok ok ok ok ok ok
rand       ( 19,794 B): 391719210
rand 2000  ( 21,999 B): FAIL ok FAIL FAIL FAIL FAIL   (also 585484476 in 2 of 3 earlier runs: flaky)
seq N=5000  ( 23,893 B): FAIL x6 (bend: memory fault (machine stack overflow?))
seq N=6000  ( 28,893 B): FAIL x6
seq N=8000  ( 38,893 B): FAIL
random 10,000 (107,403 B): bend: memory fault (machine stack overflow?)
```
So up to about 19 KB passes always, 22 KB is a coin flip, 24 KB and above always fails. 4,000 short numbers pass; 2,000
ten-digit numbers fail. Cause not isolated (suspect the non-tail `String.split` over one big string in the interpreted lane);
the compiled binary on the same program is fine to 100,000 ten-digit numbers (1.07 MB). Interpreted argv did not hit the limit
at 100,000.

Compiled stdin through a pipe (what Go's `exec.Cmd` gives), 100,000 events, same result as the redirect and the Python reference:
```
$ cat ev100k.txt | ./stdin.bin
2157487122
$ hyperfine --runs 3 'cat ev100k.txt | ./stdin.bin'
  Time (mean ± σ):      64.8 ms ±   2.0 ms    [User: 39.6 ms, System: 26.1 ms]
  Range (min … max):    63.2 ms …  67.0 ms    3 runs
```
Compiled argv, 100,000 events (1,074,154 bytes of arguments, about half of the 2,097,152-byte `ARG_MAX`; timing includes the
shell and `cat` that build the command line; plain `-N` hyperfine with a 100k-word command line reported 1.4 ms, which I did not
trust, so I used the shell form):
```
$ hyperfine --runs 3 './rec.bin $(cat ev100k.txt) > /dev/null'
  Time (mean ± σ):     226.4 ms ±  29.5 ms    [User: 111.1 ms, System: 49.9 ms]
  Range (min … max):   193.7 ms …  251.0 ms    3 runs
```
So at 100,000 events argv is about 3.5 times slower than stdin (226 vs 63 ms); at 10,000 both take 5 to 7 ms.

## 6. Option B probe: events embedded as a list literal in a generated .bend

Generator (shell loop; kept in `$TMPDIR/genlist.sh`, not in the repo). Core line:
`printf '  ['; seq -s, 1 $N | sed 's/,/, /g' | tr -d '\n'; echo ']'` inside `def events() -> List<&2, U32>:`, with
`main` printing `U32.show(sum(events(), 0))` (tail-recursive `sum`).

One literal, `bend big_N.bend` (wall time from `time`):

| Elements | Result | Wall |
|---|---|---|
| 100 | 5050 | 0.417 s |
| 500 | 125250 | 0.489 s |
| 1,000 | 500500 | 0.607 s |
| 2,000 | 2001000 | 0.739 s (hyperfine: 800.3 ms +/- 17.9) |
| 2,500 | ran ok 4 of 4 times | n/a |
| 3,000 | `bend: memory fault (machine stack overflow?)` (FAIL 4 of 4 times) | 2.3 s |
| 4,000 | `bend: memory fault (machine stack overflow?)` | 3.1 s |
| 5,000 | `Error: the machine stack overflowed (a deep recursion, or a literal too large to expand)` | 1.9 s |
| 10,000 (59 KB file) | same error, `SOME PROOFS FAIL`; `-o big10k` fails the same way | 0.26 s |
| `ulimit -s unlimited`, 10,000 | same error | n/a |

So a single list literal does **not** scale to 10,000 events. A string literal holding the events ("1 2 3 ...", split and
`U32.read` at runtime) also fails: 6,000 numbers work, 8,000 give `memory fault`, 10,000 give `memory fault`.

Workaround that works: split the events over several `def cK() -> List<&2, U32>:` literals of 500 elements each and combine
with `List.append(&2, U32, c0(), List.append(&2, U32, c1(), ...))` (`$TMPDIR/genchunk.sh`):
```
$ bend chunk_10000.bend          # 20 chunks of 500
50005000
$ bend chunk_50000.bend          # 100 chunks
1250025000
```
(Both sums are correct.) Timings:

| Run | Mean | Range |
|---|---|---|
| `bend chunk_10000.bend` (run) | 1.324 s +/- 0.011 | 1.313 to 1.335 |
| `bend chunk_50000.bend` (run) | 3.930 s +/- 0.276 | 3.728 to 4.244 |
| `bend chunk_10000.bend -o chunk10k.bin` (compile, 210 KB binary) | 3.719 s +/- 0.446 | 3.389 to 4.227 |
| `./chunk10k.bin` (run) | 1.6 ms +/- 0.5 | 1.3 to 2.2 |

(Re-run 4 times each: 2,000 and 2,500 pass every time, 3,000 fails every time.)

Embedding is feasible only with chunking and costs about 1.3 s of check/compile per 10,000-event sequence (3.7 s to also get
a binary). A fresh program per seeded sequence therefore costs seconds each, versus about 5 to 7 ms per run for option A.
Embedding also puts the events inside the program under test, so the program differs per run.

## 7. Option C probe: `-o x.mjs`, called from JS

```
$ bend bend/io/record.bend -o $TMPDIR/rec.mjs
$ sed -n '/export default/,$p' $TMPDIR/rec.mjs
export default {
  "step": run_lib((a0,a1) => run_loop($step(a0,a1)), 2),
  "parse": ...,  "run": ...,  "show": ...,  "final": ...,
};
```
Only non-IO defs are exported (`main` is not). `step` takes constructors as `{$: "St", balance, ops, last}` and U32 as a
number, as the guide says. `callmjs.mjs`:
```js
import R from "./rec.mjs";
let s = {$: "St", balance: 0, ops: 0, last: 0};
for (const e of [1, 2, 3]) s = R.step(s, e);
console.log(JSON.stringify(s), R.show(s));
```
```
$ node callmjs.mjs
{"$":"St","balance":1026,"ops":3,"last":3} balance=1026 ops=3 last=3
$ bun callmjs.mjs
{"$":"St","balance":1026,"ops":3,"last":3} balance=1026 ops=3 last=3
$ time node callbig.mjs ev10k.txt        # step per event from JS
balance=2703090106 ops=10000 last=3342794914     (real 0.083 s)
$ time node callbig.mjs ev100k.txt
balance=242041390 ops=100000 last=148273166      (real 0.227 s)
```
Results equal the Python reference. Node v24.22.1 and Bun 1.3.13 are on PATH from `/etc/profiles/per-user/claude/bin`,
**not** from the pinned Nix devShell, so a Go test depending on them is unpinned. It also needs the Go test to shell out to
a JS driver and to marshal Bend constructors by hand ({$: "Name", ...}).

Not verified: that the JS arithmetic for `U32.mul` is exact for every operand pair (the generated code matched Python at
100,000 events, with `b*31`). A real port should re-check wrapping multiplication against Go `uint32`.

## 8. Recommendation for the harness

**Option A: compile the Bend port once to a native binary and feed events on stdin; read one `key=value ...` line from stdout.**

Reasons:
1. Measured: 5 to 7 ms per sequence at 10,000 events (63 ms at 100,000), versus about 1.3 s (B) and 0.5 s (interpreted A).
   The one-off compile costs about 1.5 s.
2. It tests the same program on every sequence; B tests a different generated program each time, and a single literal breaks
   between 2,500 and 3,000 elements.
3. Stdin has no limit below 16 MiB (`File.read(f, 16777216)` in `stdin.bend`; raise the read size if needed). Argv is capped by
   `ARG_MAX` (2,097,152 bytes here); 100,000 ten-digit events are 1.07 MB, about half of it, and ran in 226 ms against 63 ms
   for stdin. Argv works and needs no `/dev/stdin`; use it for short sequences. The scale runs above used `<` redirects;
   a pipe (`cat file | ./stdin.bin`, what `exec.Cmd` provides) gives the same result and time at 100,000 events.
4. Fully pinned toolchain (bend plus its clang wrapper); C needs an unpinned Node/Bun and hand-marshalled constructors.
5. Go side is `exec.Cmd` with `Stdin` set and a `strings.Fields` parse of the output line.

Things the harness author must know:
- Always run the compiled binary, never `bend x.bend < in` for stdin: the interpreted run overflows its stack above roughly
  20 KB of input (section 5).
- `U32` wraps; model events and state in values that fit `U32`, or encode wider values as several words, and compare with
  Go `uint32`.
- Keep the recursion in the port tail-shaped over the event list (list first, accumulator last) so the termination checker
  accepts the fold.
- IO programs (`main` returning `IO`) are not proofs: the proof gate covers the pure `step`; `IO.print`, `IO.args` and `File.*`
  are Base foreign effects, exempt per the phase 0 guide report (hatch 12). No foreign `.c`/`.js` files of ours were added.

## 9. Harness requirements (from observed risks)

All outputs below are from the spike binaries (`args` = `bend/io/args.bend`, `stdin.bin` = `bend/io/stdin.bend`, both compiled).

(a) **Bad numbers must fail loudly; the spikes hide them.** `U32.read` returns `None` on a non-digit or overflow, and the spikes
turn that into 0 or skip it. Also the sum wraps. The real Bend port must treat `None` as an error (print `error=...` and exit
nonzero) and the Go test must check the exit code.
```
$ ./args 4294967295 1      # 4294967295 + 1 wraps to 0
0
$ ./args 4294967296 1      # 4294967296 overflows U32.read: token silently dropped, only the 1 counted
1
$ ./args abc 1             # non-number silently dropped
1
```
(b) **Only a single space and `\n` separate events.** Tabs and CRLF are not separators, so the token fails `U32.read` and is
dropped. The Go writer must emit ASCII digits separated by single spaces, with a final newline.
```
$ printf '1\t2\r\n3\r\n' | ./stdin.bin
0
$ printf '1 2\n3\n' | ./stdin.bin
6
```
(c) **A closed stdin hangs; an open pipe that is never closed hangs.** Go must always attach a pipe, write, close it, and run
under a timeout. (`timeout 5` killed the hung runs, exit 124.)
```
$ timeout 5 ./stdin.bin <&-
(no output)      rc=124
$ (sleep 8 | timeout 3 ./stdin.bin)       # pipe left open
(no output)      rc=124
$ timeout 5 ./stdin.bin < /dev/null       # empty input is fine
0                rc=0
```
(d) **`/dev/stdin` is Linux-only** (no Base stdin effect; `File.open("/dev/stdin", "r")`). Fine for this VPS.

(e) **Compiler source.** `bend ... -o` needs clang although `clang` is not on the `env.sh` PATH. It comes from the `bend` wrapper
script, which prepends a Nix clang-wrapper to `PATH` before exec'ing the real binary:
```
$ cat $(command -v bend)
#! /nix/store/8favl12dxjfxwzgqq5jh53k2kjn19nn9-bash-5.3p9/bin/bash -e
PATH=${PATH:+':'$PATH':'}
PATH=${PATH/':''/nix/store/ddqfr1sm2fgnxim39a3fcjray13x8vw1-clang-wrapper-21.1.8/bin'':'/':'}
PATH='/nix/store/ddqfr1sm2fgnxim39a3fcjray13x8vw1-clang-wrapper-21.1.8/bin'$PATH
...
exec "/nix/store/9xnqfsjii1ix743x7wfqfjxj3h2l3bdw-bend-2.0.40/libexec/bend/bin/bend"  "$@"
```
So clang 21.1.8 is pinned through the bend package. Run the compiled binary and `bend -o` through that wrapper (do not call the
inner `libexec` binary directly).

## 10. Log entry (handover section 8 fields)

- Date/time: 2026-11-22, about 01:56 to 02:01 UTC.
- Tool: Bend 2 (2.0.40).
- Use case: Phase 0 I/O spike (conformance-harness input and output).
- What was done: wrote `print.bend`, `args.bend`, `stdin.bend`, `record.bend`; ran each interpreted and compiled; grepped Base
  for stdin and found none; probed embedding (single literal, string literal, chunked list), argv at 10,000 and 100,000, stdin at
  10,000 and 100,000, and an `.mjs` build called from Node and Bun; checked against Python-computed references.
- Authoring time (honest estimate): about 25 minutes for the programs, about 25 more for the probes and write-up.
- AI iterations (estimate): about 12 edit/run cycles: `args.bend` 3 (affine list quantity, `match` in `do`), `stdin.bend` 2
  (`(a, b) = v` in `do`), `record.bend` 3 (`+e`, termination order), plus 4 generator/shell fixes (shell function not persisting,
  `#!/bin/bash` missing in the sandbox).
- Machine time: see the tables. Compile of a small program 1.5 s; run of a compiled program 5 to 7 ms at 10,000 events;
  interpreted run about 0.5 s. No separate cold run measured.
- Result: option A (compiled, stdin) works and scales to 100,000 events; option B works only in chunks and is slow; option C works
  but is unpinned; interpreted stdin overflows above roughly 20 KB of input; no Base stdin effect.
- Size: `print.bend` 6 lines, `args.bend` 26, `stdin.bend` 37, `record.bend` 40, plus this file.
- Friction: no stdin effect; affine `List<String>` from `IO.args`; `match` and destructuring not allowed inside `do`; termination
  checker order; single-literal limit between 2,500 and 3,000 elements with unhelpful "memory fault" and "stack overflowed" errors;
  stdin overflow in the interpreted run.
