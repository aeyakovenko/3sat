# How fast can a deterministic RAM decide SAT?

## Status (28 November 2026)

**The question is open.** Nothing in this repository proves that explicit SAT needs more than linear time on a logarithmic-word RAM with unrestricted workspace, and nothing here proves the quadratic or cubic exclusions either. Every lower bound recorded below is for a different model, is conditional, is finite, or is of the same order as one packed scan of the input. The test for what counts as progress is fixed in [research-steering.md](research-steering.md#what-counts-as-progress-on-the-lower-bound).

### What is established, and its scope

| Result | Scope | Note |
| --- | --- | --- |
| Every bounded-fan-in Boolean circuit for 3-SAT has $\Omega(n(\log n)^\sigma)$ gates for some $\sigma>0$. | Circuit size, not RAM time. Rests on the list-distinctness theorem of the 24 November 2026 OpenAI preprint. A RAM decides the same hard files in $\Theta(n/\log n)$ steps. | [Proof and encoding](notes/checking-the-sat-circuit-bound.md) · [RAM clock on those files](notes/scan-time-on-the-dense-list-projection.md) |
| Proper ASCII 3-SAT needs $\Omega(N^3/(\log^2N\log\log N))$ De Morgan formula leaves and $\Omega(N^2/\log^2N)$ branching-program nodes. | Formula and branching-program size. The formula bound was already recorded by Williams. | [Bounds and credits](notes/formula-and-branching-program-size-of-sat.md) |
| Weak ETH implies $\Omega(n\sqrt{\log n})$ multitape time for 2-SAT. If some characteristic lacks ports, nondeterministic linear tape time is not closed under complement. | Multitape Turing machines, conditional. | [2-SAT on tapes](notes/checking-a-word-transpose-with-two-clauses-per-cell.md) · [Complement](notes/tape-time-under-complement.md) |
| SAT is not in time $O(n^{1.082})$ on a machine with one unlimited planar tape and $T^{1/4+o(1)}$ random-access scratch words. | Restricted memory geometry. | [Mixed-tape schedule](notes/mixed-tape-williams-schedule.md) |
| Linear time together with $O(n/\log^{6.155}n)$ auxiliary bits is impossible. | Time–space band. A linear-time RAM may use $\Theta(n\log n)$ bits, so this leaves the unrestricted case untouched. | [Band](notes/sat-time-space-band.md) · [Mixed profiles](notes/mixed-checkpoint-profiles.md) |
| A linear-time solver would have to retrieve nonzero data from more than $Cn/\log^{11}n$ distinct work addresses on files of each verdict. | A property of every hypothetical linear-time solver. A linear-time computation can have this property. | [Theorem](notes/fast-sat-must-retrieve-nonzero-work-words.md) |
| On one positive DIMACS file per length, every program executes at least $(2-O(1/\log w))N/w$ instructions, and every fixed program at least $(5/2-o(1))N/w$ on a second family. | Constant factors above one load per word. Programs taking $2N/w+O(1)$ and $(3+o(1))N/w$ exist on the same files. | [Two per word](notes/two-instructions-per-homogeneous-dimacs-word.md) · [Five halves](notes/generating-fresh-addresses-on-one-native-sat-file.md) |
| The exact worst-case clock of the 16-bit sign-plane SAT catalog on the four-bit RAM is nine executed instructions. It is still exactly nine at 20 bits and in one 21-bit variant; the other 21-bit variant has upper bound nine. | Finite. No growth at the first extension. | [Exact nine](notes/exact-nine-step-clock-for-four-sat-words.md) · [Twenty bits](notes/nine-steps-at-twenty-tightly-packed-selector-bits.md) · [Fifth word](notes/the-first-fifth-word-does-not-increase-the-nine-step-upper-bound.md) |
| Cube-cycle clause banks: at most five omitted labels per bank is linear-time; one fixed six-omission pattern encodes arbitrary 3-SAT. | A sharp tractability threshold, not a time lower bound. | [Threshold](notes/shuffled-four-cube-cycle-banks-in-ordinary-sat.md) |

### The finite-exhaustion approach and its ceiling

The working approach since 25 November has been to exhaust the smallest RAM on small SAT catalogs, find the exact clock, and look for a transformation to the next size under which the deficit survives. Its measured outcome:

- The complete cyclic selector catalogs at two through six input bits have exact clocks **3, 4, 4, 6, 6**. On the sixteen four-bit inputs, an injective quadratic map into five bits preserves every verdict and raises the optimal clock from **four to six**. A second quadratic map retains six on the same sixteen ancestors. Every affine map preserving the full predicate at either extension admits five steps on the corresponding inherited suite. From source length five onward, every affine extension of this selector is an XOR insertion up to cycle symmetry. [All-length classification](notes/affine-successors-of-cycle-cover-selectors.md) From the full six-bit catalog, four XOR gaps give exact clock seven and two preserve six. The complete seven-bit clock is in $[7,8]$. [Exact clocks and algebraic maps](notes/a-strict-clock-increase-under-one-bit-cycle-subdivision.md)
- The sign-plane catalog has exact clock nine at its first extension.
- On the 16-bit cube-cycle catalog, every correct native RAM program needs at least nine executed instructions on a satisfiable mask and on an unsatisfiable mask in the same 89-mask suite. Fourteen steps suffice on the entire catalog. The lower bound survives six one-bit extensions, including 24→25 at ten steps and 59→60 at fifteen. At all six adjacent pairs a hard suite transfers unchanged in memory. Inserting the XOR of neighboring bits preserves SAT at every length. A uniform program decides this particular selector predicate in a constant number of steps per packed word. [Nine-step obstruction and one-bit extensions](notes/a-shared-nine-step-obstruction-and-the-next-native-width.md)
- With unbounded code, **every** predicate on $N$ bits is decided in at most $N+\lceil N/w\rceil$ executed instructions: one load per word and one comparison per bit. So the finite census with unbounded code measures a quantity that is $O(N)$ for every language. It can at best separate a packed scan ($N/w$) from a bit scan ($N$); it cannot show superlinear time. The measured SAT clock of nine at 16 input bits is below the clock of a typical 16-bit predicate, which is at least twelve. [Asymptotic form, 25 November](notes/worst-labelling-clock-with-unbounded-program-text.md) · [Explicit bounds at the census sizes](notes/the-ceiling-of-the-unbounded-code-clock.md)
- Concatenating independent sign-plane records does not add their clocks once a word holds several records. [Packed records](notes/which-four-word-sat-targets-finish-in-seven-steps.md)
- A superlinear bound therefore has to limit the program text: one finite program at every length, or a budget on its size. Exhaustion over program size is complete only through five stored instructions, where no program decides DIMACS SAT at any speed; every correct solver is larger. [Five instructions](notes/five-instructions-cannot-decide-dimacs-sat.md)

The steering file names the open step: to force processing beyond a scan of the packed words on a run of an arbitrary correct solver. For the per-word execution bounds and the exact clocks above, programs that meet the bound on the same files, exactly or up to a constant factor, are recorded next to them.

### What would suffice

- A speedup of deterministic RAM time by a constant number of alternations that remains valid when one memory snapshot is as long as the run, about $n\log n$ bits. [Where the hierarchy proof stops](research-steering.md#where-the-hierarchy-proof-stops)
- Or a locally bit-indexed reduction of unary-clock nondeterministic RAM acceptance to $o(t\log t)$ bits of DIMACS. [Compiler criterion](notes/compact-compilers-and-linear-sat-time.md)
- An argument that also holds relative to the oracle of [relativized-clock.md](notes/relativized-clock.md) cannot work, since linear-time SAT holds there.
- Every recorded barrier, stated with its exact hypotheses, and the two combinations of techniques that pass all of them on paper: [What any proof must get past](notes/what-any-proof-of-superlinear-sat-time-must-get-past.md)

## Layout

Start with [RESULTS.md](RESULTS.md), the index of results. [JOURNAL.md](JOURNAL.md) has the earlier research and conditional tests, the research journal, the literature checks and a list of the notes that no other file links to. [research-steering.md](research-steering.md) is the steering log of the project.

| Path | Files | Contents |
| --- | ---: | --- |
| [notes/](notes) | 990 | One Markdown note per result or attempt. Notes link to each other and to the files that check them. |
| [lean/](lean) | 692 | Lean 4 files, each run on its own as `lean File.lean`. |
| [audits/](audits) | 733 | 697 Python audits and experiments, 26 C++ programs with 3 headers, 1 shell replay script, 4 gzip-compressed JSON data files and 2 patch files. They share one directory because they import, include and open one another by bare file name. |
| [upstream-checks/](upstream-checks) | 13 | Lean files that import Mathlib, which the pinned toolchain alone does not provide. |
| [tools/](tools) | 3 | [check.py](tools/check.py), its baseline [known-failures.json](tools/known-failures.json), and [migrate_layout.py](tools/migrate_layout.py), which produced this layout from the earlier flat one. |

`lean-toolchain` and `.gitignore` stay at the root. The file counts are those of the commit that introduced this layout.

`python3 tools/migrate_layout.py` is idempotent. Run it again when a file lands at the root or when a branch made before the move is merged: it moves the new files, rewrites flat-layout links, and regenerates the list of unlinked notes in `JOURNAL.md`.

## Checking

Run the checker from the repository root:

```sh
python3 tools/check.py
```

It checks three things and prints a short summary.

1. Layout. No tracked file at the root belongs in `notes/`, `lean/` or `audits/`.
2. Links. Every relative link in every tracked Markdown file resolves to a tracked file or directory, and every `#anchor` on a Markdown target is a heading of that file.
3. Run. Every tracked Lean file is run as `lean File.lean` and every Python file in `audits/` as `python3 -B file.py`, each from its own directory, in parallel and under a time limit.

The results are compared with [tools/known-failures.json](tools/known-failures.json). The exit status is 0 when nothing regressed. It is 1 when a file that is not listed there fails, when a listed file fails without the output recorded for its category, when a link that is not listed there is broken, or when the layout check fails. Listed failures that now pass are reported and do not change the exit status.

| Option | Effect |
| --- | --- |
| `--skip-run` | Check the layout and the links only. This takes about a second. |
| `--only-links` | Check the links only. |
| `--jobs N` | Run `N` files at once. The default is 20, or the number of processors if that is smaller. |
| `--lean PATH` | Use this Lean binary. The default is `$LEAN`, then the elan toolchain named in `lean-toolchain`, then `lean` on `PATH`. |
| `--lean-timeout S`, `--py-timeout S` | Time limit for one file in seconds. The default is 300. |
| `FILE ...` | Run only the named Lean or Python files, for example `python3 tools/check.py lean/Adaptive.lean`. |

### Tool versions

Use Lean 4.19.0 with its bundled Std library and Python 3.10 or later. The finite permanent-grid and matching experiments use SymPy. The independent singleton optimization check uses NumPy and SciPy.

The baseline in `tools/known-failures.json` was recorded on 2026-11-27 with Lean 4.19.0, Python 3.10.12, NumPy 1.21.5, SciPy 1.8.0, SymPy 1.12 and g++ 11.4.0 installed as `c++`, which five audits use to compile C++20 sources.

The Lean files state the parts checked by the kernel. The asymptotic constructions, reductions, and complexity estimates are manuscript arguments.

### Known failures

Of the 1402 files that are run, 1310 pass and 92 fail for a recorded reason.

| Category | Files | Reason |
| --- | ---: | --- |
| `lean-mathlib` | 33 | Imports Mathlib, directly or through another file of `lean/`. This covers all 13 files of `upstream-checks/`, one of which also imports `OAI`. Running `lean File.lean` with the pinned toolchain provides neither library. |
| `lean-sibling-import` | 3 | Imports another file of `lean/` that needs only the bundled libraries. Running `lean File.lean` does not compile imports. |
| `python-pycosat` | 45 | Imports the `pycosat` package, which was not installed when the baseline was recorded. |
| `python-usage` | 11 | Exits with a usage error when run without arguments. These scripts need a solver path, a compiled binary, a state or output directory, an instance or a mode option. |

To record another known failure, add a line `"path": "category"` to the `failures` object of that file.

A file of the category `lean-sibling-import` checks once its import is compiled, for example from `lean/`:

```sh
lean -o /tmp/NestedClauseCycle.olean NestedClauseCycle.lean
LEAN_PATH=/tmp lean EightTerminalCycle.lean
```

The same baseline lists 6 relative link targets that do not resolve.

| Reason | Links |
| --- | ---: |
| Mathematical notation in which a parenthesis follows a closing bracket; not a link. | 5 |
| Link to a note that is not committed. | 1 |

### Commands quoted in notes

Notes quote commands with bare file names, such as `python3 some_audit.py` or `lean SomeFile.lean`. Run Python, C++ and shell commands from `audits/` and Lean commands from `lean/`.
