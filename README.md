# How fast can a deterministic RAM decide SAT?

<!-- STATUS-SUMMARY -->

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

Use Lean 4.19.0 with its bundled Std library and Python 3.11 or later. The finite permanent-grid and matching experiments use SymPy. The independent singleton optimization check uses NumPy and SciPy.

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
