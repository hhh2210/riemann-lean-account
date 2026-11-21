# Results

Output of our own run of the programs in `verify/`. Times are Unix seconds.

| File | Produced by | What it is |
|---|---|---|
| `scan.txt` | `scan.py` on the downloaded `lean.tar.gz` | size and SHA-256 of the archive, counts of files and lines, the static inspection |
| `build-summary.txt` | assembled by hand after `build.sh` ended | the first and last lines of the build log (`START` to `END`); then a count of compiled files under `.lake/build`, a count of failure marks and of warnings in the log, the toolchain file, `lean --version`, the revisions in `lake-manifest.json`, the number of processors and the processor model |
| `check.txt` | `check.sh` | where `RiemannHypothesis` and `riemannZeta` are declared, the statement, and the axioms of the five theorems |
| `axioms.txt` | the first axiom check, made when the build ended | the same axioms, from the first run |
| `corollaries.txt` | `lean/Corollaries.lean` compiled against the built archive | the axioms of the three corollaries |
| `targets.txt` | `lean/Targets.lean` compiled against the built archive | it compiles, with no output |
| `cut-result.txt` | `cut.sh` | the size of the cone of `riemannHypothesis` and of the cone of all five theorems, counts by kind and by the top-level directory of the declaring module, the probes by name |
| `cut-hub.txt` | `cut.sh` | every theorem of the file that collects the published results, with whether it is in the cone |
| `cut-in.txt.xz`, `cut-out.txt.xz` | `cut.sh` | every declaration of the archive inside and outside the cone of `riemannHypothesis`, one per line: kind (`T` theorem, `D` definition, `I` inductive type, `C` constructor, `R` recursor, `O` opaque) and full name. Declarations of Mathlib and of Lean's library are not listed |
| `cut-modules.txt.xz` | `cut.sh` | the names of the 147,489 modules of the archive that declare at least one declaration of the cone |
| `cut-five-extra.txt` | `cut.sh` | the 24 declarations in the cone of all five theorems that are not in the cone of `riemannHypothesis` |
| `replay-summary.txt` | `replay/ReplayMain.lean` | the counts of the kernel replay |
| `replay-log.txt` | the wrapper described below | the program's progress log |
| `replay-failures.txt` | `replay/ReplayMain.lean` | declarations the kernel rejected: empty |
| `replay-axioms.txt` | `replay/ReplayMain.lean` | every axiom declared anywhere in the import closure of `Main` |
| `replay-skipped.txt` | `replay/ReplayMain.lean` | the 5,840 declarations marked unsafe or partial, which a replay does not check |

## How to read the counts

**Names and declarations.** `cut-in.txt.xz` and `cut-out.txt.xz` have one line for each
declaration in each module that declares it. Lean lets an auxiliary theorem be declared again in
every module that needs it, so a name can occur on several lines: the two lists have 1,283,850
and 661,669 lines and 1,265,256 and 640,666 distinct names. All repeats are theorems: 1,093,609
lines and 1,075,015 names inside the cone, 494,644 lines and 473,641 names outside. The paper
counts names. The `BY-ROOT` table of `cut-result.txt` counts lines, which is why its in-cone
column adds up to more than `CONE-SIZE`, which counts names.

**Modules.** The archive has 175,187 Lean files; 175,014 of them declare something and 147,489
declare something in the cone.

**The replay.** The import closure of `Main` has 2,701,132 declarations. 5,840 are unsafe or
partial and are not replayed; the other 2,695,292 were. The categories of `replay-summary.txt`
add up to four fewer than that: the four constants of the quotient type (`Quot`, `Quot.mk`,
`Quot.lift`, `Quot.ind`) are added in one step and counted in no category.

## What is not in a file

- `replay-log.txt` was written by a wrapper that ran the compiled replay program exactly as
  `replay.sh` does, with `LEAN_NUM_THREADS=28`, printing `PAR-START` before it and `PAR-EXIT`
  with the exit code after it, and then the container's cumulative count of processes killed
  for memory (`oom_kill 2`). That counter already read 2 when it was read 28 minutes into the
  run, and the run exited 0, so neither kill was of this run.
- The failed attempt with the toolchain's `leanchecker` (2,012 modules on 20 threads, killed at
  the container's 128 GB limit with exit code 137) left no output that we kept.
- The label `CONE-SIZE-FIVE-THEOREMS` in `cut-result.txt` is the cone of all five theorems of
  `Main.lean`; `CONE-SIZE` is that of `riemannHypothesis` alone, and every other figure in that
  file refers to the latter.
