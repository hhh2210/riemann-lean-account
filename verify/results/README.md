# Results

Output of the scripts in `verify/`, as produced. Times are Unix seconds.

| File | Produced by | What it is |
|---|---|---|
| `build-summary.txt` | `build.sh` | first and last lines of the build log, the count of compiled modules, the toolchain and the pinned revisions |
| `check.txt` | `check.sh` | where `RiemannHypothesis` and `riemannZeta` are declared, the statement, and the axioms of the five theorems |
| `axioms.txt` | the first axiom check, made when the build ended | the same axioms, from the first run |
| `corollaries.txt` | `lean/Corollaries.lean` compiled against the built archive | the axioms of the three corollaries |
| `targets.txt` | `lean/Targets.lean` compiled against the built archive | it compiles, with no output |
| `cut-result.txt` | `cut.sh` | the size of the cone of `riemannHypothesis`, counts by kind and by top-level directory, the probes by name |
| `cut-hub.txt` | `cut.sh` | every theorem of the file that collects the published results, with whether it is in the cone |
| `cut-in.txt.xz`, `cut-out.txt.xz` | `cut.sh` | every declaration of the archive inside and outside the cone, one per line: kind (`T` theorem, `D` definition, `I` inductive type, `C` constructor, `R` recursor, `O` opaque) and full name |
| `cut-modules.txt.xz` | `cut.sh` | every module of the archive with its declarations inside and outside the cone |
| `cut-five-extra.txt` | `cut.sh` | the 24 declarations in the cone of all five theorems that are not in the cone of `riemannHypothesis` |
| `replay-summary.txt` | `replay.sh` | the counts of the kernel replay |
| `replay-log.txt` | `replay.sh` | its progress log |
| `replay-failures.txt` | `replay.sh` | declarations the kernel rejected: empty |
| `replay-axioms.txt` | `replay.sh` | every axiom declared anywhere in the import closure of `Main` |
| `replay-skipped.txt` | `replay.sh` | the declarations marked unsafe or partial, which a replay does not check |

Two remarks on the raw files. The label `CONE-SIZE-FIVE-THEOREMS` in `cut-result.txt` is the
cone of all five theorems of `Main.lean`; `CONE-SIZE` is that of `riemannHypothesis` alone, and
all other figures in that file refer to it. The last line of `replay-log.txt`, `oom_kill 2`, is
the container's cumulative count of processes killed for memory; both were attempts with the
toolchain's own checker, made before this run (the paper, Section 2.7).
