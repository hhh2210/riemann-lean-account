# Lean files

Two short files that build on the archive's top theorems.

- `Corollaries.lean` proves three immediate corollaries from the archive's `Main` and Mathlib
  alone, and prints their axioms. It needs a built copy of the archive: from the archive's root,
  `lake env lean /path/to/Corollaries.lean`. Our output is in
  `../verify/results/corollaries.txt`: each depends on `propext`, `Classical.choice` and
  `Quot.sound` only.
- `Targets.lean` states, and does not prove, consequences of GRH for Dirichlet L-functions that
  are worth formalising next. It needs Mathlib only. Each `def` is a proposition that Lean
  checks for being well formed; the constants are those of the cited papers and must be checked
  against the papers before a formalisation relies on them.

See `../ROADMAP.md`.
