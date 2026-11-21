# The argument of Alpöge's formal proof of the Riemann Hypothesis

On 20 November 2026 Levent Alpöge released a Lean 4 formalisation, 17 million lines long, of a
proof of the Riemann Hypothesis and of its analogue for every Dirichlet L-function. His note
says that no human-readable proof has been written.

This repository contains two things:

1. **A verification.** We built the archive, checked which axioms the theorems depend on,
   replayed its declarations through the Lean kernel from an empty environment, and computed
   which declarations the final theorem actually uses.
2. **An account of the argument**, read from the Lean source: the paper
   [`paper/main.pdf`](paper/main.pdf).

The archive itself is not redistributed here. Its author serves it in fourteen parts,
`https://alpo.ge/lean.tar.gz.part01` to `part14`; `verify/setup.sh` fetches them and checks the
hash.

## What the machine says

| Check | Result |
|---|---|
| Archive | `lean.tar.gz`, 239,275,554 bytes, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`; 175,187 Lean files, 17,374,215 lines |
| Toolchain | Lean 4.33.1; Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474` |
| Build | `lake build Main` exits 0: `Build completed successfully (183893 jobs)`; all 175,187 modules built; 13.4 hours on 32 cores |
| Statement | `riemannHypothesis : RiemannHypothesis`, where `RiemannHypothesis` and `riemannZeta` are Mathlib's own (declared in `Mathlib.NumberTheory.LSeries.RiemannZeta`) |
| Axioms | each of the five top theorems depends on `propext`, `Classical.choice`, `Quot.sound` and nothing else |
| Kernel replay | of the 2,701,132 declarations that `Main` imports (the archive, Mathlib, Lean's library), the 2,695,292 that are not marked unsafe or partial were replayed through the kernel from an empty environment: 2,084,256 theorems, 556,318 definitions, 15,769 inductive types; 0 failures; 57 minutes on 28 threads. The other 5,840 are compiled forms and programs, which a replay does not check |
| Dependency cone | `riemannHypothesis` depends on 1,478,219 declarations: 1,075,015 of the archive's 1,548,656 theorems (counted by name), in 147,489 of the 175,014 modules that declare anything. The archive declares no axiom anywhere |
| Literature | the archive proves 179 named statements of published theorems; the proof of the final theorem refers to all of them |

The five theorems of the archive's `Main.lean`, with the definitions of its `Statements.lean`
unfolded:

```lean
theorem riemannHypothesis : RiemannHypothesis
theorem riemannZeta_eq_zero_re :
    ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2
theorem LFunction_ne_zero_of_half_lt_re :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
theorem LFunction_eq_zero_re :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
theorem LFunction_eq_zero_re_of_isPrimitive :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

This certifies that the theorems hold in Lean with Mathlib. It does not certify any description
of the proof, including ours. Three limits: Mathlib was not rebuilt from source (its compiled
files came from the community cache for the pinned commit; the replay passed its declarations
through the kernel again); the replay program is ours and has not been reviewed by anyone else;
and we know of no other build of the archive. An independent one would be worth having, and
everything needed is in `verify/`.

## What the argument is

The paper says it at length. In one paragraph: a windowed form of Landau's theorem reduces
the statement, for each character, to a one-sided bound for a smoothed sum over prime powers on long
windows of scales. An exact identity for an auxiliary CM field turns that bound into an upper
bound for a weighted count of prime powers whose Frobenius lies outside a CM type. The upper
bound has the shape x/m + m, and the exponent 1/2 comes from balancing the two at m near the
square root of x; m is the length of a chain of theta lifts between definite unitary groups.
The bound is proved by squeezing the slope of a lattice of periods between two estimates. From
below: periods are highly divisible at inert primes, because a CM elliptic curve has a formal
group of height two there, and a slope inequality for nearly tight frames of maps transfers
that divisibility to the lattice of periods. From above: the slope of that lattice is computed,
and through the Chowla-Selberg formula it is exactly the main term of the count.

## Layout

| Path | Contents |
|---|---|
| `paper/` | the paper: `main.pdf`, its LaTeX source, the bibliography with the record behind every entry (`refs/`), and the table of where each statement was read (`basis.md`) |
| `verify/` | the scripts and the two Lean programs (dependency cone, kernel replay), and the output of our run in `verify/results/` |
| `notes/` | the reading notes the paper was written from, including the reports on bounded parts of the source |
| `lean/` | three corollaries proved against the archive, and statements of consequences worth formalising |
| `ROADMAP.md` | what could be done next |

## Reproducing the verification

On a Linux machine with 32 cores, 128 GB of memory and 150 GB of free disk:

```sh
mkdir work && cd work
bash /path/to/verify/setup.sh                       # fetch, check the hash, unpack, toolchain, Mathlib cache
python3 /path/to/verify/scan.py lean.tar.gz > scan.txt   # static inspection, before any build
bash /path/to/verify/janitor.sh > janitor.log 2>&1 &   # keeps the disk from filling; see the script
bash /path/to/verify/build.sh > build.log 2>&1      # about 13 hours
kill %1                                             # stop the janitor once the build has ended
bash /path/to/verify/check.sh                       # statement and axioms
bash /path/to/verify/cut.sh /path/to/verify/cut out       # dependency cone, about 10 minutes
LEAN_NUM_THREADS=28 bash /path/to/verify/replay.sh /path/to/verify/replay out # kernel replay, about an hour
```

Compare with `verify/results/`.

## Authors and licence

Qui Vincit and Fable. Fable is a language model (Claude, Anthropic); the paper's Section 12 says
who did what. The mathematics is Levent Alpöge's and that of the model he worked with; this is
an exposition of it.

Text and data are under CC BY 4.0, code under the MIT licence; see `LICENSE`. Corrections are
welcome as issues or pull requests.

## Versions

- **1.1**, 21 November 2026. Corrections after two referee reads of version 1.0 made by further
  instances of the model, each finding checked against the Lean source or the results files
  before the text was changed.
  - Counts of the archive's declarations are now by distinct name. Version 1.0 counted a
    theorem once for each module that declares it (1,093,609 of 1,588,253 in the cone); by name
    the figures are 1,075,015 of 1,548,656. The share, 69%, is unchanged.
  - The static inspection is now a published script with its output (`verify/scan.py`,
    `verify/results/scan.txt`).
  - The kernel replay is described exactly: 2,695,292 of the 2,701,132 imported declarations,
    the rest being unsafe or partial ones that no replay checks. A limit is added: the replay
    program is ours and unreviewed.
  - The statement about Vandiver's conjecture in Section 8.1 was wrong for the field of
    $\ell$-th roots of unity and is corrected.
  - The error term left by the period side is the first cost of Section 4.4, not the third;
    the size conditions that make the three costs come out are now stated; the lattices $N_u$
    are rescalings of sublattices, not lattices containing $M_u$; the clauses that close the
    chain of Section 5.6 are named.
  - In Appendix C the comparison of each formal statement with its published theorem is
    attributed to the reports it came from, and one row is relabelled (99 general, 75 special
    cases).
  - Smaller corrections of notation, attribution and cross-reference.
- **1.0**, 21 November 2026. First version.
