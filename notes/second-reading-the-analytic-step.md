# Second reading: the analytic step, and what the three inputs feed

Read 2026-11-20 from the source text of Alpöge's Lean archive, while the build was still running. This goes below the signatures for steps 3 and 4 of `spine-first-reading.md`. Definitions were read in full where a file is named. Sentences marked *inferred* are my reading of what a definition is for, from its shape, its names and the author's note; they were not read off a proof.

The short version: the proof bounds a weighted count of prime powers from above by an explicit main term, and an exact identity turns that upper bound into a one-sided bound on the smoothed prime sum. The error is a sum of three costs, of sizes x/m, m and k/n², where m is the number of lifts. They balance at m ≈ √x. That balance is the square root in the Riemann Hypothesis.

## 1. From a bound on windows to the zero-free half-plane

Files: `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/{PrimePairSizeCondition, ExplicitFormulaErrorOfHostConditions, Window, Analytic, TopWin, TopDefs}.lean`.

- A **level** Λ is a finite set of primitive Dirichlet characters closed under inversion. For a character ψ the proof uses the cyclic group it generates, of order o.
- For a character χ, `gChi χ y = Σ_{n ≤ y} Λ(n) χ(n) (y/n − 1) + y·L′/L(1, χ)`, and for χ = 1 it is G(y) = Σ Λ(n)(y/n − 1) − y(log y − 1 − γ).
- `Gm(y) = G(y) + Σ_{ψ ≠ 1 in the level} w_ψ · Re gChi(ψ, y)` with weights w_ψ = 1/(3o + 1), or 1 for one exceptional real odd character. The coefficient of Λ(n) is non-negative.
- **Landau on windows** (`FormBAt`): if `Gm(x) ≤ x^θ` holds on a set of x that contains, beyond every point, a whole interval [Y, Y^λ], then no L-function in the level vanishes for Re s > θ. The proof uses λ = 3/2.
- **What must be supplied** (`ChebyshevInequalityOnWindows`, `ChebyshevInequalityAtWindowScale`): for every small ε, a family of arithmetic data indexed by x, with windows of exponent λ, on which a condition `ChainTied` holds; and the implication `ChainTied` ⇒ `Gm(x) ≤ x^(1/2 + Cε)`. The first is `TopG` (section 4). The second is `level_gm_le_on_family_scales`, and its content is sections 2 and 3.

## 2. The identity: a count of prime powers equals a main term plus a sum of G-functions

File: `Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean` (140 lines), with `Formalism/ThickAverageLoss/PartnersToFactorsAt.lean`.

The setting is an abelian extension of ℚ with Galois group 𝔊 = (ℤ/2)² × H, H a finite abelian group, ramified only at 2 and two odd primes q and d. Half of 𝔊, the elements with first coordinate 0, is called Φ; in the files that build this data Φ is a CM type. Each prime has a Frobenius element and an inertia subgroup in 𝔊. Each character ψ of 𝔊 gives a Dirichlet character, and `GPsi(ψ, y)` is its G-function; for ψ = 0 it is G itself.

Fix a size a > 0, a translate t ∈ H, and a positive weight w(ρ) for each ρ ∈ Φ. Then

    ASK = Σ_p 2 log p · Σ_{i ≥ 1, Frob_p^i ∉ Φ} max(a/p^i − w(ρ_{p,i}), 0)     (plus a term at d),

where ρ_{p,i} ∈ Φ is the partner of Frob_p^i under a fixed bijection of 𝔊 ∖ Φ with Φ depending on t, and

    MAIN = a · ( log a − 1 − γ + L′/L(1, χ_Φ) − mean over ρ ∈ Φ of log w(ρ) ),

with χ_Φ the quadratic character that cuts out Φ.

**`AskMainBalance`** is the exact identity

    ASK − MAIN = (1/|Φ|) Σ_{g ∉ Φ} Σ_ψ ψ̄(g) · w(ρ_g) · GPsi(ψ, a / w(ρ_g)).

It is character orthogonality applied to the count; nothing is estimated. So an upper bound for ASK is a statement about a weighted combination of G-functions at the points a/w(ρ).

## 3. The inequality, and why it gives a square root

File: `Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean` (183 lines).

**The hypothesis** (`GrowthInequalityHypotheses`). Take a set TT ⊂ H of sizes with a_t ≈ x·b, and m systems of weights, indexed by j = 1, …, m and by a translate u₀ ∈ H. The weights come in two kinds:

- on a "thick" set of places (a subset T2 ⊂ H of density δ, moved by u₀) the weight is about b, so a/w ≈ x: the scale at which a bound is wanted;
- elsewhere the weight is at most 2b′ with b′ far smaller, so a/w ≥ X′ = exp(x^(ε/3)): a scale so large that the classical zero-free region already bounds every `GPsi` (`ThinScales`, with θ = exp(−c·x^(ε/8))).

The one substantive assumption is `topExcess ≤ Err`: the mean over u₀, t and j of (ASK − MAIN) is at most Err. It is an upper bound on a count of prime powers.

**The mechanism** (`ThickPartTranslateMean`, `GrowthInequalityForm`). Averaging the identity of section 2 over the translates u₀ kills every character that is non-trivial on H. Four survive, the characters of (ℤ/2)², and the thick places contribute

    (δ·b/2) · ( G(x) + G_ψ₁(x) − G_χΦ(x) − G_ψ₁χΦ(x) ).

The three non-trivial ones are assumed bounded by x^(1/2 + ε) at the single point x (`ValuesAtX`). The result is

    |TT| · m · b · (δ/2) · ( G(x) − 4·x^(1/2 + ε) )  ≤  Err + small.

**The sizes** (`SizeWindows`, `GrowthSizeBound`). With n = |H|, and k a rank parameter, the windows require m between x^(1/2 − ε) and x^(1/2 + ε/2), x·m ≤ k ≤ n²·x^(1/2 − ε), δ ≥ x^(−ε), and

    Err ≤ x^(Cε) · ( |TT|·a_E·(1 + m²/k)  +  m·( 2n·m·b·x^ε  +  |T2|·k·b·x^(2ε)/n² ) ),   a_E ≤ 2xb.

Dividing by |TT|·m·b·δ, the three terms are about

    x/m,     m,     k/n².

The first falls with the number of lifts and the second rises with it. At m ≈ √x all three are x^(1/2 + O(ε)), and `GrowthSizeBound` concludes `G(x) ≤ x^(1/2 + (C + 3)ε)`.

This is the shape of Stepanov's bound: a quantity of size x, divided by a multiplicity m, plus the price of having imposed the multiplicity, minimised over m.

**What is assumed about other characters.** The three quadratic-type characters need the bound at x before G gets it. The files `Formalism/ThickAverageLoss/Statement.lean`, `JacobiWeightFamilies`, `WideWeightTheorem` and `GL3MeanSquares` state results that average over a family of the auxiliary prime d and discard an exceptional set. *Inferred:* d is chosen so that its characters are already well behaved at x, by a mean-value theorem over the family. Not read.

## 4. Why the count is at most the main term

File: `Formalism/RankGapBounds/MeanBoundSecondForm.lean` (229 lines). It states, in real numbers only, the proposition `MeanBoundSecondForm`: ten hypotheses imply `mean ASK ≤ mean Main + ErrX`, where `Main` is the main term of section 2 summed over the m lifts and the sizes a_t.

**Correction, same day.** That proposition is a variant the final theorem does not use: its name occurs only in its own definition and four import lines, and it has no proof. What `ChainTied` requires is the record `SizeData₂` in `Formalism/SizeWindowBrackets/SChain.lean:17`. Its `DIV` and `SlopeIneq` are the same statements as below; `SlopesN`, `Losses` and `Count` are replaced by `QuotientSlopeBoundsWith`, `LossBounds` (for every translate, not on average) and `Count5`; and the bound it feeds holds for every translate (`each_unit_bound_statement`, `Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:175`). The chain of ideas below is unchanged. `slices/lattices.md` has the used statements and the theorem that supplies each. The record `ChainTied` ties each number to the arithmetic data (`Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean`).

For each translate u₀ and each "word" u there are three lattices, known here only through their slopes: N_u (rank d, slope μ_N, maximal slope), M_u, and a target lattice written CC; and a height h(u) and a level prime T(u). The hypotheses that carry the argument:

- **`Losses`**: the mean of ASK − Ga is at most a loss term. Ga is a sum of local "gains" over the places in the support. So the count of section 2 is, up to that loss, at most the total gain.
- **`SlopesN`**: `μ_M + Ga + Fo − Ee − (loss) ≤ μ_N`. The gains raise the slope of N above that of M.
- **`SlopeIneq`**: `s − log|W| − (1 − δ′)⁻¹·(4·u_F·log(1 + HH/u_F) + (η + 4√e)·HH) ≤ μ_CC`, where s is the rank-weighted mean over u of μ_N − h. The mean slope of the N_u, less their heights, is at most the slope of the target, with an error governed by three defects δ′, η, e.
- **`DIV`**: `μ_CC + h − Fo ≤ Σ_t ( m·(ph(a_t) − a_t·logOm) − a_t·log T ) + small`, with `ph(y) = y log y − y` and `logOm = γ + log(π/v) − L′/L(1)`. The target's slope is at most m copies of log(a!/Ω^a), where log Ω has the form of the Chowla–Selberg formula, less a·log T.
- **`Count`**: log T is at least Σ_j (mean over ρ of log(w_j(ρ)·v/π)) plus m times a fixed term, up to an error with m²/k in it.

Chained: gain ≤ (slope of N) − (slope of M) ≤ (slope of the target) + errors ≤ m·log(a!/Ω^a) − a·log T + errors, and `Count` replaces log T by the weights. The log(π/v) inside logOm cancels the v/π inside `Count`, and what is left is exactly `Main`. So the upper bound on the count is a slope inequality between lattices, with p-adic gains on one side and a period on the other.

**What the lattices are** (read by a delegated pass, `slices/lattices.md`; I checked its claims about which statements are used, not its descriptions of the lattices). All three are lattices over the integers of a totally complex Galois field with a Hermitian metric at each infinite place. M_u is an integral structure on vector-valued forms on a definite unitary group, normed by the Petersson product. N_u is a sublattice of it scaled up by ∏ 𝔓_w^(−⌊e_w·gain⌋): the gains are built into its definition, not proved as an inequality between N and M. Their cost is a separate statement (`adm2`): the periods of forms in the unscaled sublattice are divisible by 𝔓^⌊e·gain⌋, which is what keeps the scaled lattice mapping into the target. The target is the dual of a lattice of periods, and the height bounds the norm of the map sending a form to the period of its m-fold iterated lift. `DIV` rests on a statement that turns a factorisation of a determinant over the m lifts into a bound on the target's slope; this is one place a determinant enters.

*Inferred, not read:* the reading that follows. The surrounding definitions and file names point one way.

- `InertK D p` is `jacobiSym (−d) p = −1`, and the count at such a prime is `Σ_{i odd} max(0, a/p^i − w)`, that is a/p + a/p³ + ⋯ cut off by the weights. The author's note, item 2, says a Taylor coefficient of a theta function at a CM point, of order a and divided by Ω^a, "is divisible by p^(a/p + a/p³ + ⋯ − O(log a))" at inert p.
- `Formalism/WindowSums/Statement.lean` has `FactorialValuationBound`: for a prime ℓ ≥ 5 and j = ⌊(b + S)/(ℓ − 1)⌋ + 1, `b/ℓ ≤ j + v_ℓ(j!) ≤ b/ℓ + 3b/ℓ² + 2S + 2`.
- `Formalism/LatticeSlopes/Statement.lean` states the slope inequality for Euclidean lattices: an injective map L → M of operator norm at most C gives `slope L ≤ μ_max(M) + log C`.
- `Formalism/ThetaLiftIndependence/Statement.lean` defines a theta lift on a definite unitary group as a finite sum over the classes of a genus with weights 1/|Aut|, defines the m-fold composite `chainOp`, and states (`ChainInt`) that the composite is integral after multiplying by the product of the m denominators.
- Files named for Chowla–Selberg and for the algebraicity of theta Taylor coefficients at CM points exist under `Development/AbelianVarietyTheory/Proofs/`.

So the reading is: the lattices are spaces of m-fold iterated theta lifts with integral structures; the gains are the divisibility of their jets at CM points at primes inert for the CM type; the target's slope is their archimedean size, a period. The object that stands where `a^q = a` stood for Stepanov is the order a of a jet: at an inert prime a jet of order a is divisible by p about a/p times. The multiplicity that is optimised is m, the number of lifts.

## 5. The three inputs, placed

- **The cohomological bound (`VWin`).** `HypV` (`CharacterBoxes/DivinNOfHypV.lean`) asks that for every member of the family, `VVle host.E R.t sqrt(b)`: the total Σ_ℓ log ℓ · Σ_j shaLen is at most √b. `LinkN` (`Formalism/SharpRestriction/GlobalTheoremInputs.lean`) bounds a ramification-weighted sum by a rank times (a size term + that total). `divinN_of_hypV` (same file, line 117) combines `HypV`, `LinkN` and a rank equality into `DIVinN`, which `DIV` needs. So the cohomological bound enters through the bound on the target's slope. An earlier version of this note guessed it entered through the defect η of `SlopeIneq`; that was wrong: η is a defect of near-orthogonality of period matrices. `supplyChi` uses `VWin` to show hosts exist at scales with windows of exponent 3/2.
- **The hosts.** `HostExW λ P` (`.../GlobalTwisting/ThinScalesIffHostBound.lean`) says: for each small ε, at every scale in a set with windows of exponent λ, there are ranks and a host (the field, the primes q and d, the level 2^e) that are `HostGood` and satisfy P.
- **`TopG`** (`CharacterBoxes/ZeroFreeAllOfTopG.lean`): for every requirement with hosts and with `HypV`, some family in the class satisfies `ChainTied` on its windows. This is where sections 2 to 4 are assembled.
- **The definite side.** `Hyps` (`.../GlobalTwisting/APerTw.lean`) is a record of about forty-five conditions on a class of families: class-number and genus-mass formulas, period identities, counting statements, surjectivity of projection maps, and `LinkN`. Each is a statement to be read on its own; I read their names and the types of a few.

## 6. Still unread

- The proofs of the ten hypotheses of `MeanBoundSecondForm` for the actual lattices, and what those lattices are in the Lean's own definitions (`div.Nu`, `fm u`, `div.RR`). Section 4 transcribes the statement they feed and infers the rest.
- Where a determinant and Weil positivity enter. Neither appears on the path read here. `Formalism/FockGram` (Gram matrices positive semidefinite) and `ThetaLiftIndependence` (`DetChain`, `DetBlocks`) are the places to look.
- The statement that a jet at a CM point is divisible at inert primes, in the Lean's own words (`Formalism/GaussJetBounds`, 23 statement files).
- How the three auxiliary characters get their bound (section 3, last paragraph).
- Landau on windows: the statement was read, its proof was not.

## 7. A candidate for the first half of the one-page statement

> **Proposition A.** Let 𝔊 = (ℤ/2)² × H be the Galois group of an abelian CM field ramified at 2, q, d, with CM type Φ. For sizes a_t ≈ x·b and weights that equal b on a thick set of density δ and are tiny elsewhere, suppose the mean of the prime-power count ASK exceeds its main term by at most Err, and suppose the three quadratic characters of (ℤ/2)² satisfy |G_ψ(x)| ≤ x^(1/2 + ε). Then
>
> G(x) ≤ 4·x^(1/2 + ε) + 2·Err / (|TT|·m·b·δ) + (small).
>
> **Proposition B.** If Err is at most x^(Cε) times (x/m + m + k/n²) in those units, with m ≈ √x and k ≤ n²·√x, then G(x) ≤ x^(1/2 + (C + 3)ε). If this holds on windows [Y, Y^(3/2)], the L-functions of the level do not vanish for Re s > 1/2.

Both are transcriptions of definitions in two files of 140 and 183 lines. The rest of the proof is the hypothesis of Proposition B.
