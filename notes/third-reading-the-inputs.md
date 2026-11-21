# Third reading: the inputs

Read 2026-11-20 from the source text of Alpöge's Lean archive, while the build was still running. This continues `second-reading-the-analytic-step.md` into the statements that feed the count bound. Sections 1 to 3 are my own reading; the later sections integrate six delegated readings whose load-bearing quotations I checked against the source, and say so where I did not.

Marks: **read** means the definition or statement was read and is transcribed; *inferred* means an interpretation.

## 1. The cohomology groups, exactly

File: `Formalism/GaloisCohomology/Statement.lean` (186 lines). **Read.**

For a number field F and a prime ℓ, let S be the places above ℓ and G_S the Galois group of the maximal extension of F unramified outside S. Then

- `Sha D e` is the group of classes in H¹(G_S, ℚ_ℓ/ℤ_ℓ(−e)) that are trivial at every place above ℓ, and `shaLen` is its length as a ℤ_ℓ-module;
- `VLen D e` is the length of H²(G_S, ℤ_ℓ(e + 1));
- `VFormula` states, from Poitou–Tate and local Tate duality, `VLen + length H⁰(ℚ_ℓ/ℤ_ℓ(−e)) = shaLen + Σ_{v | ℓ} length H⁰(G_v, ℚ_ℓ/ℤ_ℓ(−e))`.

So `VWin` bounds, over the fields of the tower, Σ_ℓ log ℓ · Σ_{1 ≤ e < x^401} length Sha¹(𝒪_E[1/ℓ], ℚ_ℓ/ℤ_ℓ(−e)), and requires each to be finite. By `VFormula` this is a bound on the groups H²(𝒪_E[1/ℓ], ℤ_ℓ(e + 1)), which are the ℓ-parts of the even K-groups of 𝒪_E. That is why the author's note says the result implies vanishing of K-groups of ℤ, and why it is a statement of Vandiver's kind.

## 2. `Green`

File: `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:108`. **Read.**

For every prime g and every d ≥ 1 there is a map P ↦ τ_P from monic irreducible polynomials of degree d over 𝔽_g with non-zero constant term to cuspidal irreducible characters of GL_d(𝔽_g), injective and onto the cuspidal characters, with τ_P(1) = ∏_{i=1}^{d−1}(g^i − 1) and, on elements y with irreducible characteristic polynomial and eigenvalue z, τ_P(y) = (−1)^{d−1} Σ_{i<d} θ(z^{g^i}).

This is J. A. Green's 1955 parametrisation of the cuspidal characters of the finite general linear groups. It is a literature row (`greenRegularCharacters`), and `shapeWin` passes it to one link, `link_irr`.

## 3. How the middle is wired

File: `Development/AutomorphicArithmetic/CharacterBoxes/ShapeWin.lean` (51 lines). **Read.**

`shapeWin : Green → TopShape … TopG` takes the forty-odd conditions of the record `Hyps` as arguments and produces `TopG` by one call, `topDesWin`, whose arguments are named links: `link_ex` (existence of families, from hosts and `HypV`), `link_eta`, `link_irr` (from `Green`), a small-level rank equality (from surjectivity of level projections), `linkDIVt_closedK` (the division inequality, from "bridge rows"), `link_gl`, `link_g`, `link_alt`, and the hypothesis `Closed … LinkN`. The record `Hyps` is itself produced by `nonempty_hyps_definite_side_of_closed_bound` from: the literature bundles, `ThetaIntegralsAgree`, `LocalMatching`, the covolume bound, a local Langlands correspondence, and a test-vector assembly that uses Howe duality at the real place and a convergent Siegel–Weil formula.

This file is wiring. Each link is a statement to be read where it is proved.

## 4. Landau on windows

Files: `Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean:8` (`formB`), `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean:11`. **Read.**

> `zeroFree_of_rpow_window`: for a family F of characters, 0 < θ < 1 and δ > 0, if for every Y₀ there is Y ≥ Y₀ with `Gm F y ≤ C·y^θ` for all y in [Y, Y^(1+δ)], then the L-functions of F do not vanish for Re s > θ.

The classical theorem of Landau needs the bound for all large y. This version needs it only on one window [Y, Y^(1+δ)] beyond every point, which is what lets the argument work at scales where suitable fields exist rather than at every scale. It is proved in the same directory (thirty files: a kernel integral, iterated derivatives of a Laplace transform, a "nearest zero" step); the proof was not read.

## 5. The lattices, and where the divisibility is spent

From `slices/lattices.md` and `slices/jets.md`. I verified against the source: that `MeanBoundSecondForm` is unused and the record `SizeData₂` in `SChain.lean` is the one `ChainTied` requires; `divinN_of_hypV`; the constants γ and ρ; the radius lemma `LemmaRA`; and the definition of `zeroCh`.

- **The three lattices.** Lattices over the integers of a totally complex Galois field, Hermitian at each infinite place. M_u: an integral structure on vector-valued forms on a definite unitary group, with the Petersson norm. N_u: a sublattice of M_u scaled up by ∏ 𝔓_w^(−⌊e_w·gain⌋). The target: the dual of a lattice of periods. The height bounds the norm of the map from a form to the period of its m-fold iterated lift.
- **Where each hypothesis comes from.** The slope inequality is a general statement about lattices (`Formalism/HarderNarasimhan`, `theoremF`). The bound on the target's slope (`DIV`) rests on `Formalism.DivisorInequality.boundsMu`, which turns a factorisation of a determinant over the m lifts into a slope bound, and needs `DIVinN`, which is where the cohomological bound enters. The count hypothesis is a dimension count resting on mass formulas and Weyl's dimension formula.
- **The gains are a definition; their cost is one statement.** N_u is defined with the gains in it. What must be proved is `adm2`: the periods of forms in the unscaled sublattice are divisible by 𝔓^⌊e·gain⌋.
- **The divisibility theorem exists.** `Formalism/GaussJetBounds`: with γ = ℓ/(ℓ² − 1) = 1/ℓ + 1/ℓ³ + ⋯, a derivative of order κ at 0 of a function of the form U(g(z))·exp(ε·b(z)), in the logarithmic coordinate of the height-two formal group, has ℓ-adic valuation at least Σ κ_i(γ − σ_i) − (number of variables)·(log_ℓ a + 1). Theorem A of that module gives the exponent for several "letters", with top terms Σ_{e odd} ν/ℓ^e cut by a capacity, the same shape as the count. A statement that D^p vanishes was not found; the nearest is `CM3`: at an inert prime the formal group of a CM curve is the height-two one.
- **Where the divisibility is used: settled by a trace** (`slices/divisibility-trace.md`; every hop from the period divisibility up to the top theorem was read there, and I checked `admissible_level_two`, `split_bound_eleven_one` and the two jet theorems it calls). The jet theorems are on the path.
  - The period divisibility is `adm2` at `Formalism/SharpRestriction/Divisibility/LocalQuadraticParts.lean:206`, proved by `admissible_level_two` (`Formalism/LocalToGlobal/GroupLattices/AdmissibleAtGeneratorPlaces.lean:214`). It is used by the bound on the target's slope (`DIV`), not by the gain inequality (`LinkG`). A different statement also called `adm2` sits under `Adm2F` and is a Mertens bound on the level primes; the lattices slice crossed the two.
  - The gain is a closed formula fixed by `ParametersFill`: γ·Σ(a − 2c) less corrections on the "served" Frobenius orbits, plus non-negative terms on the others. It is not defined as whatever happens to divide.
  - At the places where the gain is positive, the divisibility comes from two jet theorems. On served orbits, a theorem in `Formalism/ThetaLogCoordinates` with the same rate p/(p² − 1). On unserved orbits and at inert primes, `split_bound_eleven_one` (`Formalism/SharpRestriction/Divisibility/JetPolynomialLogs/LocalBoundElevenComparison.lean:64`), which calls Theorem A, the log-loss lemma and the radius lemma of `Formalism/GaussJetBounds`.
  - At the level primes the "gain" is a loss, and at two special primes it is zero; those are covered by conditions of the record of definite-side hypotheses.
  - `LinkG` on the used route sets a chain map to zero (`zeroCh`), so its unit bound is trivial there, and it bounds only the sizes of the gains and lattice lengths. It consumes a "first theorem", a "second theorem" and an "integrality from metric" statement proved through the Gram-window bound of section 9. That last is a different "Theorem A" from the one in `GaussJetBounds`.
  - Not read: the proofs behind several divisibility inputs that reach the top only as conditions of the definite-side record (`SysTw`, `OrbitBoundWithoutOperator`, `JetIntegralityBis`, the period-integrality rows). They were traced one level up to named theorems and no further.

## 6. The hosts, and the three auxiliary characters

From `slices/hosts.md`. I verified that the named theorems exist where cited (`pair_share`, `hostThickExists`); the rest is the slice's reading.

- **A host** is the field cut out of a cyclotomic field by four conditions: ±1 modulo 2^(e+2), ψ = 1, and the quadratic characters of q and d equal to 1. So it is ℚ(√−q, √−d) times a real 2-power cyclotomic layer times the field of ψ, with Galois group (ℤ/2)² × A and CM type induced from ℚ(√−d). It is the same field the cohomological bound is about.
- **The auxiliary characters** are ξ·(·/q)^i·(·/d)^j with (i, j) ≠ (0, 0). Their conductors are at least q ≈ exp(x^(ε/(5J))), far above any power of x, so the bound needed at x concerns a sum much shorter than the conductor. It is obtained on a whole range of scales from a mean-square bound over prime moduli and a zero-density count near Re s = 1 − 1/400, and a good pair (q, d) is picked by counting: at least half the q are good, and for each, at least half the d. Nothing uses zeros near the critical line, so there is no circle.
- **The large scale** uses the classical zero-free region; on the final path no exceptional character occurs.
- **Behrend.** The thick set is built from Behrend's construction in Mathlib, so that the Frobenius orbit of a prime meets it at most twice in a window of about 4050·log x steps.
- **Off the path.** `WeightThm`, `WeightCor`, `WeightedSieveImpliesRH`, `ChebyshevWeightedAverageOverJacobiFamily` and `EstimateImpliesRH*` are referenced by no other file and no proof of them was located. The second reading named them as candidates; they are not how the bound is obtained.

## 7. The cohomological bound

From `slices/vandiver.md`. I verified the statement `NumberU3U_s` against the source.

- **Cases.** For odd ℓ the group splits under complex conjugation into a minus part, bounded by Bernoulli-type data, and a plus part, which is Vandiver's side. Every triple (ℓ, twist e, character) falls into one of six cases, and a theorem `of_four_alt` combines a bound for each.
- **One integer for all ℓ.** In the cases treated through U(3) over an imaginary quadratic field and through GSp4, there is one non-zero integer NN with log|NN| polynomial in the conductor and the twist such that the ℓ-part is at most 2·v_ℓ(NN) for every ℓ. Summing log ℓ times the lengths over all ℓ then costs log|NN|.
- **How NN bounds the group.** Through a deformation ring of the reducible representation Ψ ⊕ 1 ⊕ Ψ⁻¹: the length is at most 2·Σ v_ℓ(tr ρ(σ) − t) over its automorphic points.
- **The dominant term** is from Iwasawa theory in cyclotomic towers. All but boundedly many twists are controlled; the exceptional ones are bounded crudely (`LemmaK`, from a rank bound on the homology of GL_n of the integers), which is affordable only because the windows keep those twists small. Ferrero–Washington is proved in the tree.
- **"Patching"** here glues Galois representations of base changes to infinitely many CM quadratic fields into one two-dimensional representation over a totally real field. It is not Taylor–Wiles patching.
- **Scope.** Every ℓ and every twist is bounded; nothing is averaged or discarded; but x is confined to windows [Y, Y²]. The square root in `VWin` is slack.

## 8. Galois representations from theta lifts

From `slices/galois-from-theta.md`. I verified the definition of `AwayB` against the source and corrected the first reading's description of `Row0b`.

- **Both groups are definite.** The lift runs between unitary groups compact at infinity.
- **The geometric input** (`GeoOne`) gives, for an automorphic representation of U(a) with a odd and local conditions at two places, a Galois representation of some dimension in the étale cohomology of Kuga–Sato varieties over compact unitary Shimura varieties, with a congruence relation and crystalline comparison. Hodge numbers come from a holomorphic Lefschetz fixed-point formula.
- **Why lift.** The identification the geometry needs assumes odd dimension. Even dimension is lifted twice to odd dimension; the lift's parameters are the original's plus known characters, which are subtracted.
- **The chain** then runs through ℓ-adic congruences and limits of traces, base change between GL_a and U(a), and gluing over quadratic CM extensions. No eigenvariety and no stable trace formula is named.
- **Existence of the lift** is a Rallis inner product through the Siegel–Weil formula and doubling, in the range where everything converges absolutely, with non-vanishing by a direct estimate. No L-value is computed.
- **Compatibility away from ℓ is partial**: equality only for parameters that are sums of characters, and equality of inertia characteristic polynomials in a tame case. It is less than Caraiani's theorem.
- **The three "open literature" rows are not assumptions.** Two of them are the same proposition as `Row0b`, supplied by the theta-lift theorem; the third is constructed in the tree.

## 9. Determinants, and what is off the path

From `slices/determinants.md`. I verified the statement and proof location of `GramWindow2`, that `DetGain` occurs only in its own definition, and the chain from `theorem_A_closed_form_holds` into `local_flatness_results`.

- **No Weil functional.** There is no explicit-formula functional in the source and no positivity statement about one. "Weil" in the tree means the Weil representation or Siegel–Weil. The author's note speaks of evaluating "W(1_S)"; in the Lean that role is played by the slope inequality and the count.
- **The determinant on the path** is `GramWindow2` (`Formalism/SharpRestriction/GrowthBounds/FockGramWindow/GramWindow2.lean`), proved in the tree with the Smith normal form. Statement, in words: let a family of p-adic Gram matrices along a window of consecutive integers be the values of one polynomial matrix with non-zero determinant. Then the total p-adic degeneracy of the Gram matrices over the window is bounded in terms of the degree and leading coefficient of that determinant. This has the shape of Stepanov's method: a non-zero polynomial cannot vanish to high order at many points. The chain from it to the top theorem was read hop by hop in the slice.
- **Other determinants on the path**: the slope of a column lattice as −log det of a Gram matrix; a lattice index as the norm of a Gram determinant; a covolume as the root of one; a Bessel-model function equal to a Gram determinant and non-negative; and `BForm`: the composite of the m lifts with its adjoint is a scalar κ₀·∏ z_i, an iterated Rallis inner product formula. Whether the z_i are central L-values was not read.
- **Off the path**: every determinant statement in `Formalism/ThetaLiftIndependence`, `FockGram` and `SmithDeterminants` that the candidate list named; `DetGain` (Σ g_p log p ≤ log|Δ| when g_p ≤ v_p(Δ)), which is the closest thing in the tree to "positivity via a determinant"; `BesselPeriodGGP`; and three alternative end-games, one of which reaches only Re s > 3/4. These read as earlier or parallel formulations left in the tree.
- **How on and off were decided.** By a reference cone from the top theorem built by resolving identifiers in declaration bodies (831,160 of 1,059,499 names). It does not follow typeclass instances or attribute-driven tactics, so "off the path" carries that caveat until the build gives the true dependency cut.


## 10. The slope inequality itself (Theorem F)

Read by me: `Formalism/HarderNarasimhan/StatementFrameF.lean` (statement), `Formalism/CorankShare/StatementFR.lean` and `Formalism/HarderNarasimhan/StatementPl.lean` (definitions). It is proved as `theoremF` in `Formalism/HarderNarasimhan/ShiftInvariance.lean:61`; the proof was not read. It is a statement about Hermitian lattices over a number field with no automorphic content, and it is the cleanest self-contained piece met so far.

**Setting.** K a totally complex number field. A target lattice cc in a K-space W, and for each i in a finite set I a lattice N_i in a K-space V_i, all with a Hermitian metric at every infinite place. K-linear maps B_i : V_i → W with B_i(N_i) ⊆ cc. The slope μ is twice the normalised Arakelov degree per rank, plus a constant depending only on K; μ_max and μ_min are the largest and smallest slopes in the Harder–Narasimhan filtration. The height of a map is the mean over the infinite places of the logarithm of its squared operator norm (`htMap`).

**Hypotheses.**
- Heights: ht(B_i) ≤ h_i.
- s is at most the rank-weighted mean of μ(N_i) − h_i, and no source is far above it: μ_max(N_i) − h_i ≤ s + u.
- HH ≥ s − μ_min(cc), HH ≥ 0.
- At one infinite place the maps form an approximately tight frame. After a change of basis and an extension of the target by a small extra space (a fraction at most δ of the dimension), there are weights γ_i > 0 with Σ_i ‖γ_i·B_i*B_i − 1‖² ≤ e·Σ_i rank(N_i) in the Hilbert–Schmidt norm, e ≤ 1/4, and the frame operator Q = Σ_i γ_i·B_i B_i* satisfies tr(Q²) ≤ (1 + η)·tr(Q)²/dim.

**Conclusion.**

    μ(cc) ≥ s − log|I| − (1 − δ)⁻¹·( 4u·log(1 + HH/u) + (η + 4√e)·HH ).

**In words** (*inferred*). The classical slope inequality says that an injective map of lattices of height h forces μ_max(source) ≤ μ_max(target) + h. That bounds only the top of the target. Here many sources map in, each nearly isometrically, with images that are nearly orthogonal and together nearly fill the target. Then the mean slope of the sources, less their heights, bounds the slope of the whole target from below. The companion statement `FrameLA1` in the same file is the linear algebra under it: for a nearly tight frame, if each source has a subspace missing at most a fraction ε of its dimension, the images of those subspaces span all but a fraction η + 4ε + 4√e of the target.

In the argument the sources are the lattices N_u of forms with the gains built in, the maps send a form to the periods of its iterated lift, and the target is the lattice of periods. The gains raise the slopes of the sources; Theorem F transfers that to the target; the determinant computation (`DIV`) bounds the target's slope from above by the period term. The prime-power count is squeezed between the two.

## 11. Under the divisibility: CM curves, theta kernels, and why the rate is ℓ/(ℓ² − 1)

From three readings of proof bodies: `slices/jet-bridge.md`, `slices/service-inputs.md`, `slices/period-rows.md`. I verified against the source the statements `CM2` and `CM3`, the logarithm `ltLog`, `chowla_selberg_eta`, the Kronecker limit formula, the Weyl-lattice duality statement, and that the named bridging theorems exist where cited.

**The mechanism, in three lines** (*the slice's own summary, which I find correct as mathematics*). Let F be the height-two formal group over ℤ_ℓ with logarithm log_F(X) = Σ_j X^(ℓ^(2j))/ℓ^j (`ltLog`, `Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean:35`). Its exponential has n-th coefficient of valuation at least −ρ(n − 1), with ρ = 1/(ℓ² − 1). A function with integral coefficients in X, expanded in the variable z = ε·log_F(X), therefore has n-th Taylor coefficient times n! of valuation at least v(n!) − ρn, which is about n/(ℓ − 1) − n/(ℓ² − 1) = n·ℓ/(ℓ² − 1) = γn, less a logarithmic loss. That is the divisibility of jets at an inert prime: a/ℓ + a/ℓ³ + ⋯.

**Why the function is integral in X: a CM curve is used.**
- `CM2` (same file, line 45): for squarefree d ≡ 3 mod 4, a lattice L with CM by (1 + √−d)/2, and a prime ℓ ≥ 5 not dividing d, the curve has a model with integral g₂, g₃ and unit discriminant over the maximal unramified extension of ℚ_ℓ. It is derived from global Artin reciprocity for ℚ(√−d): the Artin map to the class group, with a Chebotarev statement, shows inertia fixes j(L).
- `CM3` (line 49): if moreover −d is not a square modulo ℓ (ℓ inert), then the curve's local series, composed with ε·log_F for a unit ε, has integral coefficients in the unramified extension. That is: the formal group of the CM curve at an inert prime is the height-two one, and the complex coordinate z is ε·log_F of an integral parameter.
- From these: theta functions of the CM lattice, normalised and translated by torsion points, become integral series in that parameter (`IntInert`), and the kernel of the lift is an integral combination of such translates (`comb_of_tied`). That gives the hypothesis ("B0") under which the jet theorems apply.
- A jet is a differential operator ∏ det(Y·∂_Z) applied at 0 to the Taylor series of the lift's theta kernel, and the period of the m-fold lift of a form is a polynomial in such jets. The "letters" index positions along a Frobenius orbit of the CM type; each carries a block of variables and a Young diagram.
- The Weil representation supplies only the polynomial (Fock) model of the forms and the law of the kernel.

**Split primes and the level primes.**
- At the two special primes the bound is CM theory at a split prime: jets of theta kernels on a CM abelian variety normalised to unit discriminant are integral there.
- At the level prime T the statement is a loss, with denominators up to T^(m·E) allowed, from a local computation with the kernel commuting with the Hecke operator at T up to a power of T.

**Integrality of the periods themselves is representation theory, not transcendence.** The "period" of a form on the definite group is a finite sum over classes of a genus. Its integrality comes from two facts about GL_n: the branching map between Weyl modules preserves their integral forms, and the integral forms of the Weyl module and the dual Weyl module are exact duals under the normalised Fock pairing. The only denominators are orders of stabilisers.

**The period Ω is an actual CM period, and its mean is computed.** On the used path Ω at an embedding is the area of the conjugate unit-discriminant CM lattice over π times a squared norm. The mean of log Ω over embeddings equals γ_Euler + log(π/v) − L′/L(1, χ_d). That rests on the Chowla–Selberg formula, proved in the tree (`chowla_selberg_eta`, `Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean:222`) from ζ_K = ζ·L(χ) and Kronecker's first limit formula, also proved there. This is where L′/L(1, χ) enters the main term.

**Corrections these readings made to the divisibility trace.**
- On served orbits the rate-γ gain comes from `kernel_a_two_generic` and `kernel_b_generic`; `kernel_a_one_generic` gives only an excess form.
- `OrbitBoundWithoutOperator` is proved on the used route (through `orbitBound_standardSeries_inertPlaces`), not left as a bare hypothesis.
- One argument credited there (`stmtNumE`) is discarded by the theorem that receives it.

**Flags, all four resolved by reading.**
- Resolved (section 14): the built points exist by explicit construction, and the property of integral test vectors is made during the construction, not assumed.
- Resolved: global Artin reciprocity is one of the literature rows (`GlobalTheory.Published.GlobalArtinReciprocity`), and its in-tree proof is `globalArtin` at `CompanionTheory/AutomorphicTheory/PlaceSeparation/IsOpenQuotientMapArt0.lean:233`. So the tree claims a proof of global class field theory, which Mathlib does not have.
- Resolved: the jet theorem is applied universally. Its consumer `prvF_of_orbitLetterBounds` (`Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitValuationBounds/PrvFOfOrbitLetterBounds.lean:17`) takes an arbitrary series with the integrality hypothesis and applies Theorem A's corollary to it, so the empty instance of the jet structure in the base data is not what carries the bound. The burden is that the actual kernel satisfies the hypothesis, which is the CM chain above.
- Resolved: Theorem A's size condition is supplied at that consumer by a lemma (`setting_sq`) from the shape hypotheses, at a equal to the square of the size parameter.

## 12. The record of definite-side hypotheses, and where the cost really sits

From `slices/hyps-record.md`. I verified the body of `classSel` and the statement of the existence theorem it leans on; the table of 46 fields is the slice's.

- **The record.** The top theorem consumes `HypsAlt` (46 fields: 5 of data, 41 propositions). A sibling record `Hyps` with the same field names feeds a different entry point that the top theorem does not use; earlier notes read parts of that sibling route (`shapeWin`). The used route is its twin, `shape_closed_link_n_of_green`; the two share everything from `link_gl` down, so the lattice reading stands.
- **Most fields hold by construction.** A class of families is defined as those whose points are "built" points satisfying every row property (`classSel`, `Development/AutomorphicArithmetic/CharacterBoxes/ClassSel.lean:14`). Then 28 of the 41 propositions hold because a theorem says every built point has the property; 5 more come from the definition of the class or its existence statement; 5 are chosen constants; 8 are theorems passed in directly.
- **So the cost sits in existence.** Period integrality, for instance, is a field of every built point. What must be shown is that built points exist in every family the argument needs: the field `hEx`, supplied through `memberTop_final_contextParameters` and `large_unramified_exponent_bundles_exist_alt`, with hypotheses that include a local reciprocity map and "third place" hypotheses on unitary groups. Those proofs are the next reading, in flight.
- **How the eleven conditions of the count bound are assembled** (in `linkCore`): the divisor bound and two comparison terms from `LinkDIV`; the quotient-slope bound from `LinkG` and `LinkMu`; the loss bound from `LinkG`; the slope inequality from `LinkDIV`, `LinkIRR` and `LinkS`; the count and slope conditions from mass formulas and all-family slope inequalities; one condition is positivity bookkeeping. `LinkN` and the rank equality are consumed earlier, with the cohomological bound, to turn a preliminary divisor bound into the final one.
- **The deep inputs named in the record**: the Siegel–Weil formula in the convergent range; a period identity equating the definite period with a non-zero constant times the inner product of a theta lift (Rallis-like in shape, with no L-value attached); archimedean Bessel multiplicity one in a large-gap range; mass and volume formulas (Landherr's Hasse principle, a class-number formula, a volume ratio with an Euler product); CM curves through Artin reciprocity; the bound by Sha lengths; zero-density estimates near Re s = 1. No Ichino–Ikeda or Waldspurger-type global period formula appears.

## 13. How the two lattice theorems are proved

From `slices/lattice-theory.md`. I verified that the named steps exist where cited (`theoremFSharp_of`, `theoremF_of_sharp`, the Markov bound `frameB_share`, `layer_cake_formula`).

**The slope inequality (Theorem F).** The form with −log|I| is the sharp form with a non-negative term thrown away; the sharp form has no such term. The proof runs level by level, for each τ between 0 and HH:

1. Cut each source N_i at the step of its Harder–Narasimhan filtration for slope s − τ + h_i. (The step exists because degree is supermodular.)
2. A Markov bound: since the mean of the source slopes is at least s and none exceeds s + u, the parts cut away have at most a share u/(u + τ) of the total rank.
3. The slope inequality in its μ_min form sends what is kept into the step of the target's filtration for slope s − τ.
4. The frame lemma: the images of what is kept span all but a share η + 4u/(u + τ) + 4√e of the frame space; passing to the target's own coordinates costs the factor (1 − δ)⁻¹.
5. So the target's Harder–Narasimhan step at slope s − τ has almost full rank, for every τ. Integrating over τ (the layer-cake formula) turns that into a bound on the target's slope: ∫ 4u/(u + τ) gives 4u·log(1 + HH/u), and ∫ (η + 4√e) gives (η + 4√e)·HH.

What is new against the classical method (*the slice's inference, which I share*): the classical inequality bounds one source from above by the target's top slope. Here many maps control the target's whole polygon from below, by combining steps 2, 4 and 5. The frame is used only to count dimensions, which is why it may be placed on a lift with free coordinate changes. The theorem says something only when its error is below HH, since μ ≥ s − HH is immediate from the hypotheses.

**The divisor inequality (`BoundsMu`).** It bounds the slope of the dual of a glued lattice R from above by the mean of log κ, less the sum of the slopes of m lattices M_j, plus local terms. Its core is an exact covolume computation with one inequality, a Cauchy–Schwarz step for a quotient metric. The product formula enters twice: the covolume of a rational Hermitian lattice is a sum of local discriminant terms, and in that Cauchy–Schwarz step. The determinant factorisation says that at each infinite place the volume of R is κ^D times the product of the volumes of the M_j; at the twisted primes the same factorisation at one place is read as an identity in the field and its valuations are taken. The dual of R is where the periods land. It has a single instantiation on the path, and in the divisor clause the mean of log κ cancels against the κ inside the heights.

**Both can be stated more simply.** For Theorem F: the sharp form, with the hypothesis being the robust-spanning property the frame is used for. For the divisor inequality: the exact covolume step, without the bookkeeping parameters. Several neighbouring statements in both modules are never proved or never used.

Not read: the lemmas that produce the frame hypotheses from the near-orthogonal family of period maps, and what the concrete lattices and matrices behind the divisor inequality are on the path.

## 14. Existence: the forms are all algebraic modular forms, and the content is a dimension count

From `slices/existence.md`. I verified the definition of the space of forms (`Fi`) and that the two named theorems exist where cited.

- **No existence theorem for forms is used.** The space attached to a point is every algebraic modular form of a given weight on the definite unitary group: all functions on the finite set of classes of a genus, valued in the weight representation and fixed by the stabilisers (`Fi`, `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/PredMemGamRanks.lean:151`). There is no selection of Hecke eigenforms. The lattice used for each index is the part "ramified at T". The lifts are explicit finite sums against jets of the theta kernel of a CM lattice. On this path the reading met no automorphy lifting, no passage from Galois representations to forms, and no trace-formula count.
- **The content is a dimension count.** The class number equals mass × index × (T^k − 1)^f. So the dimension of the full space is a known multiple of (T^k − 1)^f, and the ramified part has a known share of it. The level prime T is chosen in a short window so that this dimension matches the target's; its level structure also kills the stabilisers, which makes the count exact. The statement giving T (`LevelPrime`, `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LogCondLeThree.lean:81`, read by me): for any T_s with log T_s ≥ c·m·L there is a prime T with T_s ≤ T ≤ (1 + 1/(f·k))·T_s satisfying a norm-form condition. T is of size exponential in m ≈ √x while f·k is a power of x, so the interval has relative length a power of 1/log T, which is the range of the prime number theorem with the classical error term (*inferred; the proof `levelPrime_unconditional` goes through `shortNorm`, not read*).
- **Minkowski's bound** (every finite subgroup of GL_n(ℚ) has order dividing an explicit number) is proved in the tree and used only to bound the stabiliser denominators.
- **Where the heavy hypotheses go.** The literature bundle supplies class field theory for the base fields and the CM lattice, archimedean representation theory for the indefinite side, and Galois cohomology for a statement about twists. The local reciprocity map attaches parameters to rows on the indefinite side. None of them produces forms.
- **The family is not degenerate.** The rank of each N_u is positive and given by a formula. The number of lifts is forced to be at least x^(1/2 − ε) by a size condition inside `ChainTied`; the family has m ≈ √x, group order n ≈ x^(2 + 8ε) and k ≈ x^(9/2 + 10ε). That the period maps are non-zero is inferred from the frame condition and a Bessel identity with a non-zero constant; confirming it is part of the frame reading in flight.
- **Premise.** Hosts on windows are an input to this construction, supplied from the cohomological bound.

This corrects the picture in section 12: the Galois representations built from theta lifts serve the cohomological bound, not the existence of the forms in the slope argument.

## 15. The frame, and the lattice of periods

From `slices/frame-and-glue.md`. I verified the statement `InputSG` (`Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean:30`); the rest is the slice's reading.

**The frame.**
- **The map.** B_u sends a form of archimedean type u, ramified at the level prime, to a functional on the target: its value at a point is the period of the form's m-fold lift against a test vector lying over that point. Up to unitary changes of basis and a non-zero scalar, B_u is a compression of a Poincaré-series map P_u from all forms of type u into one space of dimension about D*.
- **The hypothesis** (`InputSG`), for the Gram operators K_uu′ of the normalised P_u: off the diagonal ‖K_uu′‖² ≤ (1 + η₀)·d_u·d_u′/D*; on the diagonal ‖K_uu − 1‖² ≤ e₀·d_u; and the common space has dimension at most (1 + η₁)·D*.
- **What it means.** Each P_u is nearly an isometry, and different P_u overlap no more than independent random subspaces of those dimensions would. That is a nearly tight frame, not a nearly orthonormal family, and tightness comes from there being many indices u (the dimensions add up to far more than D*). Turning this into the hypotheses of Theorem F is linear algebra.
- **What proves it: a relative trace formula for Bessel–Poincaré series** (the tree's "Theorem S"; from `slices/theorem-s.md`, where I verified the statements of the expansion and of Bessel uniqueness).
  - *Setting.* G = U(V) is an indefinite unitary group, of signature (k + r, r + 1) at each real place; H = U(W) is definite of rank k; the Bessel subgroup is N⋊H for an isotropic flag and a vector of norm −T(u). So the forms live on the definite group H, and the common space into which they are mapped is a space of forms on the indefinite group G, of one fixed discrete-series type at infinity. P_u sends a form on H of type π_u to the Poincaré series built from the Bessel function of that discrete series.
  - *Unfolding.* The inner product of two such series is a sum over integral double cosets of archimedean orbital integrals.
  - *Identity cosets* give exactly 1 on the diagonal (the identity orbital integral is a volume over the formal degree, and the normalisation cancels it) and 0 off it, by Schur orthogonality.
  - *Degenerate cosets* vanish off the diagonal by Schur's lemma, since distinct indices have distinct archimedean parameters. On the diagonal they decay like (C/k)^(j(k − 1 − j)f) in the corank j, summing to exp(−k·f·log k). That decay needs archimedean Bessel uniqueness in a large-gap range: Bessel maps from a discrete series of U(p, q) into π_u span a space of dimension at most one.
  - *The remaining cosets* are bounded by a second-moment expansion over pairs of cosets sharing a row. The scalar generic pairs give the main term d_u·d_u′/D*; everything else is exponentially small in k. The main term is a product of an archimedean Plancherel bound, a count of generic frames, and volume identities.
  - *Siegel–Weil* is used in the convergent range and only as a mass formula: the integral of a theta series of frames with a given Gram matrix equals the product of local densities. The tree proves Siegel–Weil; that proof was not read.
  - *What drives the decay* is the weight k. The level prime has no decay rate of its own.
  - *Standard or new* (*inferred by the slice*): every ingredient is standard. What looks new is the uniformity over the whole family of archimedean types at once, with each off-diagonal block within a factor 1 + b⁻⁶ of the random-subspace value.
  - *Non-zero.* Every P_u is non-zero, since a zero map would violate the diagonal bound. Nothing asserts that each individual compressed block is non-zero, and a zero block would be tolerated by the height bounds, not excluded. No degenerate instantiation was found on the used path.
  - *Not read:* the proofs of Bessel uniqueness and of the tail bounds, the unfolding, the lattice count, and who builds the record identifying the concrete Poincaré setting with the abstract one.
- **The numbers.** The defects are exponentially small in a power of x, except one that is a polynomial budget x^(−CH). The tree proves that the frame's total cost in Theorem F is at most about 6b, with b = exp(x^ε), provided the range HH is at most x^(CH)·b.

**The lattice of periods.**
- **What it is.** A lattice R glued prime by prime from images, under the m-step lift, of integral forms of each local type; the periods land in its dual. There are m auxiliary lattices M_j, one for each step of the lift.
- **The determinant identity** is not a seesaw. On each Hecke piece the m-step lift composed with its adjoint is the scalar κ·∏_j λ_j, and each single step composed with its adjoint is λ_j; the pieces have matching dimensions, so the determinants multiply.
- **Where m·log(a!) and Ω^a come from.** Not from the divisor inequality. Each lift step has a budget for the size of its kernel of the form Σ(ν·log ν − ν) − (Σν)·log Ω; the step's eigenvalue is subtracted, and the covolume of M_j cancels part of the log Ω term. The slice's reading is that m·(a·log a − a − a·log Ω) is what survives; the cancellation itself was not read. The −a·log T comes from the last period map.
- **Passing between two level structures.** The bound is proved for a "base" lattice and moved to the lattice whose dual is Theorem F's target by a statement about one lattice stable under a finite group and the idempotents of two level structures, needing near-constant multiplicities at one level and multiplicity one at the other.
- **Where the cohomological bound is spent** (corrected by the main-term reading, section 16). In one place: it bounds the discriminant index of the Hermitian form on the lattices of the lift levels at the twisted primes.

## 16. The main term: a ledger that closes exactly

From `slices/main-term.md`. I verified the identity `key_identity5` (`Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:105`), the theorem assembling the single-step scalars (`scal_of_aForm_bForm`), the inputs of the eigenvalue lower bound, and the one consumer of the cohomological bound (`inEta_num`).

**The ledger, for each lift step j and each CM place.**
- *Cost of the kernel of the step:* Σ(ν·log ν − ν) − (Σν)·log Ω. The ν·log ν − ν is log ν! up to lower order, and comes from a Cauchy estimate in the Fock (Gaussian) norm: a polynomial of degree ν has norm about ν!.
- *Repaid by the step's eigenvalue:* all of that sum except the term at the top places, a·log a − a.
- *Repaid by the covolume of the auxiliary lattice M_j:* the remaining log Ω terms except a·log Ω.
- *The last map:* −a·log T.

What survives is Σ_t [ m·(a_t·log a_t − a_t − a_t·log Ω) − a_t·log T ]. The line-by-line algebra is the slice's own working from the hypotheses of the packaged inequality; the proof body of that inequality was not read.

**Ω.** Ω at a place is the area of the conjugate CM lattice of unit discriminant over π times a squared norm; the mean of log Ω over conjugates is the Chowla–Selberg value (section 11).

**The single-step identities.** The step composed with its adjoint is a scalar λ_j, and the m-step lift composed with its adjoint is κ·∏λ_j. They come from the Siegel–Weil formula, the doubling method and unramified Howe duality. The L-values involved are partial L-functions at (1 + t)/2, in the region where the Euler product converges; no central value is computed. The height needs only a lower bound, log λ_j ≥ Σ log(hook products) less a small term, and interlacing of the weights cancels every factorial except the one for the long row.

**The lattice side equals the analytic side identically.** `key_identity5` states: (the divisor sum) − (Σa)·(the count's lower bound for log T) + m·(Σa)·log(g₀g₁) = MAIN + (Σa)·c·(La + m²·La/k). The log(π/v) from Ω cancels the log(v/π) in the count; the term in g₀g₁ cancels a comparison term; the heights' κ cancels. There is no discrepancy: what remains besides MAIN is the stated error, with its m²/k.

**How the cohomological bound is used: a correction.** The frame reading (section 15) said it was the premise of two statements. On the used routes, both of those take it as an argument and never use it. Its content is unfolded in exactly one place (`inEta_num`, `Formalism/LocalToGlobal/Divisibility/SumLeEtaSumNum.lean:60`): it bounds the length of a quotient of the lattice of lift level j, which bounds the discriminant index of the Hermitian form on that lattice at the twisted primes. The link from Galois cohomology runs through congruence ideals of a Hecke-type algebra, bounded by Sha lengths, in the manner of Ribet's argument. The cocycle argument behind that bound was not read.

Not read: the Fock-norm estimate's proof, the covolume chain for M_j, the cocycle argument, and the body of the packaged divisor inequality.

## 17. From Sha lengths to an index of lattices of forms

From `slices/congruence-sha.md`. I verified in the source that `divinN_of_hypV` weakens √b to b (`hle.trans (Real.sqrt_le_self_iff.2 …)`) and that the bounding theorem's namespace exists where cited.

- **What is bounded.** For lift level j, T_j is the orthogonal projection of the lattice of that level onto a Hecke-stable subspace Z inside its theta-lift block, and cut_j is the lattice's intersection with Z. T_j/cut_j is a congruence module, and the discriminant index of the Hermitian form on T_j is bounded by it. Z is the set of eigensystems whose parameter contains a Speh block of length t, that is, the theta lifts.
- **The bound.** At a prime ℓ, the valuation of the congruence ideal between an eigensystem in Z and those outside is at most: the length of a Selmer group of a twist of its Galois representation, plus Σ_{0 < e < t} of the Sha lengths over the host field, plus v_ℓ of the class number, plus ramification terms at auxiliary places.
- **How it is proved.** A determinant (Fitting-ideal) form of Ribet's lemma in the algebra spanned over the Hecke algebra by Galois images. At each eigensystem outside Z the line of the distinguished character is not Galois-stable, which bounds the congruence ideal by modules of cocycles. Cocycles for the trivial twist are unramified everywhere and are bounded by the class number through Artin reciprocity. Cocycles for the twists ε^(−e), e ≥ 1, are unramified outside ℓ and coboundaries above ℓ, so they land in the Sha groups.
- **Why e runs from 1 to t − 1.** The Galois side of the Speh block is the t characters χ₁, χ₁ε⁻¹, …, χ₁ε^(−(t−1)); t is the rank each lift adds.
- **Galois representations are needed here, for every eigensystem**, of dimension k + m − 1. They come through a field resting on two literature rows; whether the theta-lift theorem fills them on this path was not traced.
- **The bound needed is far weaker than the bound proved.** `HypV` gives the Sha sum ≤ √b with b = exp(x^ε), and the consumer immediately weakens it to ≤ b. The slot it must fit is about f·m·b·x^(2ε). The cohomological theorem delivers about exp(x^(4ε/5)). So what the slope argument needs from "a weakening of Vandiver" is that the total Sha length is at most exp(x^ε): finite and sub-exponential in a small power of x.
- **Arguments passed and unused.** Two hypotheses are discarded by the determinant lemma, their content entering through idempotent data built upstream. One link (`LinkEta`) is discarded on the used route, so nothing there forces the local Hecke data to be non-empty; the slice judges this harmless because two ties force non-empty data wherever the congruence module is non-zero, but did not read who proves those ties.

## 18. The core of the cohomological bound

From `slices/vwin-core.md`. I verified the statements of the congruence number (`CongruenceNumberRankThree`) and of the commutative-algebra lemma (`LemmaM`), and that Kato's unramified zeta statement is assembled in the tree.

- **The one integer.** NN is the product, over every cuspidal eigensystem of the relevant weight and level and over a Galois orbit of character values, of q^e·(t_s − eis), where t_s is the Hecke trace at a Frobenius and eis = q^(−e)z + 1 + q^e·z⁻¹ is the trace of the reducible representation Ψ ⊕ 1 ⊕ Ψ⁻¹ there. It is an integer because the factors are permuted by the automorphisms of ℂ. It is non-zero because a Jacquet–Shalika bound gives |t_s| ≤ √q + 2 while eis has a term of size q^e ≥ 7. Its logarithm is polynomial because the number of eigensystems is polynomial in the level and weight. It is a congruence number between cusp forms and an Eisenstein class.
- **Why Sha is bounded by valuations of NN.** A commutative-algebra lemma about the universal deformation ring of Ψ ⊕ 1 ⊕ Ψ⁻¹, graded by the torus: the length of the weight −1 part of the cotangent space is at most 2·Σ v(a) over the non-triangular points, with a = tr r(σ) − tr r₀(σ). The Selmer group sits inside that weight −1 part. It needs the weight-zero part finite, every non-triangular point automorphic, and every point rigid. This is the residually reducible pattern in which an Eisenstein congruence bounds a Selmer group; it is not an Euler-system bound.
- **Where automorphy comes from.** Hida families on U(3), propagated from seed points that are adjoint lifts of GL₂ forms congruent to Eisenstein series; endoscopic points come from newforms. For the GSp4 cases, a potential-modularity tower.
- **What Kato's Euler system contributes.** Only rigidity at the endoscopic points, through vanishing of two Bloch–Kato Selmer groups. The Euler system is built in the tree.
- **In the tree as well:** the crude bound on exceptional twists by a Soulé-type argument in the homology of GL_N of the integers, finished with Poitou–Tate; Borel's rank bound reproved by integrating invariant forms over cycles; Ferrero–Washington from Stickelberger, Sinnott and reflection.
- **What the bound rests on.** Not the main conjecture of Iwasawa theory: nothing by that name is on the path, and the minus part comes from an Euler system of Gauss sums. It does rest on automorphy lifting in every case, on Galois representations for U(3) and GSp4, on Kato's Euler system for one rigidity statement, and on K-theory of rings of integers for the exceptional twists. Fourteen of the fifteen literature hypotheses of this part are consumed; one is never read. Two attributions (Hida theory, Rubin's argument) are inferred from names, not proof bodies.

## 19. Landau on windows, and the supply of hosts

From `slices/landau-hosts.md`. I verified that the mean-square theorem and the zero-density statement are proved where cited.

**Landau on windows.**
- The theorem holds for every level and every λ > 1; the exponent 3/2 is chosen by the supply.
- **Method.** Take the Laplace transform of G(e^u) and its k-th Taylor coefficient at a real point σ. That coefficient is an integral of G against a Gamma kernel, and with k ≈ (1 + δ/2)·σ·log Y the kernel sits inside the window. A one-sided bound suffices because |g| + g = 2·max(g, 0).
- **The zeros.** If the zero nearest to σ is real, its residue is positive and makes the coefficients grow. Otherwise the argument moves to σ + iγ, nearer to that zero than any zero is to σ. Either way the window bound is contradicted.
- **Why λ > 1.** The only a priori bound is |G(y)| ≤ C·y², so the window must have logarithmic length proportional to log Y; then σ ≈ 36/δ², which is 336 at λ = 3/2.
- **Inputs.** No zero-free region and no zero-density estimate; only non-vanishing on Re s ≥ 1 from Mathlib. Positivity of the Dirichlet coefficients is not what is used; positivity of the weights is, through the sign of a residue.

**The supply of hosts.**
- **The auxiliary characters are bounded only as a family.** Over primes q ≡ 3 mod 8 of the right size, then primes d ≡ 7 mod 16 with a divisibility condition, all but a share are good. That rests on a mean square over prime moduli and a zero-density count (at most C·Q^(1/4) characters with a zero near Re s = 1 − 1/400), both proved in the tree.
- **The mean square is not a large sieve.** It is orthogonality of quadratic characters over prime moduli, with reciprocity and the prime number theorem in progressions, one exceptional modulus dropped, and Siegel's bound and Landau–Page.
- **Order of the argument.** Each character is handled alone. The only assumption about it is its cohomological bound; nothing about its zeros is assumed, and there is no induction on conductor, order or scale.
- **Why windows, and why 3/2.** The windows come from the cohomological bound, which holds only on [W, W²]. The exponent 3/2 absorbs a constant factor, and the same absorption is why the cohomological bound is stated with exponent 401.
- **Dead statements nearby** include a classical all-large-x Landau theorem and several host conditions that are never used. Nothing degenerate was found.

## 20. An adversarial pass on four flags

From `slices/vacuity-flags.md`. I verified that the three named theorems exist with the stated shapes (the congruence-length identity, and the two converters from the theta-lift theorem). Verdicts are the slice's.

| Flag | Verdict |
|---|---|
| Is the index bounded by the Sha lengths the true one? | Excluded: it cannot be declared zero while the lattice length is non-zero |
| Is the abstract frame data the concrete Poincaré maps? | Excluded: equal by definition, up to linear isometries and a non-zero scalar |
| Could zero blocks of period maps empty the slope inequality? | Tolerated and harmless |
| Are the Galois-representation fields assumptions, and is partial compatibility enough? | Tolerated and harmless, one hop open |

- **The index.** On the path the record's η is defined as a sum of local terms, and a theorem proves that sum equals the lattice length. That proof needs every maximal ideal of the local Hecke algebra at a twisted place to be covered by a local index, so empty local data forces the lattice length there to be zero. The toy records with no local data exist only as a stage before localisation.
- **The frame.** The slot is built with the concrete setting substituted definitionally; the spaces, the maps and both volumes come from it. A zero map would contradict the diagonal clause of Theorem S.
- **Zero blocks.** Heights are fixed for every index by one formula, zero block or not, and the slope inequality is proved for zero maps too. From Theorem F's own hypotheses the rank share of zero blocks is at most (√e + √c)² with c = (1 + √e)·√((1 + η)δ), which with the tree's numbers is exponentially small in a power of x. That derivation is the slice's, not the tree's. A single zero block is not ruled out.
- **Galois representations.** Both fields are filled by the tree's theta-lift theorem through two converters, so neither is an assumption. The consumer uses only characteristic polynomials of Frobenius at split unramified places, which the partial compatibility gives exactly; the rest follows by Chebotarev. The open hop: an inertia condition at the auxiliary places, whose source was not traced to the tame case.

**The three hops that pass left open, settled** (`slices/open-hops.md`; verdicts are the slice's, not separately checked by me).
- *The lift-level lattices are the real ones.* The field is an integral structure defined by integrality of values: forms of the given level whose value at every class lies in the dual Weyl lattice. It is not defined as the image of a lift, and the ties that pin it are fields of the record types, so every record on the path satisfies them.
- *The localisation exists by definition.* The local index type is defined as the set of maximal ideals, so the covering condition returns each ideal's own index. What is proved is that there are finitely many, by commutative algebra: commuting, split Hecke operators on a finite-dimensional space have finitely many eigencharacters. No Galois representation indexes them.
- *The inertia condition stays within the partial compatibility.* The auxiliary places are designed for it: two primes totally split in the host field and larger than 16·n², with square-free local types, which is exactly the tame case the compatibility covers; at the remaining auxiliary places every inertia eigenvalue is a root of unity of order dividing N(w) − 1, which falls under the abelian case. One supplier's proof (`EigPd`) was not read.

With this the text reading has reached the literature rows on every branch it followed. What remains unread is the bodies of those rows, which the build checks and a text reading of this size cannot.
