# Audit of the one-page draft against the source, by the author

Operator direction, 2026-11-20: whoever writes the paper reads the source for each claim, and does not rest on a delegated reading. This note is that check for `one-page-statement-draft.md`. The rule from here on: a claim enters the paper only with a line in this table saying what I read.

Three levels are kept apart:

- **S**: I read the Lean *statement* (definition or theorem type) in the source.
- **P**: I read the *proof* body, or enough of it to see what it uses.
- **D**: delegated reading only (`slices/`); I have not read it.

Nothing here is a verification of the mathematics. That is the kernel's work, and the build is still running.

## Step by step

| Draft step | Claim | Level | What I read |
|---|---|---|---|
| top | `riemannHypothesis := rhOfAll`, and `rhOfAll := Formalism.VW.rh_of_every allChi` | P | `Main.lean:4`; `Supplements/Kernels/MainTheorems.lean:9` |
| top | The definite side enters as `Nonempty (HypsAlt …)`, with `Green` and `VWin`; the route is `forall_goal_of_shape_of_hyps … (shape_closed_link_n_of_green hG) trivial trivial h`, λ = 3/2, hosts from `supplyChi ψ (hV ψ)` | P | `…/ThirdPlaceSeries/TopPlug.lean:12-18`, whole file |
| top | The assembly: which record field feeds which link, and the final call to `topDesWin` | P | `…/ThirdPlaceSeries/TopShape.lean`, whole file (57 lines) |
| 1 | Landau on windows, statement: for 0 < θ < 1, δ > 0 and a constant C, a bound G_F(y) ≤ C·y^θ on some [Y, Y^(1+δ)] beyond every point gives non-vanishing for Re s > θ | S | `zeroFree_of_rpow_window`, `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean:11` |
| 1 | The definition of G: the prime sum with weight (y/n − 1)₊, less y·log y − (1 + γ)·y for the trivial character and plus y·L′/L(1, χ) otherwise; a family is a finite set of characters with positive weights | S | `ramp`, `Gchi`, `CharFamily`, `Gm`, `Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean:10-36` |
| 1 | Its method: the window hypothesis is passed to the u-variable; zeros with Re s ≥ 1 are excluded separately; the supporting lemmas are iterated derivatives of a Laplace transform under the a-priori bound C·e^(2u), a kernel integral, a dichotomy and a nearest-zero lemma, and a growth contradiction | P | `lemmaL`, same directory, `lemmaL.lean:13-23`, and the statements of `IteratedDerivLaplace.lean:84`, `LandauDichotomy.lean:24`, `LandauNearest.lean:36`, `kernelIntegral.lean:9`, `LandauGrowthContra.lean:9` |
| 2 | The identity `AskMainBalance`; ASK and MAIN | S | `Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean` (second reading) |
| 3 | Thick and thin weights; four characters survive; the bound `G(x) ≤ 4x^(1/2+ε) + …` | S | `…/GrowthBoundGivesRiemannHypothesis.lean` (second reading) |
| 3 | The sizes: m ≈ √x, the three costs x/m, m, k/n² | S | `SizeWindows`, `GrowthSizeBound`, same file |
| 3 | Hosts from the cohomological bound: `VWinAt ψ 401 → HostExW (3/2) (GChi ψ).req` | S | `…/CharacterBoxes/SupplyChi.lean:8` |
| 3 | Auxiliary characters bounded as a family by a mean square and a zero-density count | S for the two theorems' statements; D for how they combine | `meanSqK.lean:51`, `CountZAll.lean:13`; `slices/hosts.md`, `landau-hosts.md` |
| 4 | N_u is the unscaled lattice times ∏ 𝔓_w^(−⌊ur(sg)⌋) | S | `Iu`, `NprimeDef`, `Formalism/LocalRingCardinality/DataDIVDefs.lean:17-24` |
| 4 | Periods of the unscaled lattice are divisible to that order | S | `adm2`, `Formalism/SharpRestriction/Divisibility/LocalQuadraticParts.lean:206` |
| 4 | That divisibility is proved by `admissible_level_two` and rests on the jet theorems | S for the theorem's statement and for `split_bound_eleven_one` calling `thmA_of`, `thmOne_of`; D for the chain between | `AdmissibleAtGeneratorPlaces.lean:214`; `LocalBoundElevenComparison.lean:64`; `slices/divisibility-trace.md` |
| 4 | Gain against count: `ASK − Ga ≤ LoP` for every translate | S | `LossBounds`, `Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean:34` |
| 4 | Gains raise the slope: `μ_M + Ga + Fo − Ee − Lo5 ≤ μ_N` | S | `QuotientSlopeBoundsWith`, same file :19 |
| 4 | The record the final theorem requires is `SizeData₂` with eleven clauses | S | `Formalism/SizeWindowBrackets/SChain.lean:17` |
| 4 | Theorem F, statement | S | `Formalism/HarderNarasimhan/StatementFrameF.lean` |
| 4 | Theorem F, proof: Harder–Narasimhan steps of each source and of the target, a Markov bound on the rank cut away, the μ_min form of the slope inequality, the frame lemma applied with ε = u/(u + τ), and a layer-cake integral over τ | P | `theoremFSharp_of`, `Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean:168-390` (skeleton: `hnStep` at 218 and 278, `slope_inequality_mean` at 292, `thmF_place` at 311, `layer_cake_formula` at 374); `frameB_share`, `FrameHermSharpB.lean:25` |
| 4 | The frame hypothesis `InputSG` | S | `Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean:30` |
| 4 | It is proved by a relative trace formula for Bessel–Poincaré series | S for Bessel uniqueness and the expansion's statement; D for the proof | `UniqGap`, `KExpansion`; `slices/theorem-s.md` |
| 4 | The divisor clause: `μ_CC + h − Fo ≤ Σ_t(m(ph(a_t) − a_t·logOm) − a_t·log T) + errors` | S | `DIV`, `Formalism/RankGapBounds/MeanBoundSecondForm.lean:118` |
| 4 | The count for T: `Σ_j mean log(w·v/π) + m·lg − c(La + m²La/k) ≤ log T` | S | `Count5`, `QuotientSlopeBoundsWith.lean:27` |
| 4 | Lattice side equals MAIN identically | S | `key_identity5`, `…/ChainSlopeWindows/LevelOfCongruence.lean:105` |
| 4 | Chowla–Selberg: mean log(4π·Im τ·|η|⁴) = γ + log(2π/√d) − L′/L(1, χ) | S | `chowla_selberg_eta`, `…/DedekindZetaEqSumRealEisenstein.lean:222` |
| 4 | The ledger over lift steps: for each step j and place ρ, (covolume term) + (kernel term) − (eigenvalue term) is at most ph(a_ρ) − a_ρ·logOm at the top places plus errors; summing over the m steps gives m·Σ_t(ph(a_t) − a_t·logOm) − Σ_t a_t·log T | P | `divisor_inequality_assembly`, `Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DivAssembly.lean:11-46`, whole proof |
| 4 | The gain is a closed formula: zero at excluded primes; on served orbits the larger of γ_p·Σ_s a_s − Σ_s Σ_{e odd} min(a_s/p^e, capacity) − corrections and a non-negative term; on the other orbits a non-negative term | S | `gU`, `gainP`, `Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean:165-228`; `sg`, `Ga`, `logOm`, `Formalism/LocalRingCardinality/DataParams₂.lean:212-224` |
| 4 | **Missing from the draft until this audit:** the covolume of the auxiliary lattices is proved by arithmetic intersection theory | S | `topCovolSlim2_use_alt_alt`, `…/ThirdPlaceSeries/TopCovolSlim2Use.lean:16` (see below) |
| 4 | The auxiliary lattices are lattices of integral forms on a moduli space, integrality meaning non-negative valuation at every point over every finite place | S | `cuspA`, `PtM`, `nrmM_le_one_iff`, `Formalism/LocalToGlobal/ProjectiveLattices/CuspidalL2Subspace.lean:47-60` |
| 4 | The covolume clause: `lcv(XW_j, M_j)/D ≤ l3_j` for every lift step | S | `L3`, `Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean:315` |
| 4 | It is obtained as a chain of slope comparisons with eight named inputs, ending in `mainT + C·unitE` | S | `lcv_le`, `Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFromGramAndBounds.lean:39`; the eight inputs at `Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean:53-96` |
| 4 | The chain itself: covolume ≤ −slope(good sublattice) (`RecAt`); the good part is cut out by an orthogonal idempotent and the bad part has rank share at most 3·exp(−x^(ez/7)) (`CutAt`, `BadAt`); slope(type lattice) ≥ a core slope − C·unitE (`CoreAt`); the core slope ≥ −mainT − C·unitE (`LowAt`) | S | same file |
| 4 | Where the period enters the covolume: mainT is within C·unitE of Σ_τ (p − q)·anchor_τ·logOm | S | `AnchorAt`, same file :98 |
| 4 | That `CoreAt` and `LowAt` are the statements proved by the arithmetic-geometry inputs | D | `slices/five-proofs.md` |
| 4 | The cohomological bound is consumed in one place | P | my own search: `DIVinN_at` occurs in five files and is unfolded only at its producer and in `inEta_num` (`SumLeEtaSumNum.lean:71`) |
| 4 | `LinkN_at`, `DIVinN_at`, `etaSum` | S | `Formalism/SharpRestriction/GlobalTheoremInputs.lean:31-63` |
| 4 | The consumer drops the square root (√b to b) | P | `divinN_of_hypV`, `…/CharacterBoxes/DivinNOfHypV.lean:117-131` |
| 4 | The Sha lengths in the record are the true ones | P | `vvRecord`, same file :17-55: the field equals `GaloisCohomology.shaLen` of the host field by `D.nd.sha_eq` |
| 5 | The height-two logarithm; `CM2`; `CM3` | S | `Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean:35-55` |
| 5 | The radius lemma and the rate γ = ℓ/(ℓ² − 1) | S | `LemmaRA`, `Formalism/GaussJetBounds/StatementG.lean:12` |
| 5 | The jet theorem is applied to an arbitrary series with the integrality hypothesis | P | `prvF_of_orbitLetterBounds`, whole proof (61-line file) |
| 5 | The kernel is an integral combination of torsion translates; a period is a polynomial in jets | D | `slices/jet-bridge.md` |
| 6 (i) | `VWin`, `VVle`, the Sha groups as locally trivial classes | S | `ExistsPageN.lean:12`; third reading, sections 1-2 |
| 6 (i) | The one integer: `NumberU3U_s` / `CongruenceNumberRankThree` | S | `NumberU3US.lean:30`; `CongruenceNumberRankThree.lean:125` |
| 6 (i) | Its construction as a product of (trace − Eisenstein trace), and why it is non-zero | D | `slices/vwin-core.md` |
| 6 (i) | The deformation-ring lemma | S | `LemmaM`, `…/CommutativeAlgebra/OrbitVanishingLocal.lean:111` |
| 6 (ii) | `HostExW` | S | third reading |
| 6 (iii) | The space of forms is all algebraic modular forms | S | `Fi`, `…/AutomorphicMembership/PredMemGamRanks.lean:151` |
| 6 (iii) | The level prime in a short window | S | `LevelPrime`, `…/GlobalTwisting/LogCondLeThree.lean:81` |
| 6 (iii) | The class number formula: the number of classes equals a mass times an index times (T^k − 1)^f | S | `ClassNumberFormula₂`, `Formalism/SharpRestriction/GlobalSchurBounds/StandardLattice.lean:453` |
| 6 (ii) | The host field: a subfield of a cyclotomic field fixed exactly by the a with a ≡ ±1 mod 2^(e+2), ψ(a) = 1, (a/q) = 1, (a/d) = 1 | S | `IsChiField`, `Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:19`; `KerChi`, `…/TwistForm.lean:9` |

## What the audit changed

1. **Arithmetic geometry is an input to the slope argument, and the draft did not say so.** The draft's period side said the kernel cost of each lift step is "repaid by the covolume of an auxiliary lattice". I read the theorem that supplies that covolume bound. Its hypotheses are: resolution of singularities and principalisation in characteristic zero, a Poincaré–Lelong statement, an arithmetic Hilbert–Samuel statement, Moriwaki's bigness, a statement of Fargues, Zarhin's trick, Riemann–Roch for nef bundles, toroidal compactifications (two statements), semi-negativity of the Lie algebra of a semi-abelian scheme, a point-separation statement, an arithmetic-degree statement, a bundle of theorems on the Hodge bundle, and Grothendieck's deformation theory. Inside, it uses a Chow-form height comparison and a Fubini–Study formula for Chow heights. The delegated reading says the auxiliary lattice is a lattice of integral forms on a moduli space attached to the indefinite unitary group, and that the bound is a chain of Arakelov slope estimates; that description I have not read myself. This is why resolution of singularities and Kawamata–Viehweg-type statements sit among the literature rows. The draft is corrected.
2. **`HypsAlt`, not `Hyps`.** My first reading named the wrong record. The top theorem's type says `HypsAlt`.
3. **The Sha field is not free.** The record carries Sha lengths as a field, which could have been a hole. I read the lemma that converts the true bound into the record's: the field is equal to the true Sha length of the host field by a tie in the base data.

## What is still delegated in the draft

Marked D above: the method of Landau on windows; the chain from the jet theorems to the period divisibility; most of the proof of Theorem F; the trace formula's proof; the main-term ledger; the bridge from the kernel to jets; the construction of the congruence number; the class number formula. Each is to be read by me before it is stated in a paper as more than "the tree's proof is reported to go as follows".
