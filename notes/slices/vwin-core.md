# The core of `VWin`: the integer NN, the deformation-ring bound, LemmaK

Read 2026-11-20 from the source text only; nothing was built. Tags: **read** = transcribed from source; **proved-by** = the proving declaration was located and its body read at the depth stated; *inferred* = my interpretation. Path prefixes: `AA/` = `src/Development/AutomorphicArithmetic/`, `AV/` = `AA/AutomorphicVarieties/`, `DT/` = `AV/ModularityArgument/ThresholdArguments/DenseThresholdCases/`, `AR/` = `AA/Foundations/GaloisRepresentations/AdmissibleResidues/`, `U3/` = `AV/UnitaryThreeGroups/`. The Lean is condensed.

## Direct answers

1. *inferred* NN is an Eisenstein congruence number at a single Hecke operator. *inferred* It is the product, over every cuspidal eigensystem of the given weight and level and over a Galois orbit of character values, of q^e·(t_s − eis3), where eis3 is the trace of Ψ ⊕ 1 ⊕ Ψ⁻¹ at Frob_w⁻¹. **read** The source names the statement `CongruenceNumberRankThree`.
2. *inferred* It is an integer because Aut(ℂ) permutes its factors. *inferred* It is non-zero because of the Jacquet–Shalika bound: |t_s| ≤ √q + 2, while |eis3| ≥ q^e − 2. *inferred* Its logarithm is polynomial because cuspidal representations are counted by a cohomology dimension. *inferred* No Bernoulli number, regulator or Ramanujan bound enters.
3. *inferred* The length bound is commutative algebra on the universal deformation ring R of Ψ ⊕ 1 ⊕ Ψ⁻¹, graded by the torus diag(t, 1, t⁻¹): the weight −1 cotangent length, which bounds the ψ-Selmer group, is at most 2·Σ v(trace difference) over the non-triangular points. *inferred* It requires R⁰ finite over O and all those points automorphic and rigid, which is the residually reducible "R = T bounds Selmer by an Eisenstein congruence" pattern; it is neither an Euler-system bound nor a lattice construction of classes.
4. *inferred* The points are automorphic by Hida families on U(3), propagated from seed points that are adjoint lifts of GL₂ forms congruent to Eisenstein series. *inferred* Their Galois representations come from `RowT`, the theta-lift construction.
5. *inferred* Kato's Euler system, which is built in the tree, only makes the endoscopic points W ⊕ 1 rigid.
6. **proved-by** LemmaK, BOdd and Ferrero–Washington are all proved in the tree. *inferred* LemmaK is a Soulé-type argument in the homology of GL_N(O_L): BOdd uses invariant differential forms, and the torsion bound uses a complex with finitely many orbits. *inferred* FW goes through Stickelberger's theorem and Sinnott's theorem.
7. *inferred* Of the 15 fields of `HypothesesH'`, 14 are consumed on this path and `quat` is never read; all 15 are built from in-tree terms.

## 1. `NumberU3U_s`: how NN is built

**read** The statement (`DT/NumberU3US.lean:30-48`) applies to K imaginary quadratic and gives ∃ c A such that, for every e ≥ 1, N ≥ 1, prime p ≥ 7 with p ∤ N and p ∤ disc K, w | p, and every finite `Orb` with roots of unity z : Orb → ℂ permuted by Aut(ℂ):

    ∃ NN : ℤ, NN ≠ 0 ∧ log|NN| ≤ c·#Orb·(N(e+1))^A·log p ∧ ∀ l ≠ 2, p, ∀ X : Orb → Finset ρ
      (each ρ `Adm3U_s ι e N` ∨ `Adm2A ι e (N·|disc K|)`, pairwise non-isomorphic; σ a Frobenius at w),
      (∀ o ρ, tr ρ(σ⁻¹) ≠ ι⁻¹ eis3(Nw, e, z o)) ∧ ‖NN‖_l ≤ ∏_o ∏_{ρ∈X o} ‖tr ρ(σ⁻¹) − ι⁻¹ eis3(Nw, e, z o)‖_l

**read** `eis3 q e z := q^{-e}·z + 1 + q^e·z⁻¹` (`AV/AutomorphicForms/CongruenceNumberRankThree.lean:121`). **read** `Adm3U_s` requires ρ irreducible, with `tw ρ χ_cyc⁻¹` attached to a conjugate-self-dual cuspidal representation, of level N and weights (e, 0, −e), plus `Unl` (`DT/NumberU3US.lean:27-29`, `DT/AfStmt.lean:29-32`). **read** `Adm2A` requires ρ ≅ W|G_K ⊕ 1, with W irreducible and attached to a newform of weight 2e+1 (`AV/ModularityArgument/AutomorphyLifting/AutomorphyDescent/AutNewformW.lean:14-21`). **read** `Adm2B` is defined as `Adm2A` (`:23-24`), so the hypothesis "Adm2A → Adm2B" is an identity.

**proved-by** `numberU3U_of_prints : Hypotheses' → NumberU3U_s` (`DT/KeepNumU.lean:79`) runs through `numberU3U_of_adm2A_imp_adm2B` (`:25-78`), which uses all six of its arguments. The sketch:

1. **read** Two finite trace data are built (`DT/FrobeniusTraceCountBoundOfCmEigensystemCount.lean:418, 348`). **read** D₁ comes from `CountKAlt`: the Satake multisets at w of cuspidal, regular algebraic, conjugate-self-dual π on GL₃(𝔸_K) of weight (e−1, −1, −e−1) and level N. **read** D₂ comes from `CountQAlt`: the Satake pairs at p of weight-(2e+1) newforms of level N·|disc K|. **read** `TrData q e` is a finite S with t : S → ℂ, stable under Aut(ℂ), with ‖t s‖ ≤ √q + 2 and q^e·t s integral (`AR/WinDefs.lean:70-77`). **read** The values are t_s = Σ_b (q b)⁻¹ for D₁ (`traces_from_eigenvalues_rank3`, `AR/FrobeniusTraceCountBoundOfRatEigensystemCount.lean:78`) and t_s = 1 + Σ_b b^{−h}, with p^h = Nw, for D₂ (`:169`).
2. **read** `NN := ∏_{(o,s)} q^e·(D.t s − eis3 q e (z o))` (`:335`). **read** It is an integer by `exists_int_eq_prod_of_galois_permuted_integral` (`:345`; `AV/BuildingsResidueChars/ExistsIntEqProdOfGaloisPermutedIntegral.lean:5`).
3. **read** `eisenstein_trace_difference_log_bound` (`:237`): for q ≥ 7, e ≥ 1, ‖t‖ ≤ √q + 2 and z a root of unity, t ≠ eis3 and log‖q^e(t − eis3)‖ ≤ 2e·log q + 1. **read** Its proof: if t = eis3, then q^e = ‖q^e z⁻¹‖ ≤ ‖t‖ + q^{−e} + 1 < 7. **read** The bound on ‖t‖ is `Win`: every normalised Satake parameter b satisfies q^{−1/2} < |b| < q^{1/2}, with unit product (`AR/SumThree.lean:7-10`). **proved-by** `win_algSat` (`AR/WinSat.lean:47`) proves `Win` from `PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound`, an in-tree theorem (`Development/WeilBound/CoreStatements/PublishedTheorems/JacquetShalikaBound/JacquetShalikaBound.lean:77`). *inferred* So the non-vanishing is the Jacquet–Shalika bound, not Ramanujan: the Eisenstein trace has a term of size q^e ≥ q.
4. **read** Hence log|NN| ≤ #Orb·#S·(2e·log q + 1) (`:329`). **proved-by** The bound #S ≤ c·(N(e+1))^A is `card_k_of_printed_results` (`DT/TCardK.lean:18`). **read** It multiplies three bounds: `P.borelC` (the number of cuspidal π is at most a cohomology dimension), `cohBoundFree` (that dimension is ≤ c·M^A·d at level 3M; `AV/AutomorphicForms/TemperedLocalComponents/CohBoundFree.lean:93`), and the Weyl dimension d ≤ c·(H+1)^A. **read** It also uses `P.cohC`. *inferred* That is Clozel's statement that regular algebraic cuspidal representations are cohomological. **proved-by** D₂ is counted by `countQ_alt`, which runs `countP` over n² + 2 imaginary quadratic fields and then extracts roots (`rootSum`).
5. **read** The ℓ-adic clause uses `Classifies` (`AR/WinDefs.lean:87-90`): a class map ρ ↦ s that separates non-isomorphic ρ and satisfies tr ρ(σ⁻¹) = ι⁻¹ t_s. **read** Its inputs are `LevelKNAlt` (an admissible ρ comes from some π in the counted set, with Frobenius eigenvalues equal to Satake parameters; `DT/AutQN.lean:51`) and `iso_of_frobenius_of_printed_results`. **read** Every factor is an algebraic integer, so `adicNorm_prod_le_prod_of_injective_classes` (`AV/BuildingsResidueChars/AdicNormProdLeProdOfInjectiveClasses.lean:5`) bounds ‖NN‖_ℓ by the product over X.

**read** In `PropGK`, Orb is the set of Dirichlet characters mod N with kernel H, z χ = χ(Nw)⁻¹, and #Orb ≤ φ([(ℤ/N)^× : H]) (`DT/FPropGKU.lean:110-173`). **proved-by** The GSp4 statement `NumberSp4Alt` (`DT/AfStmt.lean:34-43`) is proved the same way by `number_sp4_of_admissible_to_admissible_n` (`DT/VWinNumN.lean:94`). **read** There the factors are (sum of four Satake parameters) − eis4, with eis4 = p^{e+1}z₁ + p^e z₂ + p z₃ + 1, taken over the twists by (ℤ/k)^×. **read** They are non-zero because ‖t‖ ≤ (7/2)·p^e while the p^{e+1} term dominates (`est`, `:35`).

## 2. From NN to the ψ-part of Sha

**proved-by** `propGK_of_numberU3U_of_oneCharU` (`DT/FPropGKU.lean:110`) applies `OneCharU_s` to each ψ in the orbit, with σ⁻¹ and t = eis3(Nw, e, ψ(Nw)⁻¹). **read** The hypothesis "tr ≠ t" is taken from NumberU3U_s applied to singletons. **read** This yields Vn ψ ≤ 2·Σ_{ρ∈X_ψ} v_ℓ(tr ρ − t), and `vl_bound` turns the sum over ψ into Σ_ψ Vn ψ ≤ 2·v_ℓ(NN) for every ℓ ≠ 2, p.

**proved-by** `oneCharU_of_katoTwoW_rig_admI_automorphy` (`DT/FOneCharU.lean:75`, body `oneChar_unramU` at `:19-73`) uses all nine of its arguments:
- **read** `AutomorphyUnramifiedCoefficientsAlt` gives g₁, finiteness, automorphy of type-I points and modularity of type-II points (`:33`);
- **read** `exists_ring` and `exists_model` give the universal ring S.R of 3-dimensional lifts of r0 = Ψ ⊕ 1 ⊕ Ψ⁻¹ (with polarisation η and local conditions) and a graded presentation M;
- **read** each non-triangular point yields an `Adm3U_s` or `Adm2A` representation (`hadm`, `:48-53`);
- **read** the bound is `model_upper` (`:55`) followed by `vlen_le` (`:58`).

**read** `model_upper` (`U3/ModelUpper.lean:103-111`):

    l ≠ 2 → Marks η Ψ cc g₁ → LemmaM → Module.Finite O (weightZeroSubalgebra O S.r.hom) → PtHyp η S.r.hom M.x₀ →
    ∀ σ, η σ = 1 → (∀ f, TwoPt η S.r.hom f → trDiff η Ψ S.r.hom σ f ≠ 0) →
    M.len ≠ ⊤ ∧ ∃ T, CoversPt η S.r.hom T ∧ (one f per torus orbit) ∧ nrm M.len ≤ 2·Σ_{f∈T} v_ℓ(trDiff σ f)

**read** `TwoPt f` means f is a point and push f r is neither upper nor lower triangular (`U3/ConjStable.lean:94`). **read** trDiff σ f = f(tr r(σ)) − tr r0(σ) (`:101`). **read** `M.len` is the length of the weight −1 part of the cotangent space at the base point (`:89`). **proved-by** The body derives M1–M5 from finiteness and `PtHyp` (`U3/ModelUpper.lean:117-149`), puts a := tr r(σ) − tr r0(σ) in weight 0, and applies `LemmaM` (`:159`).

**read** `LemmaM` (`AV/CommutativeAlgebra/OrbitVanishingLocal.lean:111-118`) is about a ℤ-graded O-algebra with weights in {−2, …, 2}, a complete local weight-zero part, a point x, and equations Q that satisfy:
- **read** M1: a smooth chart, with Q spanning the cotangent pieces;
- **read** M2: the weight-zero part is finite modulo Q;
- **read** M3: over a diagonal point other than x, upper-only and lower-only points do not both occur;
- **read** M4: at a two-signed point, any two derivations killing Q are proportional;
- **read** M5: a has weight 0, x(a) = 0, and ξ(a) ≠ 0 at every two-signed point.

**read** The conclusion: finitely many torus orbits cover the two-signed points, and `cotLen x 𝒜 (−1) Q.F ≤ 2·Σ_{ξ∈T} v(ξ a)`. **proved-by** It is proved by `Alg.M.main_holds` (`…/CommutativeAlgebra/GradedModulesLength/MainCotSpan.lean:32`), whose inequality `core_holds` (`…/AlgMemCoef.lean:92`) compares Euler characteristics of a Rees-type graded module (`low_holds`, `chain`, `up_holds`). *inferred* It is a multiplicity count: the cotangent length bounds an Euler characteristic from below, and a bounds it from above through its valuations at the finitely many generic points.

**read** `vlen_le` states Vlen ψ ≤ M.len (`U3/VlenLe.lean:52-54`). **proved-by** `sha_inj` (`U3/ShaInj.lean:29`) embeds the b-torsion of the Selmer group into the weight −1 cocycles of r0 mod a (`shaCoc`). **proved-by** `model_lower` (`U3/ModelLower.lean:373`) turns those cocycles into weight −1 derivations and applies `LemmaM'`.

*inferred* As for the kind of argument: it is not an Euler system, and it constructs no Selmer classes, since it bounds them from above. *inferred* It is the residually reducible R = T pattern (Mazur's Eisenstein ideal; reducibility ideals as in Bellaïche–Chenevier and Wake–Wang-Erickson). *inferred* The Selmer group sits in the extension directions of the tangent space of R; every generic point is automorphic and reduced, so the reducibility locus is measured by the congruences a(ξ) between cusp forms and the Eisenstein trace. **read** The inequality itself names no Hecke algebra; Hecke algebras appear only inside the automorphy proofs of §3.

## 3. Where the points come from

**read** `AutomorphyUnramifiedCoefficientsAlt` (`DT/AutomorphyUnramifiedCoefficients.lean:23-26`) asserts that some marked g₁ has `FinA` (the weight-zero part is finite), `AutBAlt` (type-I points are automorphic) and `LemWAlt` (the 2-dimensional pieces at type-II points are modular). **proved-by** It is `automorphyUnramified_of_locPrints_kisin_gdEnd` (`DT/AutomorphyU3OfEndoscopy.lean:27`), from `GdEndAlt` (`DT/AutEnd3AltAlt.lean:35`), after moving each point to an ordinary point over a finite DVR. **proved-by** `GdEndAlt` is the first component of `ends0_alt hH` (`DT/DnEndsTop.lean:15`), via `gdEnd_of_frame_linkedEnd_downCsdK_descent` (`DT/GdEndOf.lean:22`), and its finiteness and automorphy come from `LinkedEndEAlt` (`DT/PlDefs.lean:12`).

**proved-by** `LinkedEndEAlt` is proved by `linked_endomorphism_dense` (`DT/LinkedEndE.lean:18`), which calls `twoRuns_alt` (`DT/TwoRuns.lean:80`), which calls `modularity_linked_ends` (`DT/PrLinkedEnd.lean:22`). **read** That uses `ModUAlt` (`DT/PointTheoremBaseObject.lean:44`): for the universal ordinary determinant ring B over Λ there is an ideal J with fields
- **read** `ring`, which includes B/J finite over Λ (`hJ.ring.fin` is used that way in `DT/PrLinkedEnd.lean`);
- **read** `dense`, a density condition;
- **read** `pt`: every automorphic arithmetic point kills J;
- **read** `end1` and `end2`, named for purity and classicality of arithmetic points.

**proved-by** `ModUAlt` comes from `hida_unitary_of_printed_hida` (`DT/THidaU.lean:38`), with J produced by `exists_hecke_ideal` over unitary Hecke data. *inferred* J is the kernel to a Hida Hecke algebra on definite U(3). *inferred* A dimension count (`dimOf`) makes every component through a seed point modular, which is the shape of Skinner–Wiles. *inferred* I met no Taylor–Wiles patching on this chain.

**read** The seeds come from `UnitaryThreeAutomorphyDense` (`DT/SymUse.lean:27`). **read** For every B it gives some m ≥ B with m ≡ j mod ℓ − 1, together with an r that is irreducible on open subgroups and satisfies `IsSeedAlt` with residual characters χ_cyc^j χ′, 1, (χ_cyc^j χ′)⁻¹ and weights (m, 0, −m). **proved-by** It is `adjoint_lift_from_eisenstein_of_propagation (prop_eg_w_of_printed_hida hH) (seedInW_alt hH) (adjoint_automorphy_w_of_printed_hida_window hH hR)` (`DT/UnitaryThreeInputsOfLiterature.lean:29`). **read** `PropEGW` produces ρ with `EisRep`: irreducible, automorphic for GL₂/ℚ, residually 1 ⊕ χ_cyc^{k−1}φ, and ordinary (`AV/IdeleGenerators/SlopeTestRemainingChoices.lean:101-109`). **read** `AdAutW` makes ad⁰ρ, suitably twisted, automorphic (`AV/ModularityArgument/SymmetricPowerTransfer/WeilDeligneUnramified/UnitaryTwoForm.lean:172-181`). *inferred* So the forms on U(3) behind type-I points are Hida deformations of adjoint lifts of Eisenstein-congruent cusp forms. *inferred* The type-II points are the endoscopic W ⊕ 1.

**read** The Galois representations enter as `rowOf' hH.litN.aut.gal` (`DT/UnitaryThreeInputsOfLiterature.lean:30`, `DT/KatoTwoWOfPublishedH.lean:48`, `DT/AutNewform2A.lean:20`). **read** At the top, `gal := gal` with gal the row h (`DT/TopMainZj.lean:47`), and h = `galoisRepresentations_of_thetaLift tLiftK` (`AA/CharacterBoxes/MainConclusion.lean:7-11`).

**read** Case V uses `ThmS6Core_s` (`DT/ThmS6CoreS.lean:27-36`) over ℚ(i): weight zero is finite and type-I points are automorphic. **proved-by** It is proved by `symmetric_cube_theorem_of_endomorphisms_alt (hostEnd_of_loc3_frame_linkedEnd_downCsdK …)` (`DT/DnEnds.lean:35-38`), the same machinery. **proved-by** Cases II and III use `SymplecticFourImageDense` (`DT/IsAut4.lean:14-17`), proved by `sp4In_alt coh FW.ferreroWashington seedIIs fourth_initial pmEx` (`DT/Sp4In0.lean:18`, `DT/Sp4In.lean:13`). **read** Its `PMExAlt` input is a potential-modularity tower (`DT/PotentialModularityTower.lean:63`).

## 4. Rigidity, and what Kato contributes

**read** `PtHyp` (`U3/Rigid0.lean:16-19`) has three fields. **read** `fixed`: a point that is both upper and lower triangular is the base point. **read** `rigid0`: there are no tangent vectors of weight ≤ 0 at the base. **read** `rigid`: every two-signed point is `Rigid`. **read** In `model_upper`, M1 is derived from `hpt.rigid0`, while M3 and M4 are derived from all of `PtHyp` (`U3/ModelUpper.lean:117-120`). *inferred* So M3 uses `fixed` and M4 uses `rigid`.

**proved-by** `ptHyp_of_autB_of_lemW_of_isBase` (`DT/FPtHypU.lean:15`) proves each field:
- **proved-by** `rigid0` by `bloch_kato_nonpositive_weight` (`U3/BlochKatoNonpositiveWeight.lean:297`), which uses LemmaK (`hP.lemK` at `:200`, passed to `X.soBar` at `:237`);
- **proved-by** `rigid` at type-I points by `RigidityFirstCase` (the adjoint Bloch–Kato Selmer group vanishes; `DT/RigEnd3.lean:28`), which rests on `AdjointLiftingTheorem` (`DT/AutomorphicPointGalois.lean:35`), whose core `DenseThresholdMainCase` is `core_of_ord_vanishing_two_phi_all (ordinary_vanishing_two_of_printed_hida hH) …` (`DT/ThFinal.lean:17`), and *inferred* that is Hida-theoretic;
- **proved-by** `rigid` at type-II points by `KatoTwoW` together with `RigiditySecondCase`.

**read** `KatoTwoW` (`AV/ModularityArgument/KatoQuadraticCharacters/SphericalDecomposition/KatoTwoW.lean:12-16`): for W with `Used` and W ⊗ χ_cyc^{−e} attached to a newform of weight 2e+1, `BlochKatoSelmerVanishes` holds for W and for W ⊗ θ. **proved-by** It is `katoTwoW_of_printsH` (`DT/KatoTwoWOfPublishedH.lean:48`), via `twoS`. **read** `ZetaUr` (`Development/AbelianVarietyTheory/Statements/CuspidalUnitaryTwists/ZetaUr.lean:18-20`) asserts `ES W A` for W from an ℓ-ordinary newform of level prime to ℓ. **read** `ES` (`Development/AbelianVarietyTheory/Definitions/Foundations/FinalTheorems.lean:98-103`) asks for an integral class y ∈ H¹, unramified away from ℓ and outside the ordinary local condition at ℓ, together with Kolyvagin derivative data `Tame` at every prime w ≡ 1 mod ℓ^n. **proved-by** `zetaUr` (`AV/ModularityArgument/KatoQuadraticCharacters/UnramifiedZeta/ZetaUr.lean:9`) builds it from `kato_eulerSystem_integrality`, `smoothedZetaClass_hodgeTateLaw`, and a non-vanishing of a Hecke projection. *inferred* Kato's contribution is that the off-diagonal pieces of ad(W ⊕ 1) have vanishing Selmer groups, which makes the endoscopic points isolated and reduced (M4). *inferred* It never bounds Sha directly.

## 5. LemmaK, BOdd, Ferrero–Washington, the minus part, PropZ

**proved-by** `lemmaK_litN_alt hN := lemmaK_of_litN_alt hN bOdd` (`DT/KFinal.lean:11`) reduces to `lemmaK hB pt lfK ltK` (`AV/ModularityArgument/ClassCounting/LemmaKOfLitN.lean:28`), and that to `lemmaK_of_steps` with 21 step lemmas (`…/ClassCounting/LemmaKOfSteps.lean:170-174`). **read** `BOdd` (`:11-15`): for L totally complex, k even with k + 1 < r₂(L), and n ≥ 2(k + 1) + 4, the span of the `zSeq` images of H_{k+1}(GL_n(O_L)) has rank ≤ r₂(L). **read** `zSeq` iterates x ↦ (A ↦ 1_l ⊗ A)_* x − l^{t+2}·stab_* x (`…/ClassCounting/HasVal.lean:45-61`). **proved-by** `bOdd_zk` (`AV/LiteratureResults/KTheoryStability/ReductionBoundsTorsion/TorsionIntegers/Bridge.lean:34`) reduces to `bStarOdd` (`…/FinalOdd.lean:8`), whose steps integrate invariant forms `Form (HS L N) (k+1)` over cycles (`SWtOdd`, `…/SBStarOdd.lean:9-18`) and use Stokes, Hecke and separation lemmas. *inferred* This is Borel's rank theorem for odd K-groups, reproved through invariant differential forms.

**read** `STors` (`…/LemmaKOfSteps.lean:157-159`): log #tors H_m(GL_{4E+6}(O_L)) ≤ kBound C E [L:ℚ] |disc L|. **proved-by** It is `sTors` (`…/ClassCounting/ExponentLe.lean:122`), from `torsBound` (`AV/HermiteNormalForms/Assembly.lean:32`): an acyclic complex (`acyc_simp`), an orbit count (`orbnum`), and finite stabilisers. *inferred* This is Soulé's method. *inferred* Selmer elements are detected by homology classes (`SClass`, `SDetect`), the number of those classes is (ℓ^ν)^{r₂} times torsion counts (`SUpper`), and Poitou–Tate finishes (`SFinal`).

**proved-by** `UpperTheory.V.FW.ferreroWashington` (`AV/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:104`) goes through `cyc` (`:18`), which uses:
- **proved-by** `stickH`, Stickelberger annihilation (`StickH.lean:8`);
- **proved-by** `nonvan`, the twisted Stickelberger element is non-zero mod ℓ (`Nonvan.lean:12`), which comes from `sinnott` (`Sinnott.lean:10`);
- **proved-by** `reflOdd`, reflection.

*inferred* This is Sinnott's proof that μ = 0. **proved-by** `thmBab_of_lemmaK` (`AV/LayeredIsomorphisms/ThmBabOfLemmaK.lean:9`) consumes FW and `TowerBound` (`aBound_of_isTower`, `AV/AdditiveValuationNorms/ABoundOfIsTower.lean:7`). *inferred* Bounded ℓ-rank up the tower leaves at most R exceptional roots s_i: μ = 0 plus the structure theory of Λ-modules.

**proved-by** The minus part `ML.iv` (`AV/PrimitiveFrobeniusFixed/Iv.lean:4`) goes through `psiOf` (`PsiOf.lean:12`). **proved-by** It is assembled from Kolyvagin derivative classes (`kolStep`, `KolStep.lean:135`), elements `IsX` with X·X̄ = 1 and (X) = ∏ σ_t(𝔞)^{θ(t)} (`IsAdmissiblePrimeListNil.lean:15`), and their Jacobi-sum congruences (`xCongJac`, `XCongJac.lean:101`). *inferred* This is Rubin's Euler system of Gauss sums. **proved-by** `X.propZ` (`AV/LevelCohomology/PropZ.lean:11`) splits into two cases: ℓ − 1 | e (`zOne`), and ω^e quadratic (`zQuad`).

## 6. `HypothesesH'`: use, not presence

**read** `published_hypotheses_from_patching_alt` (`DT/PublishedHypothesesFromPatching.lean:98-103`) fills every field with an in-tree term. **read** Consumers below `vwin_of_hypotheses_H_E_alt` (`DT/WindowBoundOfLiteratureLevel.lean:25`) were found by an upward name-reference search over `AA/`; the hops marked ✓ were checked by reading. **read** All files in the table are in `DT/`.

| field | first consumer | reaches |
|---|---|---|
| litN | `lemmaK_litN_alt`, `of_four_alt` ✓ | all cases |
| cohC, borelC | `TCardK.lean:26-28` ✓ | `countK_alt` → NumberU3U |
| conjC | `TConjK.lean:41` ✓ | `countK_alt` |
| galR | `ExRS.lean:22` ✓ | `autNewformA_of_printsH_of_repNewAE` → `ends_of_alt` |
| smoR | `UnramifiedAlgebraicWeights.lean:67`; `SdAdAutQ.lean:36` | Kato; `sp4In0_alt` |
| gkR | `PolGL2.lean:41` | `rankTwoAutomorphyDescends_of_printsH` → `ends_of_alt` |
| admR | `TCentChar.lean:314` ✓; `UnramifiedAlgebraicWeights.lean:66` | `autNewformA_of_printsH`; Kato |
| bc | `AutNewformAOfEx.lean:115`; `BcIndCs.lean:19` | `ends_of_alt`; `sp4In0_alt` |
| newform | `TNewformAut.lean:69`; `ExistsRep.lean:22` | `rigII_a_alt` → CountI; Kato |
| descU | `UnitaryThreeInputsOfLiterature.lean:27` ✓ | seeds |
| cyc, cyc2 | `GalRepDescentAlongQuadraticExtension.lean:12` ✓ | `ends_of_alt` |
| ssR | `ExistsSat.lean:46`; `TwistNewform.lean:55` | `sp4In0_alt`; Kato |
| quat | none | — |

**read** In `src/` (excluding `BuildAid`, `Lemmata`, `Supplements`), `.quat` or `DefQuatExists` occurs only in the definition, its proof, the two structure fields, and an unrelated `ZarhinFam.quat`; the constructor writes `quat := defQuatExists` and nothing reads it. *inferred* `DefQuatExists` is carried along and never used. *inferred* The search matched names only, so it misses typeclass resolution, and three of its first answers ran through name collisions (`cyc`, `core`); that is why the ✓ hops were read.

## 7. What the bound rests on

- (i) **read** No declaration or file in `Development/` or `Formalism/` matches `MazurWiles` or `MainConjecture`. *inferred* The minus part rests on a Kolyvagin–Rubin Euler system, and the towers on Ferrero–Washington (μ = 0) plus Λ-module structure; no Iwasawa main conjecture.
- (ii) *inferred* Automorphy lifting carries weight in Cases I and V (U(3) Hida families plus seeds), in Cases II and III (a GSp4 potential-modularity tower), and for the type-II pieces (GL₂).
- (iii) *inferred* Galois representations for U(3) and GSp4 are needed. *inferred* `RowT`, `galR` and `IsAut4` are discharged through the theta-lift construction.
- (iv) *inferred* Kato's Euler system is used only for the rigidity of endoscopic points.
- (v) *inferred* A Soulé-type K-theory argument carries LemmaK and the rigidity of the base point. *inferred* Bloch–Kato enters only as vanishing statements for Selmer groups; no Tamagawa-number formula appears.

## Not read

- `core_holds` internals (`low_holds`, `up_holds`), `sha_inj_gen`, `main_der`, `exists_model`, `LemmaP`.
- `exists_ordPt_of_point`, `finA_of_end`, and inside `twoRuns_alt`: `absMain`, `dimOf`, `glueN`.
- `seedPtOf_alt`, the proofs of `PropEGW` and `adjoint_lift_from_eisenstein_of_propagation`.
- The bodies of `hida_unitary_of_printed_hida` and `DenseThresholdMainCase`; `twoS` and `VanishOrdL` inside `zetaUr`.
- LemmaK's step lemmas (`SClass`, `SDetect`, `SUpper`, `SNum`), the Sinnott internals, `ML.iv` beyond its names, `zOne`, `zQuad`.
- `LevelKNAlt` and its local–global compatibility, `iso_of_frobenius_of_printed_results`.
- `main4_alt`, `sp4Main_alt`, `countIV`, `countVs`, and the body of `symmetric_cube_theorem_of_endomorphisms_alt`.
