# The period-integrality rows of `HypsAlt`: statements and what proves them

Read 2026-11-20 from source text only; nothing was built. Paths are relative to `src/`. Abbreviations:
- AGP = `Formalism/LocalToGlobal/GroupLattices/AdmissibleAtGeneratorPlaces.lean`
- WDS = `Formalism/SharpRestriction/Divisibility/WeightDegreeSizes.lean`
- PFZ = `Formalism/SharpRestriction/GlobalSchurBounds/ProductFirstZerothParts.lean`
- FMAT = `Formalism/SharpRestriction/GlobalSchurBounds/FiniteModelOfAdmissibleTransports.lean`
- GI = `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/`
- SP = `Development/AbelianVarietyTheory/Proofs/SatakeParameters/`
- HI = `Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/`

Tags: **[R]** means I read the quoted text. **[P]** means I read the proof and name what supplies it. *[I]* marks my interpretation.

## 1. Direct answers

**These rows are theorems, not assumptions.**
- **[R]** `allRows_of_open0_alt` (TPS/LinkROfIsLinked.lean:50) fills aP10 and aPt0 to aPerTw (lines 60–65) from `period_entries_tie_and_level_valuations_at_built`, which is `six_rows_at_member_alt` (TPS/SixRowsAtMember.lean:11). It fills aAtG (line 61) from `row_aAtG_at_built_alt _ rfl _` (TPS/RowAAtGAtBuilt.lean:10).
- **[R]** Neither call takes any of the `GlobalTheory.Published` arguments that `allRows_of_open0_alt` itself receives. Their only inputs are the slot data `𝒮` and `Lk`, plus `𝒮.Rx = RX`, which holds by `rfl`.
- **[R]** Each row has the form `Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) …` with the witness `R := True`. Through `Row` (GlobalTwisting/ValidForConstructedPointClassesEventuallyWorking.lean:268) it constrains only families whose members are bundle points carrying a `Built` record. *[I]* So each row says nothing until some family is shown to consist of built points; that is established elsewhere, and I did not read it.

**What kind of mathematics proves integrality.**
- **[P]** aPt0 and aPtTw (integrality of the period-point map) rest on integral representation theory of GL_n. The branching map `brOne`, from the GL_N Weyl module to the GL_{N−1} Weyl module, sends ℤ-forms to ℤ-forms (`int_member`). The rest are ties that identify the abstract lattices with integral coordinate models.
- **[P]** aPer0 and aPerTw (the period pairing) rest on an exact duality: the ℤ-forms of the Weyl module Δ and of the dual Weyl module ∇ are dual under the normalised Fock pairing. It is applied one class at a time, and the only denominators are the stabiliser orders, which divide DGam.
- *[I]* The "period" in these four rows is therefore algebraic and of Gross–Prasad type: a finite sum, over the genus classes of a definite U(N−1), of Weyl-module pairings weighted by 1/|Γ_c|. It involves no q-expansion, no transcendental CM period, no Schwartz-function integrality and no literature item.
- **[P]** aP10 is a local computation at the split level prime T. It uses point models at T, the fact that the theta kernel intertwines U_T up to the factor T^{(t+1)/2}, and stabiliser orders prime to T.
- **[P]** aAtG, at the primes g₀ and g₁, is CM theory. The Taylor jets of theta kernels on a CM abelian variety are p-adically integral at split primes. That variety is built from the CM elliptic lattice δ·𝒪_K, with δ¹² = Δ, i.e. normalised to unit discriminant.

**Ω.**
- **[R]** `logOm := γ + log(π/v) − L.logDerivativeAtOne` (DataParams₂.lean:224). The field `logDerivative_at_one_eq` (:126–127) pins the last term to Re L′/L(1, χ_d). Here v = rdE/2, and rdE is the root discriminant of the CM field E (DataHost.lean:140–143).
- **[R]** The CM period itself is the field `gx.Om τ s`. On the built path, `gx` is set to `trueGx` (Retie.lean:11; also the hypothesis of `omTied_withTrue`, IwasawaDecomposition/ExistsGIs.lean:51).
- **[R]** `trueGx` sets `Om τ s := posOr1 (area (conjLat s) / (π·‖s (gen τ)‖²))` (AutomorphicMembership/IsHalfPtIff.lean:45, 51). Here `conjLat s` is a lattice of discriminant 1 whose j-invariant is the s-conjugate of j(𝒪_K), and `gen τ` generates an ideal of LL built from the relative different of E/K.
- **[P]** That the mean of log Ω_τ over embeddings equals logOm is a theorem: `omLink_of_tied` followed by `meanPeriodAt` (chain in §3).
- **[P]** Chowla–Selberg, which that theorem needs, is proved in the tree from Kronecker's first limit formula, and the limit formula is proved there too. It is not a literature item.
- **[R]** `Lerch` (Formalism/LFunctionBounds/PositivityBound.lean:19) occurs nowhere in this chain.
- **[R]** A hypothesis-shaped `KroneckerLimit` (Formalism/LocalToGlobal/GlobalTheory/GL3/Statement.lean:12) occurs only as an antecedent, for example of `LinkPer` (:56). A search for a proof term of that type found none.
- **[R]** None of the seven definitions mentions `Om` or `logOm`, and *[I]* neither do the proofs I read. Ω enters elsewhere: `kerSide_chainS` uses `meanLogPeriod_chowlaSelberg` (DivisorProofs/KernelHalfChainNumbersAnyLevelPrime.lean:222, 227). I did not trace that to the top.

**Vacuous or true by construction.**
- **[P]** `SgAtG` is bookkeeping. At the g-places `FDef` gives F = FTypeG and `ErrDefs` gives E = vDG + EatG, with EatG = FTypeG + vNN + ce.g·f·(Nm² + m²·etaSz) (DataErr.lean:91). So Σ_j(F − E) = −Σ vNN − m·ce.g·A − m·vDG, which is at most −Σ vNN − C1·errC once 2·C1 ≤ ce.g (`sumFE_atG_le`, AdmissibleParameterJoins/GandSx.lean:12). The row takes C1 = 1, and `2 ≤ Fm.cX.err.g` comes from the family's large-constant condition.
- **[R]** Integrality of the test vectors is a definition: `mem_mtildeL_iff … := Iff.rfl` (GI/ExistsTrueColsRowInt.lean:16) says z ∈ MtildeL exactly when every row value of z lies in ∇.
- **[R]** The period lattice `ptLat` is a free field of `MemberForms` (DataForms.lean:203). **[P]** Its place-by-place description by integral coordinates (`pt_co`) comes from the tie `Tf.valP.lat`. The substantive step in aPt0 is therefore branching integrality.
- **[R]** Over T the "gain" is a loss: `ETDef` sets gain = F = 0 and E = ET at places over T (PFZ:320). *[I]* So aP10 permits denominators up to T^{m·ET}.

## 2. The seven statements

1. **MemberChainIntegral (aPt0).**
   - **[R]** `def MemberChainIntegral D := ∀ u, product_first_zeroth_parts.Conclusion6 D u` (WDS:718).
   - **[R]** `Conclusion6` (PFZ:334) is a conjunction:
     - `til` is injective, and every `stabMap c` is bijective;
     - `∀ φ ∈ Fi m, Pt D u φ ∈ ptC`;
     - `∃ h : PRat, PtilIntegral h ∧ ∀ v x, maj_v (PtL h x) ≤ ptB·maj_v x`;
     - `ipP (Pt φ) (Pt φ) ≤ ptB·ipC m φ φ`.
   - **[R]** `PtilIntegral h := ∀ x ∈ (lat m).L, PtL h x ∈ ptLat.L` (DataForms.lean:273). `PtL` is the LL-linear descent of `Pt = lowerMap ∘ evz` (:264–271), and `ptB = ∏_τ T^{−deg τ}·beOn τ²` (PFZ:332).
   - *[I]* In words: evaluate a top-level form on the classes coming from the smaller group, then branch its values. This map is defined over LL and sends the 𝒪_LL-lattice of top-level forms into the period lattice at all finite places at once, with a norm bound at each infinite place.
2. **TwistedPointIntegral (aPtTw, AGP:11).**
   - **[R]** `∀ u μ, UsedT D μ → μ ≠ mu0 → ∃ h : (T.fm u μ).PRat, (T.fm u μ).PtilIntegral h`: the same integrality for every used twisted chain.
3. **PeriodClassSumWeyl (aPer0, WDS:723).**
   - **[R]** The statement: `DGamDef D → ∀ u, ∀ x ∈ ptLat.L, ∀ F ∈ Mtilde μ0, F ∈ V0 μ0 → ∃ y, embLL y = P.period (ptEmb x) (eMt⁻¹ F) ∧ ∀ w, y = 0 ∨ −ur D w (vDG D u w) ≤ v_w y`.
   - **[R]** Here `vDG = v_p(DGam)` (WeilJacquetShalikaLaw.lean:67) and `ur D w y = e_w·y` (DataDIVDefs.lean:15). DGam is a common multiple of every stabiliser order of the chain (DataKernels.lean:23–25).
   - *[I]* The pairing of a period-lattice vector with a test vector in Mtilde ∩ V0 lies in LL, and at every finite place its denominator is at most that of DGam.
4. **TwistedPeriodAdmissible (aPerTw, AGP:14).**
   - **[R]** The same statement for the period map `PTw u μ`, with μ ≠ μ0 used, at places whose residue characteristic is not in `Dx.Qp μ`.
   - **[R]** `Qp_muAt` (DataDIV.lean:492) guarantees that the place where the bound is applied is never excluded.
5. **Conclusion5Sharp (aP10, first half; PFZ:315).**
   - **[R]** The statement: `∀ w, OverT D u w → ∀ c n, val w c = n → e_w·(m·ET D u w) ≤ n → Into D u w (c • colT D u ·) (Nlam D u w) ((fm u).S m w)`.
   - **[R]** `Nlam` is the image of the ramified local lattice `Sram` under `T^expT·U^m` (DataLatDefs.lean:96).
   - **[R]** `EatT` is 2Σ_τ Wtau + f·Nm + |tops|(t+1)(m+1)/4 when `seenP w` holds, and 0 otherwise (DataErr.lean:103).
6. **TwistedColumnBoundAtT (aP10, second half; AGP:20).**
   - **[R]** The statement: `∀ w over T(u), ∀ μ used, μ ≠ μ0, w ∉ Qp μ → ∀ x ∈ Nlam, ColGeTw T u μ w x (−m·EatT)`.
   - **[R]** `ColGeTw` says that the twisted chain sends x to `a • z`, with z in the w-local top lattice and `a = 0 ∨ e_w·s ≤ v_w a` (WeilJacquetShalikaLaw.lean:19, 28).
7. **UsedTuplesBoundByConstant and SgAtG (aAtG).**
   - **[R]** `UsedTuplesBoundByConstant` (AGP:25): `∀ i w, Over D i w → ∀ u, resChar w ≠ T(u) → ∀ μ used, ∀ φ ∈ MramL D u, ∀ F ∈ Mtilde μ, ∃ y, embLL y = perCol u μ (jN u φ) F ∧ (y = 0 ∨ −Σ_j vNN EX i u j w − C1·errC ≤ vG D w y)`.
   - **[R]** `Over D i w` means resChar w = g_i. The loss is `vNN = (Σ_τ nuAbs(u,j,τ)·v_w(τ(π̄_{g_i})))/e_w` (DataErr.lean:88).
   - **[R]** `SgAtG` (WDS:1002) says that at the same places `Σ_j (F − E) ≤ −Σ_j vNN − C1·errC`. `familySizeBoundAtTypePrime` (WDS:1147) is the eventual form for the family.

**How the rows are used.**
- **[R]** `period_geTU` (AGP:72) multiplies a column factor a, with v_w(a) ≥ e_w·s, by the period of a point of the top lattice.
- **[R]** For μ = μ0 that period is bounded by aPt0 and aPer0 (`pair0U`, AGP:39); for μ ≠ μ0 by aPtTw and aPerTw (`pairTwU`, AGP:55).
- **[R]** The column factor comes from aP10 over T (AGP:92) and from `Conclusion1` at other places (AGP:171).
- **[R]** At g₀ and g₁, aAtG replaces the whole argument (`atG_coreU`, AGP:113; `admissible_at_generator_places`, AGP:134).

## 3. Chains

**aPt0.**
- **[P]** The chain to the top, step by step:
  - `six_rows_at_member_alt`;
  - `referenceChainEvaluation_bundlePoints_overColumns` (GI/ReferenceChainEvaluationBundlePointsOverColumnsA.lean:18);
  - `view_at_built` (GI/PropertyAtConstructedPointsOfTrueColumnsView.lean:11), together with `colView_of_built` (GI/ColViewOfBuilt.lean:13);
  - `formsMap_at_every_trueColumnMember` (GI/FormsMapAtEveryTrueColumnMember.lean:15);
  - `formsMap_of_symmetricComparison_lowerMap_finiteChar` (GI/FormsMapOfSymmetricComparisonLowerMapFiniteChar.lean:12).
- **[P]** The last of these is `classMap_estimate_of_partial` (FMAT:2259), applied to a `Pend` (PFZ:480) that `exists_integralPendingObject_symmetricFormsLevel` provides (GI/ExistsIntegralPendingObjectSymmetricFormsLevel.lean:291).
- **[P]** The `PtilIntegral` part runs `Pt_integral` (FMAT:2240) ← `Pt_loc` (:2192) ← `blk_IntSpan` (:2169). That uses clause 1 of `IsBr` (Divisibility/PrimeDegreeVariant.lean:79): `∀ f ∈ delSq ℤ N λ, ∃ g ∈ delSq ℤ n σ, br (map f) = map g`.
- **[P]** For `brOne` that clause is `int_member` (KernelLocalFactors/InterlaceDifferenceShiftInvariant.lean:3956), which calls `int_brOne`, reached through `brOneIsBr` (:4710).
- **[R]** `delSq ℤ N λ` is `weyl`: the ℤ-span of words in divided-power operators applied to the highest-weight vector. `nablaSq` is `dualWeyl` (LocalRingCardinality/DataCoeff.lean:49–52; GradedWeylDivisibility/StatementA.lean:24, 71).
- **[P]** The fields of the `Pend` are ties:
  - `lat_co` comes from `(Tf.val m).lat`, with the level character's values inverted as roots of unity (`root_mem_intW`);
  - `pt_co` comes from `ptCo_mem_intSpan`, `exists_ptEmb_of_coord_int` and `mem_SP_of_coord_integral` (:211), and the last reads `Tf.valP.lat`.

**aPtTw.** **[P]** `row_aPtTw_of_overCols` (GI/TwistedChainEvaluationRationalIntegralBundlePoin.lean:13) ← `twistedPointIntegral_of_TC_ok` (GI/TwistedPointRowAdmissibleTrueColumns.lean:12) ← `lowerTieTwAt_integral` (Divisibility/HookProducts/AdmPtTw.lean:108). That last step is `Pt_integralT` (:98) with `brOneIsBr`.

**aPer0.**
- **[P]** The chain: `row_aPer0_of_overCols` (GI/ReferencePeriodIntegralBundlePointsOfOverColumns.lean:9) ← `periodAdmissible_of_integralPeriodRows` (GI/PeriodAdmissibleOfIntegralPeriodRows.lean:10). That theorem combines two results.
- **[P]** `admissiblePeriodZero_of_classPeriodDecomposition` (GI/AdmissiblePeriodZeroOfClassPeriodDecompositionAl.lean:196) writes the period as Σ_c |stab c|⁻¹·y_c (`petersson_eq_sum_restrict`, :88). It gets |stab c| ∣ DGam from the injectivity of `stabMap` (:202–204, with `vAdd_card_le`, :170).
- **[P]** `perDec0At_std` (GI/VAddNonnegOfInt.lean:28) proves each y_c integral by `pair_integral` (GI/ClassPairingIntegralFormRowIsIntegral.lean:49), once the period is identified with the class-sum Petersson pairing through `F.per`.
- **[P]** Below `pair_integral`: `PeriodClassSum.pairBDual` (GI/IsClassSumPairingFormsLat.lean:196) ← `pairBDualK` (:181) ← `TransDual.nabDelDual` (FoundationProofs/TransportedWeylLatticeHermitianDuality.lean:278) ← `standard_weyl_lattices_fock_dual`.
- **[R]** The statement doing the work, `PairBDual` (Columns/CoefModB.lean:112), is a duality in both directions: x ∈ Δ(L) iff pairB(x, y) ∈ 𝒪 for every y ∈ ∇(L), and x ∈ ∇(L) iff pairB(x, y) ∈ 𝒪 for every y ∈ Δ(L).
- **[P]** The test-vector side is `RowInt.ref` (GlobalTwisting/LowerTieTwAt.lean:80), a field of `RowsT` (AutomorphicMembership/NonzeroPlacesOverPrimes.lean:61).
- **[P]** That field is set in `exists_rowsT` (IwasawaDecomposition/ExistsRowsT.lean:62) by `rowInt_over` (GI/PeriodRowLatticesIntegralProvisionalRows.lean:47), which carries the definitional `mem_mtildeL_iff` across the generator tie `latT`.

**aPerTw.** **[P]** `row_aPerTw_of_overCols` (GI/TwistedPeriodsIntegralAtBundlePoints.lean:11) ← `twistedPeriodAdmissible_of_rowInt` (GI/AdmissiblePeriodTwistOfIntegralRows.lean:14) ← `perDecTwT_of_std` (GI/PerDecTwTOfStd.lean:11, which calls the same class-pairing theorem), then the twisted decomposition and the reduction to place tuples.

**aP10.**
- **[P]** The chain: `row_level_valuations` (GI/LevelPrimeColumnValuationsBundlePointsOverColumn.lean:11) ← `closing_true_cols` (GI/ClosingTrueCols.lean:12) ← `row_true` (GI/TrueColumnsRowSharpBounds.lean:36) ← `trueColumns_chain_last_step_sharp_bound` (:17) ← `sharpBound_stability_latticeColumnChain` (GI/SharpBoundStabilityLatticeColumnChain.lean:17).
- **[P]** Its inputs are:
  - `fivePointLaws_trueChains`: T splits at every level, and the kernels satisfy KerEq, KerDil, KerUK, KerBar and KerP;
  - T > [E:ℚ]·N(m) + 1, from `X.a_gt` and `X.T_gt`;
  - weight signs.
- **[P]** Inside it:
  - `levelChainUOperatorCommutation_of_pointPairLaw` gives `U_{i+1}(K_i φ) = T^{(t+1)/2}·K_i(U_i φ)` (PFZ:291);
  - `stabUnit_of_chainIn` uses the size of T;
  - `UKS.ukSharp` and `levelChainSharpColumnValuation_of_stability` conclude.

**aAtG.**
- **[P]** The chain: `row_aAtG_at_built_alt` ← `row_aAtG_of_rowPin` (SP/ConstructionAtBundlePointsOfTrueColumns.lean:11) ← `row_atG_pinned` (SP/PeriodValuationsTypePrimesOfJetTableSplitPrime.lean:11) ← `row_atG_of_jetSplitAmb` (SP/TypePrimePeriodRowOfConstructedPointChains.lean:15), which fixes C1 = 1.
- **[P]** `SgAtG` is `family_type_prime_loss` (AdmissibleParameterJoins/GandSaj.lean:43) ← `sgAtG_of` ← `sumFE_atG_le`.
- **[P]** The bound itself comes from `jetTableBound_constantOne_of_chainAgreement` (SP/JetTableBoundConstantOneOfChainAgreement.lean:11) ← `boundAt_of_ties` (SP/PeriodValuationBoundTypePrimePlaceOfChainAgreeme.lean:96) ← `boundAt_of_chainTie` (:19).
- **[P]** `boundAt_of_chainTie` uses:
  - `PerTie`, to rewrite the period as `PtilE` of the concrete chain `colMu` on `ambOf (recSeam D) B χ cD`;
  - `colMu_bound_all`: the chain times Π_j lossAt is integral at w;
  - `valuation_PtilE_le_one`;
  - `BranchFormula.integrality`;
  - `vG_loss_le`.
- **[P]** The jet input `JetLossAll` comes from `jetSplitAmb_holds` (SP/JetTableBoundSplitPrime.lean:7) ← `jetAtSplit_ambOf` (KernelLocalFactors/SelfDualLatticeNorms.lean:110) ← `AlgTh.jetAtSplit` (AlgebraicTheory/LocNormScale.lean:12) ← `split_place_scaled_bound : SelfDualLatticeThetaPadicIntegrality` (AlgebraicTheory/SplitPlaceScaledBound.lean:9).
- **[R]** `JetSplitAmb` (GaloisGeometry/JetSplitAmb.lean:15):
  - It assumes a split prime p = ππ̄ ≥ 5 with p ∤ d.
  - It also assumes `IsCurveIdeal`, δ¹² = Δ(𝔠) (`IsDiscriminantTwelfthRootOfIdealLattice`) and `IsChi`.
  - It concludes `‖ι(σ₀(jetK S N N′ (p·c′) x m))‖·‖ι(π̄)‖^{deg m}·‖p‖^{|Tau|·a·b} ≤ 1`.
- **[R]** The CM hypotheses reach this point through `AnTie` and `HostTie`, which requires `ccK = ⊤` (ThetaLiftGeometry/BadPrimesPeriodBound.lean:61, 70).

**Ω.**
- **[R]** `OmegaCompatible` (Formalism/LocalToGlobal/GlobalTheory/LinkTiesOm.lean:72): `Om τ s = (π‖s d‖²/area(lamConj M s (lamOf D ccK δ)))⁻¹`, where d generates `ellT D M τ`.
- **[P]** `omTied_retie_of_cube` (ExistsGIs.lean:21) proves it for `trueGx` through `ties_of_data`.
- **[P]** `omLink_of_tied` (LinkTiesOm.lean:80) turns it into `OmLink`, that is, `logOmMean = meanLogOm` (GlobalSchurBounds/Joints.lean:545).
- **[P]** `meanPeriod` (DivisorProofs/MeanLogPeriodChowlaSelberg.lean:84) is proved via `meanPeriodAt` (:58) from three results:
  - `br_meanLogOm_eq` (GL3/CubicFields/PeriodRelations/Period.lean:39);
  - `two_log_brN` (:17), which gives log rdE − log √d from the norm of the relative different of E/K;
  - `mean_log_period` (FoundationProofs/MeanLogPeriodConjugatesEqChowlaSelberg.lean:202): the mean of log(area/π) over conjugates equals γ + log(2π/√d) − L′/L(1).
- **[P]** `mean_log_period` comes from `mean_log_area` (:141), which uses three ingredients:
  - CM elliptic curves over number fields;
  - integrality of CM homomorphisms under good reduction;
  - the class-group average, and the product formula applied to the unit discriminant.
- **[P]** It also uses `chowla_selberg_eta` (HI/DedekindZetaEqSumRealEisenstein.lean:222), which says (1/h)Σ_c log(4π·Im τ_c·|η(τ_c)|⁴) = γ + log(2π/√d) − L′/L(1, χ). That follows from:
  - ζ_K = ζ·L(χ) (`dedekindZeta_eq_mul_LFunction`, HI/ExistsIsKroneckerCharOfDiscr.lean:507);
  - ζ_K as a sum of real-analytic Eisenstein series over ideal classes (:83);
  - Kronecker's limit formula `tendsto_realEisenstein_sub_pole` (HI/TendstoRealEisensteinSubPole.lean:352), which says E(τ,s) − π/(s−1) → 2π(γ − log 2) − π log Im τ − 2π log|η|².
- **[P]** `omValue_of` (Joints.lean:555) turns these into `OmValue`, the content of `ChowlaSelbergPeriod` (Divisibility/WeightFamilies.lean:387).

## Not read

I did not read the following, beyond a call site or a signature:
- `symmetric_level_clauses_hold` and its four clauses, which give the injectivity and norm parts of `Conclusion6`.
- The bodies of `int_brOne`, `standard_weyl_lattices_fock_dual` (`StdDual.std_dual`) and `weyl_eq_dual_nabla_holds`.
- `colsTiedSym_std`, `lowerMap_tie`, `brExists_of_rest4S`, `ptCo_mem_intSpan`, `exists_ptEmb_of_coord_int`, `coMTS_of_gaInv`, and the concrete `forms`/`TC.cols` construction.
- `twistedEvaluation_branching_all_tuples_trueColumns` and the remaining twisted-period lemmas.
- `fivePointLaws_trueChains` and the five kernel laws, `ukSharp`, `levelChainSharpColumnValuation_of_stability` and `stabUnit_of_chainIn`.
- `colMu_bound_all`, `valuation_PtilE_le_one`, `vG_loss_le`, `jetLossAll_of_jetSplitAmb`, `jetAtSplit_of` and its ten lemmas, `split_bound_of_xi_lemmas`, and `kerStdEx`.
- `concreteChainAgreesAtTuple_of_normalisedRows`, `rowPin_of_rx` and `kernelDegrees_small_against_typePrimes`.
- `ties_of_data`, `induced_type`, `exists_ellipticCurve_polarised_lattice_family`, `mean_log_covolume_eq_mean_classGroup`, `thetaUnifAV_all` and `homExtension_semiAbelian_dvr_unconditional`.
- Whether `OmValue`, `kerSide_chainS` and `L3main` lie on the path to the top theorem.
- The existence of built bundle points, which is what makes these rows non-vacuous.
