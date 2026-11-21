# The main term: per-step budgets, eigenvalues, covolumes, and where the Sha bound is spent

Read 2026-11-20 from source only; nothing built. Paths are relative to `lean/src/`. DV = `Formalism/LocalToGlobal/Divisibility/`, DP = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/`, DD = `Development/AbelianVarietyTheory/Definitions/Divisors/`, TPS = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`, IF = `Formalism/LocalToGlobal/IndefiniteForms/`, IR = `Formalism/LocalToGlobal/IndefiniteReal/`. Tags: **read** (definition or statement transcribed), **proved-by** (proof body read, inputs named), *inferred*.

## Direct answers

1. The lattice main term is closed real arithmetic (`DivIneqRecord`). Per lift step j and CM place ρ, the step's kernel costs Σ_i ph(ν_i) − (Σ_i ν_i)·log Ω. The step's eigenvalue repays Σ_i ph(ν_i) except ph(a) at a top place. The covolume of M_j repays the k·w·log Ω part. Each step leaves ph(a) − a·log Ω; the last map costs −a·log T. **proved-by**
2. The a! comes from a Cauchy estimate in the Fock (Gaussian) norm for jets of a function of Gaussian growth (`BlockBound`). Ω_ρ,τ = area(Λ^ρ)/(π|ρ(c_τ)|²) enters through the jet coordinate scaling |c·r|² = 1/Ω. Its mean over conjugates, γ + log(π/v) − L′/L(1,χ_d), is Chowla–Selberg (`MeanPeriod`). **read**
3. The eigenvalue of one step is θ_jθ_j* = a_j·z on each Hecke part, z = L^S((1+t)/2, ·) with t large (`AForm`). The bookkeeping uses only a lower bound: log λ_j ≥ Σ_ρ log(hook products) − O(f·n²·log). Interlacing makes source factorials and target hook products cancel except the long row a. **read**
4. `ThmAop`/`ThmBop` are scalar identities on Hecke pieces at the base place. They come from `AForm` and `BForm` (ΘΘ* = κ₀∏_j z_j, the same L-values) through Siegel–Weil, doubling and unramified Howe duality, with κ = κ₀/∏a_j. `BForm` is the same identity as `ThmBop`. **proved-by**
5. The Sha bound (`DIVinN`) is consumed at exactly one place. It bounds Σ_w log N(w)·len(T_j/cut_j), which bounds the Hermitian discriminant index of the lifts' level lattices T_j at twisted primes, the J-term of the divisor inequality. On the used routes, the proofs of `Onto` (index of θ_j T_j in M_j) and `Fun0` (top slope) discard the premise. **proved-by** The link to Galois cohomology runs through congruence ideals of Hecke algebras, bounded by Sha lengths (Ribet-type, not Bloch–Kato). *inferred*
6. The lattice main term equals the analytic MAIN identically. log(π/v) cancels log(v/π), m·log(g0 g1) cancels the special-prime penalty, and Main = Σ Re MAIN by unfolding. Only the stated error terms remain. **proved-by**

## 1. The record and the arithmetic

**`RecNums`** (DV/Inputs.lean:18) **read**:
- Data: TT (top places), logT, aT, row lengths ν j ρ i, logH j ρ, weights w j ρ, pq j, logOm.
- Constraints:
  - `weight_height_sum_le : Σ_i ph(ν j ρ i) − logH j ρ ≤ [ρ∈TT]·ph(aT ρ) + eE j ρ`
  - `weight_sum_eq : Σ_i ν j ρ i = [ρ∈TT]·aT ρ + k·w j ρ + δ j ρ`
  - `p22 : |pq j − k| ≤ m`, `p23 : |logOm| ≤ La`
  - `sE`/`sδ`: eE ≤ C0(w + S + Nn² + m(tt+1)η)La; |δ| ≤ C0(w + k(Nn+S) + …).
- Derived (:188–200):
  - `hA = −Σ_{t∈TT} aT·logT + Ch(…)La`
  - `hB j = Σ_ρ(Σ_i ph ν − (Σ_i ν)·logOm) + Ch f Nn²(La + m³L)`
  - `hX j = Σ_ρ logH − Ch f nV² Lp`
  - `hu = hA + Σ_j(hB j − hX j)`
  - `rhs = Σ_{t∈TT}(m(ph aT − aT·logOm) − aT·logT) + (50C0+10)|TT|·a·La + 60·ce·m·x^ε(B0+Nc)`.

**The concrete instance** `RecNums.ofNum` (DV/NumbersLink.lean:541) **read**:
- The two constraints hold by definition: eE := Σph(ν) − logHook − [top]ph(aT) (`eEN`, :35) and δ := Σν − [top]aT − k·w (`dN`, :38).
- The content therefore sits in `sE`/`sδ`, proved by `stepE_num` (:388) from `rowsStepEOrigin`. The constraints are not vacuous. **proved-by**
- `logH := logHook = log hookProd(apDiag)` is the hook product of the Young diagram with rows ⌊aPlus⌋ (DV/Numbers.lean:245).
- `pq j := (k + j − 1) − (m − j)` equals sigW j.1 − sigW j.2, where `Ranks.sigW j = (k + j − 1, m − j)` (`Formalism/LocalRingCardinality/Params.lean:46`). That sigW is the signature (p_j, q_j) of W_j is *inferred*.
- `logOm := γ + log(π/v) − Re L′/L(1, (·/d))`, with v = rd/2 (Numbers.lean:56–68).

**The DIV clause** (`divClausesR_of`, DV/ConstantGeTwentyEight.lean:184) **proved-by**:
- Clause 3 of `DivClausesR` (:111) is `muCC − meanLog κ + R.hu − 2·FoOfR ≤ R.rhs`.
- `BoundsMu` gives μ(R_base^∨) ≤ meanLog κ + Σ_j l3_j + 2Fo + LG + Σ(E1+E2) + E3. `passage` moves the bound to the cols level. `L3main` gives Σ l3_j ≤ Σ_jΣ_ρ pq_j·w·logOm + El3.
- `R.divIneq` (DV/DivisionHeightBoundStatement.lean:131) then applies `divIneqRecord` (`QuotientMetricDivisors/ScalarLiftLowerBoundFull.lean:52`; proved by `divisor_inequality_explicit`).
- The height: `height_chain_atR` (:123) and `HtNums.le_hu` (:113) give mean log‖B_u‖² ≤ hPn + Σ_j mean_s sz − Σ_j l6_j − meanLog κ ≤ hu − meanLog κ.
- The κ of ΘΘ* = κ∏λ appears with opposite signs in `BoundsMu` and in the height, and cancels.
- 2·FoOfR is the family's Fo, which arrives through the `ON` bound on idx_w(M_j, θ_jT_j) (IF/IndefSide.lean:318). The same F shifts N_u (`sg = Σ_j(gainD + F − E)`), so Fo cancels against `SlopesN`. *inferred*

**The arithmetic, line by line** (my algebra on `DivIneqRecord`'s hypotheses; the proof of `divisor_inequality_explicit` was not read). *inferred*
- (i) μ_C + hu − 2Fo ≤ [Σ_jΣ_ρ pq_j w_jρ logOm + Eb + Lpass] + [hP + Σ_j hK_j − mlam].
- (ii) Kernel: hK_j ≤ Σ_ρ(Σ_i ph ν_jρi − (Σ_i ν_jρi)·logOm) + eK_j.
- (iii) Eigenvalue: mlam ≥ Σ_jΣ_ρ logH_jρ − e6.
- (iv) Last map: hP ≤ −Σ_{t∈TT} a_t·logT + eP.
- (v)+(vi) per (j,ρ): pq_j w logOm + Σph ν − (Σν)logOm − logH ≤ [ρ∈TT](ph(a_ρ) − a_ρ logOm) + (pq_j − k)·w·logOm − δ·logOm + eE.
- Summing over the m steps leaves Σ_t[m(ph a_t − a_t logOm) − a_t logT].
- The remainder includes Σ_j(pq_j − k)Σ_ρ w logOm. Its size is at most m·m·f·2b·La, inside 60·ce·m·x^ε(B0+Nc) because B0 = f·m·b·x^ε.

## 2. Where each piece comes from

### Kernel: a! and Ω

- `HtNums.sz = liftedMapLogSize` (`Formalism/ThetaSupremumBounds/DivIneqExplicit6.lean:15`) has leading term Σ_τ(Σ_i ph ν − (Σν)·logOmτ τ s). Field `i1` (Inputs.lean:264) requires mean_s logOmτ τ s = R.logOm. **read**
- On the path, `HtNums` comes from `kerSide_chainS` (DP/KernelHalfChainNumbersAnyLevelPrime.lean:219). The chain is `rowsBody_colFace` (DP/ColumnsMemberRowsOfLogLevelLe.lean:25) ← … ← `kernel_columns_from_ties_alt` (TPS/RowsUOfColPinsStatement.lean:13, called at TPS/PointEvaluationSide.lean:53) ← `DefiniteSideCondition`. **proved-by**
- The per-step bound is `StepBound_sq` with `kernelBound_sq`/`liftBound_sq` (`DivisorBase/TopPlaceLogTheta.lean:17,174`): ‖step φ‖²_v ≤ exp(Σ_z[Σ_i ph(ν) − (Σν)·logOmAt(ρ,z)] + lower order)·‖φ‖²_v. **read**
- `BlockBound` (`DivisorBase/PaddedWittNormSquare.lean:36`) **read**:
  - G is entire with ‖G(z)‖ ≤ S·exp(Σ|r z|²/2), and |c_τ r_τ|² = 1/Ω_τ.
  - Then the jet operator from the weight-λ to the weight-λ′ polynomial model has Fock-norm² ≤ S²∏_τ Ω_τ^{−|ν_τ|}·e·(2|ν_τ|+2)^{2ab}·exp(Σ_i ph(ν_τ,i)) (`tmax`, :32).
  - Proved in-tree by `blockBound` (DP/NormFockLSqLe.lean:262). That proof was not read.
- So a jet of weight ν costs ∏ν_i! (ph(u) ≈ log u! by Stirling) times Ω^{−|ν|}. That is the Cauchy estimate in the Bargmann–Fock norm. *inferred*
- Ω **read**:
  - `logOmAt ρ τ = −logMet(M, Λ, ρ, c_τ)` (TopPlaceLogTheta.lean:49).
  - `logMet = log(π|ρ s|²/area(Λ^ρ))` (`…/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean:157`).
  - Λ = δ·φ₀(𝔠) with δ¹² = Δ(φ₀(𝔠)), a unit-discriminant CM lattice (:53; `ccK = ⊤` on the path).
  - Hence Ω_ρ,τ = area(Λ^ρ)/(π|ρ(c_τ)|²), with c_τ a generator (`IsDgen`).
- The mean over embeddings ρ of the coefficient field M is supplied by `mean_logMet_eq` (DP/MeanLogMetricGeneratorEqMeanPeriod.lean:45) and `meanPeriod` (DP/MeanLogPeriodChowlaSelberg.lean:84). The latter uses `mean_log_period`: mean_ρ log(area(Λ^ρ)/π) = γ + log(2π/√d) − L′/L(1,χ_d). Together they give `logOmVal = γ + log(π/v) − Re L′/L(1,χ_d)`. **proved-by**
- In `kerSide_of_meansS`, the place-wise logOmτ z v = Σ_a wt(v,a)·logOmAt(a,z) is an average over the embeddings above v. **read**

### Eigenvalue: hook products

- `L6` (IF/IndefSide.lean:326): l6_j ≤ log λ_j(μ0,p,v) for all p, v. Here l6_j = Σ_ρ logHook_jρ − Csz·f·nV²·Lp (`ZscOfNum`, DV/ZscOfNum.lean:59; adjusted by `ZscAt`, `Formalism/LocalToGlobal/IndefiniteRealisationChoice.lean:61`). **read**
- `lamLow_of_classicalTheorems` (DP/LamLowOfPublished.lean:30) → `lamLow_closing` → `lamLow_of_weak` → `lowTop_ofCore` (DP/LiftAdjointEigenvalueLowerBoundBaseEmbedding.lean:161) **proved-by**:
  - `LowTop` (DD/RealisedChainTorusEq.lean:98): every eigenvalue l of θθ* at the base embedding satisfies lowB ≤ log l, with lowB = hookPlus − 8f·nV²·Lp (:95).
  - `main_le_lowB` ties NumDatum's `logHook` to lowB.
  - Published inputs: CuspRapidDecay, WeilSiegelFormulaUnitary, SiegelWeilUnitaryConvergent, DoublingMethod, UnramifiedDoublingGL, BernsteinZelevinskyFiniteness, FormalDegreeCompactDual.
- `AdelC` (DD/FormalDegreeUpperC.lean:24) **read**:
  - θ∘adj acts on each type-part by l > 0, with mainTerm − 8f·nV²·Lp ≤ log l.
  - mainTerm = Σ_ρ log(hookOf(p_ρ,a⁺)·hookOf(q_ρ,a⁻)) (`DivisorBase/TwistedLevelValues.lean:55`).
  - `FiniteZetaC` (same file) states the inner-product identity with factor eulerOff/dOff. eulerOff = ∏(1 − x_w,a)⁻¹ with |x| ≤ N(w)^{(r−1)/2 − (1+t)/2}. dOff = ∏_v∏_{t<i≤nV}(1 − χ(v)^i N(v)^{−i})⁻¹ (DP/InnerProductFormula.lean:54–57).
- As an exact identity, `AForm` (`Definitions/TwistedInnerProducts/RealLowestKTypeCoeffSquareIntegrable.lean:42`) says θ_jθ_j* = a_j·z on each Hecke part, where `IsLValue` (`BlockTheory/TwistedDiscreteSeries/LabelSettingScalars.lean:30`) requires z = L^S((1+t)/2, c ⊗ μ_j⁻¹), convergent and positive. **read**
- An L-value thus appears, but at a point of absolute convergence; no central or special value is computed. *inferred*
- The cancellation of factorials **read**:
  - `RowsStepEOrigin` (`QuotientMetricDivisors/TheoremDivIneqRowsShift.lean:129`) and `IsRowsTop`/`RowsFactorial` (`…/TheoremDivIneqRows.lean:25,34`).
  - At a top place the jet rows are {a+w, r0 ≤ w, w+c_i, block}. The target rows are ≈ {w+c′_i}, with c′ interlacing c.
  - Then Σph(ν) − Σ log(ap_i!) ≤ ph(a) + O((w + S + n·sh + Bl)·La).
  - `RowsHook` (:52) gives log hookProd ≥ Σ log(row!).
- Interlacing pairs every source row with a target row of nearly equal length except the long one. The eigenvalue therefore repays every factorial but a!. The long row recurs at every step because the top entry u₀ = a + (k−1)/2 of `srcPar` does not depend on j. *inferred*

### M_j: covolume

- `L3` (IF/IndefSide.lean:316): lcv(XW_j, M_j)/D ≤ l3_j, with l3_j = Σ_ρ pq_j·w_jρ·logOm + C·B0·log log x (ZscOfNum.lean:59). **read**
- In the realisation, `RecAt` (DD/CovolXOfCovol.lean:57) gives lcv/D ≤ −slope(latGood). Here latGood is the type-P part of the integral span of `(R.FW i).MK`, cut by the good idempotent (DD/NormNegCmConstantEqAtAllEmbeddings.lean:44). `MeasAt` (:81) identifies its norm with c·(Petersson norm) on algebraic cusp forms `cuspA (i+1) (wtA κ_i)`. **read**
- *inferred*: M_j is a Petersson-normed lattice of algebraic cusp forms of weight κ_j on the unitary group of W_j, of signature (k+j−1, m−j).
- The bound runs through `CoreAt`/`LowAt` (−mainT − C·unitE ≤ muCore, :92,96) and `AnchorAt` (mainT ≈ Σ_τ(p−q)·anchor_τ·logOm, :98). It also uses the flat-line degree `flatDegVal = (p−q)/2·logOm + q(log d − lrd E)` (`Definitions/Foundations/ExistsFlatSecRankZero.lean:751`); `flatDeg : ScholzeWeinsteinB → Hypotheses2 → FlatDeg`. **read**
- So Ω enters M_j because Petersson norms of weight-w forms scale like Ω^{(p−q)w}. *inferred*
- At the top level, the covolume bound is a hypothesis: `CovolumeBoundOfX`, an input of `nonempty_hyps_definite_side_of_closed_bound` (TPS/SiegelEisensteinSecondTermHypotheses.lean:44). **read**

### Last map: −a·log T

- `LastMapNorm` (`DivisorBase/OrthogonalNormSquareSum.lean:48`) **read**:
  - The branching map from U(N) weight λ to U(N−1) weight σ runs along a coordinate whose Gram entry g has t̄gt = T.
  - Its squared operator norm is exactly T^{−Σ nBr}·∏cBr²·kapBr, with nBr = |λ| − |σ| (`Formalism/LocalToGlobal/Columns/FiniteSumNonzeroLargeDepth.lean:57`).
- `lastSide_of_logT_le` (DP/LastMapHalfRecNumsOfLogLevelPrimeLe.lean:14) sets lam1 = aT − m(t+1)/2 at top places. So Σ nBr ≥ Σ_t a_t − O(…), which gives `t1`/`t5` (Inputs.lean:284,292). **proved-by**

## 3. ThmAop, ThmBop, BForm

**The statements** (IR/CutTuples2.lean:99,128) **read**:
- `ThmBop`: ∀ t p, ∀ e ∈ EEp p ⊓ EEl b, Θ_t(Θ_t* e) = (κ(v0)·∏_j λ_j(t,p,v0))·e.
- `ThmAop`: ∀ j t p, ∀ w ∈ Wp j p ⊓ range(w0C b j), θ′_jt(θ′_jt* w) = λ_j(t,p,v0)·w.

**The chain** **proved-by**:
- `thmBop_of`/`thmAop_of` (IR/BaseLiftsPackageOfPrimitiveLinks.lean:175,184) take `PThmB`/`PThmA` (:68,71), fields of `PrimRows3`.
- `PThmB` ← `pThmB_short` (`DecoratedLatticeProofs/ThetaLiftSecondHypotheses.lean:37`) ← `scal_matchUp_upInj` (`…/ThetaLiftScalarIdentityMatchingAdjointInjective.lean:35`) ← `scal_of_aForm_bForm` (`TwistedOperators/ScalOfAFormBForm.lean:26`).
- `scal_of_aForm_bForm` sets λ_j := a_j·z_j and κ := κ₀/∏a_j. It then uses `BForm` (ΘΘ* = κ₀∏z_j on EEc, RealLowestKTypeCoeffSquareIntegrable.lean:46).
- `AForm` is proved by `thetaInnerProduct_eq_const_mul_LValue`.
- Published inputs: DiscreteSeriesCover, HarishChandraFinite/Modules, CasselmanWallach, CuspRapidDecay, HoweUnram, WeilSiegelFormulaUnitary, SiegelEisensteinContinuation, UnramifiedDoublingGL, BernsteinZelevinskyFiniteness.

**Reading.** *inferred*
- These are Rallis inner-product identities via Siegel–Weil and doubling, with unramified Howe duality. `BForm` is the same identity as `ThmBop`.
- The L-values z_j cancel identically in the determinant identity. The height needs only lower bounds on λ_j.

## 4. What DIVinN controls

**The statements** (`Formalism/SharpRestriction/GlobalTheoremInputs.lean:40–63`) **read**:
- `LinkN_at`: etaSum L j ≤ dZ0_j·(C(f·m·b·L² + log²x·Nc) + Σ′_ℓ vvTerm ℓ), where vvTerm ℓ = (Σ_{1≤e<t} shaLen(ℓ,e))·log ℓ.
- `DIVinN_at`: etaSum ≤ D0·C·x^ε(B0+Nc).
- `divinN_of_hypV` (`Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:117`) uses Σ′vvTerm ≤ √b ≤ b. The square root is slack. **proved-by**

**Where the content is consumed.**
- `DIVinN_at` occurs in exactly five files under `Formalism/` and `Development/`. They are:
  - its definition;
  - its producer, `DivinNOfHypV.lean`;
  - the two `InpAtOf.lean` copies, which pass it to `inEta3_num` (`Formalism/LocalToGlobal/InpAtOf.lean:46`);
  - `SumLeEtaSumNum.lean`, which unfolds it in `inEta_num` (DV/SumLeEtaSumNum.lean:60). **read**
- No other directory under `src/` mentions DIVinN. **read**
- The other files naming `etaSum` define it or prove upper bounds on it; none consumes a bound on it. They are:
  - `LevelLetterCocycles/`;
  - `ResidueCharacters/TwistedPlaces.lean`;
  - `HeckeGaloisCriteria/EvPowLeExp.lean`;
  - `AdicCompletionExports/NonnegativeDivisors/Statement.lean`. **read**
- `inEta_num` yields `InEta` (DV/LiftLat.lean:251): Σ_w lw·etaJW ≤ bd·D, with etaJW = len_w(T_j/cutZ_j) (:116).
- That feeds `borderedMinorImage` (E2) and `biv` (`lift_index_bound_extended`, DV/TwistedPlaceEtaSumLeExtended.lean:30): jw_w(HZ_j, T_j) ≤ ramw·J0·D + etaJW + D(vw(DG) + vw(s)). Here jw = lidx(T, T^∨) (`Formalism/HermitianLattices/StatementLat.lean:98`). **proved-by**
- So the Sha bound pays for the discriminant (non-unimodularity) of the Hermitian form on the lift level lattices T_j at twisted primes, the third local term of `BoundsMu`. *inferred*

**(a) ON** **proved-by**:
- `SurjectiveOntoX` (TPS/ExportSt.lean:47) takes DIVinN as a premise.
- Its proofs `onto_path_alt` (TPS/OntoPath.lean:18) and `onto_path` (DP/SurjectivityFromAllEstimates.lean:24) run `intro eps Fm CH _ H _`. `Closed.imp` (`Formalism/SharpRestriction/ParamsHeightRankConstant.lean:173`) binds 0<eps, the estimates, and then the DIVinN premise, which is never used.
- On these routes, the index of θ_j T_j in M_j is bounded by F (`FjP`) and page and twist estimates.

**(b) FUN.**
- The leaves of `Fun0Fit` (DD/TwistedPlaceChoiceLiesOverPair.lean:306) carry DIVinN by definition of `Lf` (:252). **read**
- The one leaf read, `desHLeaf` (DP/ZetaDenominatorsFitFunction.lean:117), discards it. **proved-by**
- Given the search above, FUN does not use the Sha bound. *inferred* This corrects frame-and-glue §2.6.

**The Galois mechanism.**
- `etaSum_le`/`etaAt_le` (`Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean:558,57`): per prime ℓ, etaJ ≤ Σ_π mult·(vcc + v_ℓ|G|) ≤ dZ0·[σ(ℓ) + λG(ℓ) + Σ_e shaLen(ℓ,e) + v_ℓ(h_E) + v_ℓ|G|]. **proved-by**
- `vcc` (`Formalism/CharacterColumnKernels/StatementN.lean:18`) is the valuation at a point of the congruence ideal ker(T → functions off Z) of a Hecke-type algebra. **read**
- `CharacterColumnKernelEqualityForm.lean:246` bounds vcc by local H¹ terms + Σ_{0<e<t} Sha(e) + vhE, using cocycles Ψ of a block-restricted representation. **read** That is a congruence-module bound, not a Bloch–Kato formula. *inferred*

## 5. Check against the analytic side

- The family MAIN and logOm are defined in `Formalism/LocalRingCardinality/DataParams₂.lean:224,232`. **read**
- `Data` is defined in `Formalism/RankGapBounds/MeanBoundSecondForm.lean` (logOm :88, Main :107, DIV :118, HComp :126, HHBound :158). `EComp5` and `Count5` are in `Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean:24,27`. **read**
- `Mod.data` (`Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean:464`) sets gam := γ, LpL := L.logDerivativeAtOne, v := host.v and lg := log(g0 g1). `logOm_eq` (:556) and `main_eq` (:561) make the family MAIN literally the right side of `DIV`. **read**
- `key_identity` (`Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean:170`) and `key_identity5` (`Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:105`): SDiv − sumA·Lam5 + m·sumA·lg = Main(u0) + sumA·cCount(La + m²La/k), exactly. Here Lam5 is `Count5`'s lower bound for log T. **proved-by**
  - It uses log(π/v) = log π − log v and log(w v/π) = log w + log v − log π.
  - The m·sumA·lg term is matched by `EComp5` (Ee ≈ m·sumA·lg) in `s_lower5`.
- `ch_top_main_eq` (`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean:11`): Main(u0) = Σ_{t∈TT}Σ_j Re MAIN(ell, a_t, w_j), with MAIN as in `Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:89`. **proved-by**
  - The ties are `Ident` (`Formalism/SizeWindowBrackets/SChain.lean:26`) and `Char_at` (QuadraticLogDerivCongr.lean:221). `Char_at` gives L.logDerivativeAtOne = Re ell(chC) and ell ψ = L′/L(1,χ) for the primitive χ attached to ψ ≠ 0. **read**
- **Verdict:** identical. There is no discrepancy term beyond the stated errors: the Count5 slack, cE·m·B0, the cDiv terms, and the (pq_j − k) and δ remainders. **proved-by**

## Not read

- The proofs of `blockBound` (the Fock–Cauchy estimate) and of `norms_matrixSteps_coupledFactor_bounded_anyLevelPrime`, which gives the Gaussian growth S of the CM theta kernel.
- `young_diagram_step_origin` and `young_diagram_hook`.
- `divisor_inequality_explicit`, `height_bound_at_set`, `stepDiiiRecord`.
- The proofs behind `AdelC`/`AdelicLiftScalar`: the archimedean computation that gives hook products, and the formal-degree bound. Also `thetaInnerProduct_eq_const_mul_LValue` and `bForm`.
- `brNorm` (LastMapNorm).
- The `CovolX` chain: Deep covers, `SumAt`, the use of Scholze–Weinstein B in `flatDeg`. Also the supplier of `CovolumeBoundOfX`.
- The FUN leaves other than `desHLeaf`.
- The `adm1`/`AdmT` clauses and the cocycle construction behind the vcc ≤ Sha bound.
- The supplier of `CharF`.
- Which top-level entry point the whole chain is reached from (`everyE₂` has no callers).
