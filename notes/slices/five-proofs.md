# Five proofs: the packaged divisor inequality, the Fock bound, the covolume of M_j, EigPd, goodR_fold

Read 2026-11-20 from the source text only; nothing was built or edited. **read**

Paths are under `lean/src/`. QMD = `Formalism/QuotientMetricDivisors/`, HTD = QMD`HermitianTwistDivisors/`, DV = `Formalism/LocalToGlobal/Divisibility/`, DP = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/`, TSB = `Formalism/ThetaSupremumBounds/`, GSB = TSB`GaussianShiftBounds/`, TPS = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`, DD = `Development/AbelianVarietyTheory/Definitions/Divisors/`, IRL = `Formalism/LocalToGlobal/IndefiniteReal/`, TC = `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/`, LLC = `Formalism/SharpRestriction/LevelLetterCocycles/`.

Tags: **read** = statement or definition transcribed; **proved-by** = proof body read, inputs named; *inferred* = my interpretation.

## Verdicts

| Item | Verdict |
|---|---|
| 1 | The slice's algebra is confirmed term by term. Inside the record the kernel, eigenvalue and last-map bounds hold by definition at the call site; the eigenvalue bound and the covolume are consumed before the record. **proved-by** |
| 2 | It is not a Cauchy integral. It is the Fock reproducing identity, a singular-value bound, a one-variable maximisation (the source of exp ph(ν) ≈ ν!) and one Gaussian integral. **proved-by** |
| 3 | M_j is a lattice of integral forms. Its covolume is bounded by Arakelov slope estimates, with no Minkowski bound, mass formula or theta normalisation. **proved-by** log Ω enters as the degree of a flat line bundle. *inferred* |
| 4 | EigPd uses RelU's `ine`/`mono` at the pde place, RelW's `eq_of_unr` at split places, Chebotarev, and the order-15 design. **proved-by** |
| 5 | goodR_fold is list induction on goodR_sum. Nc of a sum descends to the summands because the square-free threshold is antitone. **proved-by** |

## 1. The packaged divisor inequality

**Answer.** `DivIneqRecord` (QMD/ScalarLiftLowerBoundFull.lean:52) is closed real arithmetic, proved by an exact cancellation lemma plus an error-absorption lemma. **proved-by** The slice's cancellation is right. **proved-by**

**Chain.**
- `divIneqRecord := divisor_inequality_explicit` (QMD/SixthReductionExplicit.lean:9) `:= divIneqRecord_of divisor_inequality` (HTD/GlobalBoundRefinements.lean:91). **read**
- `divIneqRecord_of` (:63) instantiates `TheoremDivIneq` (QMD/StatementK.lean:11) with Nc ↦ (log x)²Nc/x^ε, xe ↦ (ce/C0)x^ε, dC ↦ 1, lam0 ↦ m·lam0. **proved-by** `constant_factor_le_sixty` (:58) turns (50C0+10)(ce/C0) into 60ce. **proved-by**
- `divisor_inequality` (HTD/TheoremDivIneq.lean:12) is `divisor_inequality_assembly` with its κ slot set to 0, plus `error_absorption`, closed by `linarith`. **proved-by**

**Which hypothesis gives which term** (`divisor_inequality_assembly`, HTD/DivAssembly.lean:11; `DivAssembly`, QMD/StatementJ.lean:56). Here ph(u) = u·log u − u (Formalism/LogFactorialIndices/StatementSize.lean:7). **read**
- h1 `muC ≤ mu0 + Lpass` is the passage error. **read**
- h2 `mu0 ≤ ΣjΣρ pq_j·w_jρ·logOm + 2Fo + Eb` is the covolume's credit. **read**
- h3 `hu = hP + Σ hK_j − mlam`. **read**
- h4 (kernel) `hK_j ≤ Σρ(phν − nν·logOm) + eK_j`. **read**
- h5 (eigenvalue) `ΣΣ fa − e6 ≤ mlam`. **read**
- h6 (last map) `hP ≤ −Σ_{t∈TT} a_t·logT + eP`. **read**
- h7 `phν − fa ≤ [ρ∈TT]ph(a_ρ) + eE` and h8 `nν = [ρ∈TT]a_ρ + k·w + δ`. **read**
- `hpt` (:14) substitutes h8 into h7 at each (j, ρ). **proved-by** It gets pq·w·logOm + phν − fa − nν·logOm ≤ [ρ∈TT](ph a_ρ − a_ρ logOm) + eE + |pq_j−k||w||logOm| + |δ||logOm|. **proved-by**
- The top term does not depend on j, so the j-sum gives m·Σ_t(ph a_t − a_t logOm) (`hite` :29, `hTT` :38). **proved-by** With h6 this is Σ_t[m(ph a_t − a_t logOm) − a_t logT]. **proved-by**

**Errors** (`error_absorption`, HTD/AbsorbE.lean:26), with T = m(B0+Nc)·xe.
- Lpass ≤ (1+C0)T, Eb ≤ C0T, ΣeK ≤ 5C0T, e6 ≤ 3C0T, ΣΣeE ≤ 15C0T. **proved-by**
- The (pq_j − k) remainder is ≤ m·f·m·2b·3L = 6m·B0 ≤ 6T (`hpqs` :137), via |logOm| ≤ La ≤ 3L. **proved-by** The slice wrote La where the proof needs 3L. **proved-by**
- The δ remainder (:158) and eP each cost C0·|TT|·a·La, through m·k·b′ ≤ a and b′N ≤ a. **proved-by**

**Correction: where the analysis enters.**
- At the one call site, `RecNums.divIneq` (DV/DivisionHeightBoundStatement.lean:131), h4–h6 close by `le_refl`/`simp`. **proved-by** hB, hX and hA are defined to be those budgets (DV/Inputs.lean:188–198). **read**
- The eigenvalue bound is spent in the height clause. **proved-by** `height_chain_atR` (DV/ConstantGeTwentyEight.lean:123) bounds Σ_j l6_j by the minimum over Hecke pieces of Σ_j log λ_j (:160). **proved-by** `HtNums.le_hu` with `I.eig6` (:206) carries it to hu. **proved-by**
- The covolume of M_j enters only through h2. **proved-by** `divClausesR_of` (:184) builds h2 as `hM` (:240) from `BoundsMu` (:211), which contains Σ_j l3_j, and from `L3main`. **proved-by**
- κ cancels because muC and mu0 are defined with −meanLog κ (:218), against −log κ_v in the height. **proved-by**

## 2. The Fock-norm estimate

**Answer.** `BlockBound` bounds a jet operator between tensor products of dual Weyl modules, realised as polynomials in matrix variables. **read** The norm is the Fock norm Σ|c_m|²m!, divided by that of the extremal vector. **read** The bound is S²·∏_τ Ω_τ^{−|ν_τ|}·e·(2|ν_τ|+2)^{2ab}·exp(Σ_i ph(ν_τ,i)). **read** The proof writes the jet functional as a Gaussian integral of the kernel G against a polynomial and bounds the integrand pointwise. **proved-by** exp(ph(ν)) is the exact maximum of (s^ν e^{−s²/2})². *inferred* Stirling is needed only to read ph(a) as log a!. *inferred*

**Statement** (Development/AbelianVarietyTheory/BlockTheory/DivisorBase/PaddedWittNormSquare.lean). **read**
- `VV λ` = ⊗_τ nablaSq(n, λ_τ), in polynomials with one n×n matrix of variables per τ (DV/CoefMod.lean:67). **read**
- `normSq λ v` (:22) = Re fockS(v,v)/∏_τ fockS(e_τ,e_τ), with fockS(f,g) = Σ_m conj(f_m)g_m·m!. **proved-by** (CoefMod.lean:21, :160–171; `normSq_eq`, DP/NormFockLSqLe.lean:71.)
- `jetOp λ λ′ J n` multiplies by ∏_τ det(X_τ)^{n_τ}, substitutes X_τ = Z_τᵀY_τ, replaces each Z-monomial Z^m by J(m), and retracts onto VV λ′. **read** (Formalism/LocalToGlobal/KernelLattices/ThDistC.lean:23–37.)
- J(m) = `jetC cD G m` = ∏cD_τ^{m}·∂^mG(0) (:60). **read** Since fockS(Z^m, G) = ∂^mG(0), the operator is the Fock pairing with G. *inferred*
- The weights satisfy ν = λ + s′ ≥ 0 and λ′ + s = ν padded with zeros, with a ≤ b and (a < b or ν's last entry 0) (`IsStepWeight` :15). **read**
- G is entire with ‖G(z)‖ ≤ S·exp(Σ|r_τz|²/2), and |cD_τr_τ|² = 1/Ω_τ (`BlockBound` :36, `tmax` :32). **read**

**Proof.**
- `blockBound` (DP/NormFockLSqLe.lean:262) shows the jet image already lies in VV λ′ (`subOne_mem` :120). **proved-by** It then bounds the functional φ = D^{−1/2}⟨w,·⟩_Fock. **proved-by**
- The pointwise input is `fock_subst_le` (DP/FockSubstLe.lean:119). **proved-by** Substituting A ∈ Mat_{a×b} with singular values t multiplies the Fock norm on the dual Weyl module of ν by at most ∏t_i^{ν_i}. **proved-by** The proof uses the spectral theorem (`exists_sing` :58) and monomial dominance (`dominance` :102). **proved-by**
- Cauchy–Schwarz (`norm_fockL_sq_le` :25) and `fock_tensor_le` (:39) turn this into |φ(v at A)| ≤ ∏t_i^{ν_i}. **proved-by**
- `scalar_block` (:198) rescales z = u/r and applies `Formalism.DimensionVariation.blockBound` (TSB/LiftOperatorBoundOfFockJet.lean:28). **proved-by** That is `blockBound_of FockJet BlockIntegral` (GSB/HeightsoundOf.lean:11). **proved-by**
- `FockJet` (TSB/StatementA.lean:41): ∫F(u)·conj(u)^e·e^{−|u|²}du = π^d·c_e·e!. **read** It is proved from ∫|z|^{2n}e^{−|z|²} = π·n! (`fjW_diag`, GSB/FockJet.lean:55) and orthogonality by rotation (`fjOrth` :85). **proved-by** Polydisc cut-offs with dominated convergence finish it (`fjPolydisc` :263, `gaussianCoeffIntegral` :318). **proved-by**
- Each monomial has degree |ν_τ| in the τ variables, so the jet scaling factors out with squared size ∏Ω_τ^{−|ν_τ|}. **proved-by**
- `blockIntegral_of` (GSB/BlockIntegralOf.lean:96) bounds the integrand by S·∏_τ∏_i s_i^{ν_i}e^{−|u_τ|²/2}. **proved-by**
- `placeBound` (:35) splits e^{−Q/2} as e^{−aQ/2}·e^{−Q/(2(N+1))}, with a = 1 − 1/(N+1) and N = |ν|. **proved-by** It bounds s^ν e^{−as²/2} ≤ e^{ph(ν)/2}e^{−ν log a/2} from log y ≤ y−1 (:12), and uses −N log a ≤ 1. **proved-by**
- The leftover Gaussian integrates to π^d(2N+2)^{|ι|} (`gaussianIntegralDiagonal`, GSB/GaussCoord.lean:34). **proved-by**
- On the path, `kerSide_chainS` uses it as `blockBound_iff.1 JetBlock.blockBound` (DP/KernelHalfChainNumbersAnyLevelPrime.lean:221; DP/WeightSequenceGuards.lean:73). **read**

## 3. The covolume of M_j

**Answer.** M_j is, in coordinates, a lattice of integral forms from the space the tree calls `cuspA`, of weight κ_j on the moduli space `Xo (j)`. **read** That these are cusp forms on a unitary Shimura variety is *inferred*. The proved bound is lcv(XW_j, M_j)/D ≤ mainT_j + C·unitE. **proved-by** On the DIV scale, mainT_j = Σ_ρ((k+j−1) − (m−j))·w_jρ·logOm and unitE = B0·log log x (DV/ZscOfNum.lean:64, :66). **read** It is *inferred* that this is the scale on the path, and that k+j−1, m−j is the signature. The proof is Arakelov geometry. **proved-by**

**What M_j is.**
- `p.S b := (p.R.toCx3 p.F).data p.F.cr b` (DD/TupleReadBaseTupleEqFamily.lean:290). **read**
- `M b i := (R.FW i).Mcoord P ψ⁻¹ (idempotent) (bL F b i)` (IRL/ZeroPartEigenvalueConvention.lean:136). **read**
- `Mcoord` (IRL/GramCEqTranspose.lean:133) gives coordinates in the basis bL of `Mj = Mall ⊓ range eOp` (:96). **read** Here `Mall = span𝒪(MK) ⊓ typeP P ψ⁻¹` (:93). **read**
- `MK` (:54) is the set of f ∈ WK with nrm(y, f) ≤ 1 at every local point over every finite place. **read** That is non-negative valuation at every point (`nrmM_le_one_iff`, Formalism/LocalToGlobal/ProjectiveLattices/CuspidalL2Subspace.lean:55). **read**
- WK ≅ `cuspA (i+1) (wtA κ_i)` on `Xo (i+1)` (`FWTie.e`, IRL/FWTie.lean:22; `cuspA`, CuspidalL2Subspace.lean:47). **read** κ_i is pinned to `sigW (i+1)` (`kap` :26). **read**
- The metric is ‖j_σ f‖ (`nrmR`, DD/NormNegCmConstantEqAtAllEmbeddings.lean:31). **read** The hypothesis `MeasAt` equates it with c·Petersson, |log c| ≤ C·unitE (DD/CovolXOfCovol.lean:81). **read**
- M_j is latGood (:44) in coordinates; the proof of RecAt passes `hp.prim.mLat i` for this slot (TPS/RecAtOfGramAt.lean:17). *inferred*

**Path.**
- `CovolumeBoundOfX` (TPS/LiftLambdaBound.lean:60) asks for `L3` (Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean:315) eventually. **read** Its target is mainT + C·unitE (`show`, TPS/CovolXOfSteps.lean:38). **proved-by**
- `riemannHypothesis` (Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:13) → `every_character_of_literature_of_vWin` (TPS/EveryCharacterOfLiteratureOfVWin.lean:810). **read** That theorem passes `topCovolSlim2_use_alt_alt …` (:812) to `every_character_of_theta_integrals_local_matching` (TPS/SiegelEisensteinSecondTermHypotheses.lean:69). **read**
- `topCovolSlim2_use_alt_alt` (TPS/TopCovolSlim2Use.lean:16) → `topCovolG_alt_alt` (TPS/TopCovolG.lean:39) → `covolX_of_lift_bounds_and_coreLe` (TPS/CovolXOfSteps.lean:16) → `lcv_le` (DP/CovolumeFromGramAndBounds.lean:39). **proved-by**

**Proof.**
- `lcv_le` chains four steps. **proved-by** RecAt gives lcv/D ≤ −slope(latGood); Cut, Bad and Lam give slope(latGood) ≥ slope(latType) − tiny; CoreAt gives slope(latType) ≥ muCore − C1·unitE; LowAt gives muCore ≥ −mainT − C2·unitE. **proved-by**
- RecAt is `covolumePerRank_le_neg_slope_scaled` with scale 1/√nP ≤ 1. **proved-by**
- LowAt comes from `low_of_cover_hypotheses` (TPS/LowOfCoverHypotheses.lean:17). **proved-by** Below the top level it picks a deeper-level cover Y and applies `lowAt_of_cover` (DP/LowerBoundOfAllEstimates.lean:65). **proved-by**
- FlatAt and UAt give the weight-Gs(−c₀) forms on Y slope ≥ −mainT − (CF+CU)·unitE. **proved-by** Maps φ_h carry this into the deep lattice (`DescentFamily.descent`), and RingAt brings it to muCore (`numeric` :18). **proved-by**
- mainT enters only through FlatAt and AnchorAt. *inferred* AnchorAt: |mainT − Σ_τ(p−q)·anchor_τ·logOm| ≤ C·unitE (DD/CovolXOfCovol.lean:98). **read**
- `FlatDegree logOm` gives each flat section degree (p−q)/2·logOm + q(log d − lrd E) (Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFlatSecRankZero.lean:751, :754). **read** Multiplying by flat sections of weight w changes degree by Σ_τ w_τ·(−deg s_τ) (`shift_spec` :727). **read**
- `flatDeg_alt_alt` (TPS/FlatDegreeStatement.lean:12) supplies FlatDegree from `FlatDegreeSt` (DD/HtValOnSubset.lean:118), at logOm = Re `CM.logOm E χ`. **proved-by** Beside it, `CMDiffSt` (:108) states that the degrees of the τ and τ̄ eigen-lattices of a CM object differ by (p−q)/2·Re logOm. **read**
- UAt rests on Hilbert–Samuel and height statements on components (`HSAt` :153, `HeightAt` :146). **read**
- `topCovolSlim2_use_alt_alt` takes fifteen algebro-geometric statements. **read** They include resolution in characteristic 0, Moriwaki bigness, Fargues, Zarhin, nef Riemann–Roch, toroidal compactification and Grothendieck deformation. **read** On the path each comes from an in-tree theorem through a projection that ignores its argument (e.g. TPS/EveryCharacterOfLiteratureOfVWin.lean:549–560). **read**

## 4. `EigPd`

**Answer.** `EigPd D` (Development/AbelianVarietyTheory/Definitions/GaloisGeometry/HeckeCharEqOfLAdicRealisation.lean:118) concerns each w ∈ S_i above pde (pde′ when ℓ = pde). **read** For every residual ρ̄ there, χ̄₁(γ₀) is not a root of charpoly ρ̄(γ₀). **read** The lift's inertia eigenvalues are 1 and χ₁; removing the χ-part leaves ρ̄(γ₀) unipotent, while χ̄₁(γ₀) ≠ 1. **proved-by**

**Chain.** `prvG5_of_admissible_cutRec` (TPS/AdmissibleJOfRestricted.lean:28) sets `hEig := eigPd_holds_alt D hA.1.1 hLGC hRb` (:32) and uses it at :43. **read** `eigPd_holds_alt` (TPS/EigPdHolds.lean:17) discards the `RbEx` and `HG` hypotheses (`_`). **proved-by**
- `residue_ne_one` (Development/AbelianVarietyTheory/Proofs/SatakeParameters/EigenPeriodOfLocalGlobal.lean:84) proves χ̄₁(γ₀) ≠ 1. **proved-by** Otherwise χ̄₁ would kill γ₀ and wild inertia (pro-q, coprime to 15), hence all inertia. **proved-by** But χ₁(inertia) is cyclic of order 15 (`Del_holds`). **proved-by** A primitive 15th root of unity stays ≠ 1 mod ℓ because 15 is not a prime power. **proved-by**
- `isoRep` gives ρ with RelW to the base-change parameter (TC/GoodRCongr.lean:288). **proved-by** `heckeQ` (TC/SplitBCOfGalIso.lean:71) uses only `eq_of_unr`, at split places outside S, to get Frobenius = Hecke polynomials. **proved-by** `exists_GoodR` then uses `OLarge` to make it integral (LLC/ExistsInertiaCharpolyFactorOfTameType.lean:438). **proved-by**
- `hLGC` gives `LGCatN` at w: RelU = RelW + Nc against the twisted automorphic parameter (TC/TrivialLocalCondition.lean:16, :27; TPS/HeckeCharEqOfLAdicRealisation.lean:60). **read**
- `splitI_of_monodromyInertiaType_of_lgCatN` (TPS/GaloisClauseOfSufficient.lean:68) passes to `SplitI_of_TY` (TC/Bridge.lean:147), which reads only `hP.ine` and `hP.mono` (:161–163). **proved-by** With `MonodromyInertiaType` this gives charpoly r(γ) = (X−1)^r(X−χ₁γ)^t on inertia. **proved-by**
- `rhobar_fac` (LLC/ExistsInertiaCharpolyFactorOfTameType.lean:1145) uses Chebotarev to give charpoly r̄ = charpoly ρ̄·∏_c(X−χ̄_c). **proved-by** `character_eq_first_off_l` (:828) gives χ_c = χ₁ on inertia. **proved-by** Cancelling (X−χ̄₁)^t leaves (X−1)^r. **proved-by**
- Labels: in `AdmAAlt` (TPS/CuspidalGaloisUnramified.lean:35), the conjunct named `ArchimedeanSignatureMatching` is `MonodromyInertiaType` (LLC/SumRepresentations.lean:370). **read** `Cheb` is the third conjunct of the one named `JacquetShalikaStrongMultOne` (:323, :372). **read**

**Verdict.** The only Galois–automorphic compatibility consumed is RelU's `ine`/`mono` at w and RelW's `eq_of_unr` at split places. **proved-by** No other compatibility is used. **proved-by** That this RelW is itself built from `AwayB` is the open-hops slice's reading, not re-read here. *inferred*

## 5. `goodR_fold`

**Answer.** If every constituent in a nonempty list satisfies `GoodR'`, so does their direct sum (TC/GoodRCongr.lean:80). **read** Its rank is the sum, its parameter the iterated `lpSum`, its Hodge–Tate multiset the sum. **read**

**Definitions.**
- `GoodR' D i r p m` (:13) asks for a continuous semisimple ρ of rank r. **read** At every w ∤ ℓ, RelW(WD_w ρ, p w) holds. **read** At w | ℓ with Nc(p w), ρ is de Rham, `RelA` holds, and the Hodge–Tate jumps equal m. **read**
- `RelW x y` (TC/AutomorphicGaloisAdmissible.lean:23) has fields `dim`, `eq_of_unr`, `ine` and `mono`. **read** Under Nc y, `ine` equates inertia polynomials and `mono` gives mono0 x. **read**

**Proof.**
- The induction treats a singleton by `goodR_congr` and `lpSum_zero`, and a cons by `goodR_sum` (:32). **proved-by**
- `goodR_sum` forms sumRep ρ ρ′ and rewrites WD(ρ⊕ρ′) = lpSum by `TieGal`'s sum clause (LLC/SumRepresentations.lean:69). **proved-by** Away from ℓ it applies `RelW.sum` (:104). **proved-by** Over ℓ it applies `nc_sum`, then each summand's clauses. **proved-by**
- `RelW.sum` adds dimensions and gets unramified summands from an unramified sum. **proved-by** Under Nc(y⊞y′) it splits by `nc_sum`, multiplies inertia polynomials (`inePol_sum`), and takes mono0 from `monomial_sum_iff`. **proved-by**
- `nc_sum` (:91) splits Nc into Tm, mono0 and Sqf. **proved-by** `tm_sum` (:64) uses monic factorisation. **proved-by** `sqf_sum` (:82) adds root multiplicities and needs thr(w, n) antitone in n (`thr_anti`; `thr`, TC/Transported.lean:11). **proved-by**
- `TieLP` and `TieGal` (LLC/SumRepresentations.lean:51, :69) concern only local parameters and the WD functor. **read**

**Use.**
- `goodR_part` (:204) folds `halfTwist` (:100) over the d twists of a Speh segment. **proved-by** Here `spehLoc` = ⊞_k lpTw(locG π, (d−1)/2 − k) (LLC/DataN.lean:1240). **read**
- `goodR_iso` (:258) folds over the parts, and `isoRep` (:288) packages the result. **proved-by**
- `halfTwist` builds each piece by `goodR_char` from `goodR_cusp`. **proved-by** `goodR_cusp` is the cuspidal clause of `AutomorphicGaloisAdmissible` (TC/AutomorphicGaloisAdmissible.lean:133). **read** The twisting character comes from that record's exact-equality clause. **proved-by**

## Not read

- Item 1: `HtNums.le_hu` and `hPn_le_hA` past their call lines; `IndefSide.boundsMu`, `L3main`.
- Item 2: `fockDiagBound`, `jetMap_mem`, `fock_mul_det`'s U(n) integral, `fjCut`.
- Item 3, read as statements only: `slope_good_ge`, `covolumePerRank_le_neg_slope_scaled`, `liftForms_frames_majorantNorm_eq_petersson`, `DescentFamily.descent`.
- Item 3, not opened:
  - `lowDef_of_gram_of_anchor` (the top level);
  - `uniform_lower_bound_of_sums'`, `height_lower_bound_general_alt`;
  - `flat_of_prints_deepGood_flatDeg_anchor`, `anchor_bound`;
  - `flat_tensor_swap_isIso`, which proves FlatDegreeSt;
  - the fifteen literature theorems.

  Also unchecked: that `ofRecord … logOm` equals `CM.logOm`.
- Item 4: `Del_holds`, `lgc_of_cut'_alt` (taken from open-hops), `isHeckeGalois_of_conj`, the body of `rhobar_fac` past its opening.
- Item 5: `RelA.sum`, `goodR_char`'s ℓ-adic branch, and the rest of `halfTwist`'s case split.
