# Jets at inert primes: the divisibility that plays the part of multiplicity

Read 2026-11-20 from source text (build unfinished). Paths are relative to `src/`; `F/` = `Formalism/`, `GJ/` = `F/GaussJetBounds/`. Tags: **[R]** read and transcribed, **[P]** proved-by (theorem located), **[I]** my interpretation.

## 1. The constants

```
def rho (l) := 1 / (l^2 - 1)        def gam (l) := l / (l^2 - 1)            -- F/IncomingBounds/IncomingBound.lean:8,10
def Constants := ∀ l ≥ 2, HasSum (k ↦ (l^(2k+1))⁻¹) (gam l) ∧ rho l + gam l = 1/(l-1)        -- :42
def ValGain := ∀ l prime, (∀ n ≥ 1, 1/(l-1) ≤ n/(l-1) - v_l(n)) ∧ ∀ e, rho l ≤ (l^2)^e * rho l - e   -- :47
```
[R] γ = 1/l + 1/l³ + ⋯ and γ + ρ = 1/(l−1) (so ρ = 1/l² + 1/l⁴ + ⋯). [P] `constants`, `valGain` (F/IncomingBounds/WeightIdentities.lean:14–15). [I] "a/p + a/p³ + ⋯" is `gam p * a`; since v(a!) ≈ (γ+ρ)a, v(a!·c_a) ≥ γa means v(c_a) ≥ −ρa, the radius of a height-two exponential.

## 2. The divisibility in the Lean's words (`GJ/`, namespace `DworkPowerSeriesWeights`)

**Setting.** [R] `letterLog`/`entLog`/`oneLog` (GJ/Statement.lean:74,120,175) are Σ_e X_{x−2e}^{l^{2e}}/l^e; `g` is their compositional inverse (`subst g (entLog l y) = X y`); `U` is integral; `be` satisfies `BHyp` (:85: coefficients in an unramified K0, torus-invariant, no low-bidegree monomials, and the exponentials of its two additive coboundaries integral in log coordinates). [R] The function is `thetaZ g U ε be = U(g(z)) · exp(ε·bSum be)` (GJ/StatementP.lean:13). [R] A jet is `jetPairPoly P Th = Σ_κ coeff_κ P · (κ!·coeff_κ Th)` (:19); `IterPderivConst` (F/FormalGroupLog/Statement.lean:162) states ∂^α F(0) = (∏ α_i!)·coeff_α F, so `mfact κ * coeff κ` is a derivative at 0. [R] `frameJet` (StatementP.lean:24) applies the product, over letters s and column blocks c, of p_{s,c}×p_{s,c} minors (`minorProd`, GJ/StatementH.lean:19) of the matrix with rows Σ_a X_{s,i,a} z_{s,a,b}.

**Radius lemma.**
```
def LemmaRA := … ∀ sig ≥ 0, ∀ κ a, 1 ≤ a → (∀ i, κ i ≤ a) →
  (∀ i j α β, pureMon l i j α β ≤ κ → ¬ MonoWtGe … (1/(l-1)) (pureMon …) (coeff (pureMon …) (bSum M be)) →
      1 ≤ l^α * sig i + l^β * sig j) →
  ‖mfact κ * coeff κ (subst (linSub M) (subst g U) * mvExp (ε • bSum M be))‖
    ≤ ‖l‖ ^ ((∑ i, κ i * (gam l - sig i)) - card ι * (logb l a + 1))          -- GJ/StatementG.lean:12
```
[R] The κ-th derivative at 0 has l-adic valuation ≥ Σ_i κ_i(γ − σ_i) − |ι|(log_l a + 1), where radii σ_i ≥ 0 must satisfy l^α σ_i + l^β σ_j ≥ 1 for each pure monomial X_i^{l^α}X_j^{l^β} below κ whose coefficient in `bSum` misses the weight bound. [R] When no such monomial occurs, σ = 0 is allowed and the bound is v ≥ γ·(order) − (number of variables)·(log_l a + 1): the note's a/p + a/p³ + ⋯ − O(log a), with the O explicit. [P] `lemma_R_log_loss` (GJ/GaussJetProofs/LemmaRA.lean:170). [R] `LemmaR` (GJ/Statement.lean:138) is the same with log_l|κ|; it is proved from a hypothesis `PureCross` (GaussJetProofs/AsmRDotAddRight.lean:75), not traced.

**One letter.**
```
‖coeff n (frameJetOne p hp I (thetaOne g U sgn ep be))‖ ≤ ‖l‖ ^ (rho l * ∑ c, p c − (N0*N1) * (logb l a + 1))   -- GJ/StatementU.lean:26
```
[R] With one letter (d = 2) the rate is ρ, not γ; `OneLetterRadius` (GJ/Statement.lean:171) records γ − 1/(l+1) = ρ, every variable having radius 1/(l+1). [P] `oneLetterGauss` (GJ/OneLetterGauss.lean:7), `oneLetterR` (GJ/OneLetterRadius.lean:23).

**Theorem A.**
```
def ThmAGauss := ∀ l d N0 N1, 3 ≤ l → 2 ≤ d → Even d → … BHyp l d K0 ζ be → … Integral U → (ε = 1 ∨ ε = -1) →
  … nu1 = colN, nu2 s = #{c | 2 ≤ p s c}, size s = ∑ c, p s c, 1 ≤ a, size s ≤ a, 2 logb l a + 2 ≤ N0 - 1 →
  ∀ n, ‖coeff n (frameJet colN p hp I (thetaZ g U ε be))‖ ≤ ‖l‖ ^ E,
  E = ∑ s ∈ TT, (topTerm s − gam l * Wcap s) + Fnum l d (Dl) − (d*N0*N1) * (logb l a + 1)      -- GJ/StatementP.lean:33
capL s = if s ∈ TT then nu2 s else nu1 s ;  Dl s = if s ∈ TT then size s − nu1 s else size s
dTop s = least odd e with s + e ∈ TT
topTerm s = ∑' e odd, if e < dTop s then max (nu1 s / l^e − capL (s+e)) 0 else if dTop s < e then nu1 s / l^e else 0
Fnum D = gam l * ∑ s, D s − maxFlow l d D          -- F/IncomingBounds/IncomingBound.lean:28, 103–113
```
[R] Each top letter s contributes Σ_{e odd} ν1(s)/l^e over its ν1(s) first-row derivatives, each term cut by the capacity of the partner letter s+e, less γ·`Wcap`; all other derivatives contribute `Fnum`, γ·ΣD minus a maximal flow. [R] `LemmaFb` (:63) gives ρ·ΣD ≤ Fnum(D); `LemmaFe` (:83) gives Fnum(D) = ρ·ΣD when D(s′) ≤ l·D(s) for all s, s′. [P] `thmAGauss` (GJ/ThmAGauss.lean:8); `lemmaFb`, `lemmaFe` (WeightIdentities.lean:18,21). [I] The top letters carry exactly the shape of `vonMangoldtClassSum` (§5); every other derivative is worth at least ρ.

**Theorem B (the ramified prime).** [R] `ThmBGauss` (GJ/StatementY.lean:9): if ‖S‖ ≤ ‖p‖^{−1/2} and sg has integral jets, the frame jets of exp(−S·Σ_t u_t X_{(false,t)}X_{(true,t)})·sg have norm ≤ ‖p‖^{−(1/2)Σ_t(size(false,t) − [t∈TT](ν1−ν2)(false,t) + [t∈TT]ν1(true,t))}: denominators at most p to half the size. [P] `thmBGauss` (GJ/FinalB.lean:232).

## 3. "D^p ≡ 0": not found as stated

[R] I found no statement that a power of an invariant derivation vanishes or is divisible by p. Nearest:

- [R] `def Dinv (l f) := (dz l)⁻¹ * dz f` (F/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/CurveHyp.lean:87) is the invariant derivation. `JetsPhO` (…/FrobeniusFibreCurves/StatementC.lean:33): `‖constantCoeff ((Dinv l)^[n] (phO s2 P l))‖ ≤ 1` for n = 1 and n ≥ 3, where `phO s2 P l = −sigS P ∘ l + (s2/2)·l² − log(l/X)` (CurveHyp.lean:75) and `sgStar s2 P = σ·exp(−(s2/2)z²)` (:36). [P] `jetsPhO` (FrobeniusFibreCurves/FinalC.lean:12). [I] This is integrality of D^n log θ(0) beyond the quadratic term, not divisibility.
- [R] Height two is built into the logarithm: `lgF K p = Σ_j X^{(p²)^j}/p^j` (F/ThetaLogCoordinates/UniformThetaSubstitution/OddLogRelation.lean:13); `IsLawOfLog p F` (IsLawOfLog.lean:40): F is an integral law with lgF(F(X,Y)) = lgF X + lgF Y.
- [R] `CM3` (F/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean:49): if L has CM by ℚ(√−d) (d squarefree, ≡ 3 mod 4), l ≥ 5, l ∤ d and −d is not a square mod l, then for every good model (g2, g3) (`IsGoodModel`, :38: integral over the maximal unramified extension, unit discriminant, a λ-rescaling of L's invariants) there is a unit ε there with every coefficient of `uSer g2 g3 ∘ (ε·ltLog l)` integral. [P] `cm3` (CMGoodModels/CmAll.lean:11). [I] `uSer = X·wpNum/wpDen` (:32) is −2℘/℘′ as a series in z, so CM3 says the curve's formal group at an inert prime is the height-two Honda group: the content of "D^p ≡ 0".
- [R] `ShiftHeight` (F/FormalGroupWitt/Statement.lean:146): the shifted group has an endomorphism e with e*log = l·log, e_j ≡ X_{j−1}^{l²} and e^m ≡ X_j^{l^{2m}} (mod l). [P] `main (hC : FunEqCongrV) : ShiftHeight` (FormalGroupWittProofs/HeightV.lean:156), conditional on `FunEqCongrV`.

## 4. Theta functions at CM points, and Ω

[R] `thetaS l g2 g3 ε = uSer g2 g3 ∘ (ε·lgF)` (…/GaussSumParity/StatementE.lean:19); `ThetaHom` (:38): the elliptic logarithm composed with thetaS is ε·lgF, and thetaS is a homomorphism from F to the curve's formal group. [P] `thetaHom` (GaussSumParity/BiextensionRelation.lean:10). [R] `ThmAEntryCM` (GaussSumParity/StatementF.lean:16): assuming `CM2` and `CM3`, for inert l as above there are g2, g3, ε with integral thetaS such that, given a Frobenius lift, dual bases and a norm relation, for every Φ with Φ ≃ sumE(cob F (phFF …)) and integral U0, ‖δ(frameJet(thetaInZ … (exp(−Φ)·U0)))‖ ≤ ‖l‖^E, E Theorem A's exponent. [P] `thmAEntryCM` (BiextensionRelation.lean:15). [R] `CM2` is assumed as `cm2 [Fact CM2]` (CmAll.lean:12) or obtained from `GlobalTheory.Published.GlobalArtinReciprocity` (Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CmGoodModelOfGlobalArtinReciprocity.lean:10). [I] The theta function at a CM point is exp(−Φ)·U0 in the formal parameter, Φ the coboundary of log σ*; `thetaForm` (KummerThetaLogarithms/ThetaIntegerIsSSubstitution.lean:173) rewrites it as `thetaZ g U (−1) be`, so Theorem A applies.

[R] Ω enters the size data, not the jet theorems:
```
def logOm := γ_E + log (π / D.host.v) − L.logDerivativeAtOne                  -- F/LocalRingCardinality/DataParams₂.lean:224
def MAIN u := ∑ t, (m * (phF (aT t) − aT t * logOm) − aT t * log T_u)       -- :232, phF y = y log y − y
```
with the field `logDerivativeAtOne = dlogL D 1` (L′/L(1, χ_{−d})) and v = rdE/2 (DataHost.lean:143). [R] `LinkDIV_at` (F/SharpRestriction/GlobalTheoremInputs.lean:77) contains `muDual + h u − Fo ≤ MAIN u + C·|TT|·a·La + C·m·(B0+Nc)·x^(Cabs·eps)`. [R] `MeanPeriodAt` (Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/MeanPeriodLogarithms.lean:11): `meanLogOm D … M τ = logOmVal D`, with (F/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean:20,157,160) `logOmVal = γ_E + log(π/v) − L′/L(1)`, `logMet ρ s = log(π·|ρ s|²/area(Λ^ρ))`, and `meanLogOm = (2·log[ℓ_τ : s𝒪_M] − Σ_ρ logMet ρ s)/[M:ℚ]`. [P] `meanLogPeriod_chowlaSelberg : MeanPeriod` (Development/…/DivisorProofs/MeanLogPeriodChowlaSelbergStatement.lean:6); also `mean_log_period_conjugates_eq_chowlaSelberg` (…/FoundationProofs/MeanLogPeriodConjugatesEqChowlaSelbergStatement.lean:8: mean over embeddings of log(area/π) = γ_E + log(2π/√d) − L′/L(1)) and `classMean_log_norm_disc_chowlaSelberg` (…/DivisorProofs/ClassMeanLogNormDiscChowlaSelbergStatement.lean:9: class mean of log(N𝔞⁶·|Δ(L_𝔞)|) = 12 log 2π − 6 log d + 6γ_E − 6 L′/L(1)). [I] m·(phF(a) − a·logOm) is m·log(a!/Ω^a), log Ω the Chowla–Selberg mean; the jets' p-adic normalization is instead the coordinate z = ε·lgF.

## 5. From jets to the gain

**The field.** [R] `gain : ℕ → Pl → ℝ` is a field of `SizeData₂` (DataParams₂.lean:93) with support conditions only; `not_inert` (:110) forces it to 0 unless the residue prime is `signal` or `inertClass`, which `primeClass` (DataHost.lean:33) assigns to primes outside a small set, q and d with (−d/p) ≠ 1; `InertK` (GlobalTheoremInputs.lean:97) is their union. [R] `gainD` (DataParams₂.lean:212) is 0 on dropped primes; `Ga` (:220) = Σ_w sz(w, Σ_j gainD − tau); `gainTot` (F/SharpRestriction/FamCore.lean:18) is the same with `gain`, over the places above one p; `ZeroAbove` (DataParams₂.lean:246) says gain = 0 above X″ (with listed exceptions); `NoGain` (F/SharpRestriction/ParConsts.lean:24) is a disjunction of conditions on p (p > X″; neither inert nor signal; inert with small orbit order, p^i near X′, or large `Sig`), whose use I did not read.

**The relation to the count.** [R] `LinkG_at` (GlobalTheoremInputs.lean:122), third clause, for w with `InertK` and p ≤ X″:
```
(∀ j ∈ lifts, 0 ≤ gain j w ∧ gain j w ≤ 4·|TT|·a/p) ∧
(∑ j ∈ lifts, ∑ t ∈ TTw w, (vonMangoldtClassSum j t p − loG L C bo p)) − m·flG L C p ≤ (∑ j ∈ lifts, gain j w) − tau w
flG = C·f·N(m)²·log_p a + C·f·(log_p a)²                                      -- :100
vonMangoldtClassSum j t p = ∑_{i < log_p a_t + 2, i odd} max 0 (a_t/p^i − wPart j t p i)   -- DataParams₂.lean:240
```
[R] `loG` (:109) is C(Sc + k + etaSz)·log_p(2a) plus terms for inert p below X′. [I] Summed over lifts, the gain at an inert place is at least the a/p + a/p³ + ⋯ count cut by the weights, minus losses of order (dimension)·log_p a + (log_p a)²: the shape of Theorem A's exponent and error term. [R] `Losses` (F/RankGapBounds/MeanBoundSecondForm.lean:148): mean(ASK − Ga) ≤ LoP.

**The formula behind the field.** [R] `ParametersFill` (F/SharpRestriction/GrowthBounds/IsResidueClassZero.lean:401) requires `gain j w = gainP X K (aL L) (bL L) p j`, `tau w = tauP …` and `wPart j t p e = fill X (bL L) j (partner D p t e)`. [R] `gainP` (:355) sums over Frobenius orbits:
```
g0 = ∑_s ∑'_{e odd, not excluded} max 0 (al s / p^e − capU s e) − dl        -- :247
gU = gam p · ∑_s al s − ∑_s ∑'_{e odd} min (al s / p^e) (capU s e) − dl     -- :254
dl = dl1·nP·Nm²·log_p(2a) + dl2·Nv·(log_p(2a))²                              -- :241
```
[I] These are Theorem A's top terms again, since Σ max(a/p^e − cap, 0) = γa − Σ min(a/p^e, cap).

**The local divisibility wired into lattices.** [R] The local system's gains `gB`, `gA` (F/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:57,66) have the same shapes with error `de`; `NumCmp` (:727) asks gU ≤ gB and g0 ≤ gA; `VolumeRatio₂` (:658) says the column jets of exp(−Ph)·U have valuation ≥ gA; `Conclusion5` (:697) bounds below the valuation of the m-fold chain map on the sublattice `Iprod` by Σ_j(Σ_{v∈VV} max(gB − Pr, gA) + Σ_{v∉VV} gA) − Σ dG. [P] `stmt_proved : Stmt D` (GrowthBounds/MultisetValuation/PrvAndKernelCommutationUpToUnitsOfRests.lean:107); its `VolumeRatio₂` comes from `ea_A1U` (MultisetValuation/EaGeCOfNorm.lean:198), which applies `kernel_a_one_generic : KernelValuationBoundUltrametric` (F/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGaussK.lean:213):
```
InClass p (hhS p u) (subst (ϖ·X) Th) → ∀ n, ‖coeff n (frameJet colN hts hp I Th)‖ ≤ p ^ (−excessGain …)     -- UniformThetaSubstitution/StatementGK.lean:63
excessGain = ∑_{s∈TT} ∑'_e (if 2e+1 ∈ D s then 0 else max (al s/p^(2e+1) − cap(s+2e+1)) 0) − de    -- F/GrowthSums/StatementA.lean:108
deLoss = ∑_s (r1·lgN(al s) + r0·r1·lgN(ls s)) + ∑_{s∈TT} lgN(al s)²                                -- UniformThetaSubstitution/StatementAB.lean:100
```
[R] For pairings: `LocalValuationBoundAt` (F/LocalToGlobal/Divisibility/JetBounds/Statement.lean:52) says every pairing Pt(φ, F) of a lattice vector with a test vector is 0 or has w-valuation ≥ sgw; `LocalValuationBound` (:67) states that this follows from an expansion of Pt into products of entries of type `IsEntry7` (IsExpansion.lean:113), whose `weyl` case is a Theorem-A frame jet with exponent `expA`; no proof of it located. [P] `valuation_of_entry_bounds` (JetBounds/JetBoundsProofs/ValuationOfEntryBounds.lean:13) proves the version with explicit entry norms. [R] `NprimeMuR` (GlobalTheoremInputs.lean:69): |μ(Nu) − μ(NuH) − Σ_w sz(w, sg u w)| ≤ C·X″, with sg = Σ_j(gainD + F − E) (DataParams₂.lean:215). [I] The gains are the slope gained by the integral structure `NuLat`.

**On the path?** [R] `zero_free_all_of_green_v_win` (…/ThirdPlaceSeries/TopPlug.lean:12) uses `shape_closed_link_n_of_green` (TopShape.lean), whose line 54 calls `closed_linkG_of_duty` (ThirdPlaceSeries/LinkG.lean:13) → `linkG_concrete5` (F/LocalToGlobal/GroupLattices/LinkGConcreteNoKer.lean:54) → `linkG_concrete_noKer` (:48) → `link_of_local_closed` (AdmissibleFamilyNoKernel.lean:272) → `linkG_fam_noKer` (:241) → `linkG_without_kernels` (:224) → `linkG_at_of` (GrowthBounds/PlaneCountTheoremWithConstants.lean:811), which receives `ParametersFill` from the family field `Fm.fills`. So `LinkG_at` and its `vonMangoldtClassSum` clause are on the path. [R] That route instantiates the lattice data with `zeroCh` (AdmissibleFamilyNoKernel.lean:166), whose chain map is 0, so its kernel-valuation hypotheses hold trivially (`vKge_zero`, :178); `stmtF_proved` feeds `family_satisfies_ties` (:135) and `link_of_descent_closed`, a sibling route not called there. [I] On the route read, the gain inequality is arithmetic in the formula `gainP`. I could not tell whether GaussJetBounds or `KernelValuationBoundUltrametric` is load-bearing for the top theorem; the candidates are `LinkMu`/`NprimeMuR` and `LinkDIV`, not traced.

## 6. The main theorems of GaussJetBounds, in brief

- [R] `ThmAGauss`: Theorem A (§2). `ThmAJetA` (GJ/StatementG.lean:33): exponent E for one coefficient after a linear substitution `frameM x`, given labels `spec` pairing non-top rows with top letters at odd distance. [P] `thmAGauss`; `theorem_A_one_monomial_log_loss` (GaussJetProofs/TheoremAOneMonomialLogLoss.lean:238). [R] `ThmAJet` (GJ/StatementE.lean:16) is the version with log of the order; no proof located.
- [R] `ThmAEntry` (GJ/StatementV.lean:10), `ThmAEntryFull` (GJ/StatementX.lean:10): the same bound for δ(frameJet), every functional δ of norm ≤ 1 on the integral span `nablaO` of minor products (StatementS.lean:34); `ThmAEntry` assumes saturation `SBSat`, `ThmAEntryFull` does not. [P] `thmAEntry` (GJ/OneLetterGauss.lean:8, via TheoremAMatrixEntries.lean:70), `thmAEntryFull` (GJ/ThmAEntryFull.lean:8, via `slope_bound_saturation`).
- [R] `ThmAWeyl` (StatementS.lean:48): if ‖c‖ ≥ ‖l‖^E then c⁻¹·frameJet ∈ `nablaO`, i.e. the jet divided by l^E is an integral combination of minor products. [P] `thmAWeyl_of thmAGauss` (CoefficientBoundMembership.lean:94).
- [R] `OneLetterGauss`, `OneLetterR`: rate ρ, error N0·N1·(log_l a + 1). `LemmaS` (GJ/Statement.lean:98): coefficients of `be` have valuation ≥ 1/(l−1) − 1 − ρ·deg (≥ 1/(l−1) − ρ·deg off "bipower" monomials). [P] `lemmaS` (OneLetterRadius.lean:17).
- [R] `ThmBGauss`: the ramified-prime bound (§2).

## Not read

Proofs of Theorem A and `kernel_a_one_generic`; `FunEqCongrV`, `PureCross`, `EntryBound`, `SysBound`; `AuxBlock8.Pf.stmtF`, `linkG_at_core`, `LatticeLengthsAtPlace`, `LinkMu`; `GJ/StatementA–D, I–K, M–O, Q, R, W`, `GenLogInverse`, `OneLetterGaussJets/`; the `All7`/`Int7` variants (proved, no consumer found); `ThmP` (an upper bound on valuations); `GaussValuationBounds`, `GaussIdealIdentity`, `EllipticTorsion`, `Frobenius*`, `TorsionNormIteration`, `WindowSums`, `LogFactorial*`, `MoebiusJetDuality`, `TruncatedSeriesCounting`; `ArtinHasse` proofs; `Supersingular.lean`; `JetHarmonics`.
