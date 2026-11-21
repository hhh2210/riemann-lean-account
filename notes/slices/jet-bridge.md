# The jet bridge: from a theta-lift period to a Taylor coefficient in the height-two logarithm

Read 2026-11-20 from source text only; nothing built. Paths are relative to `src/`. Tags: **read** (quoted or transcribed text was read), **proved-by** (proof body read, inputs named), *inferred* (my interpretation). Abbreviations: `PZF` = `Formalism/SharpRestriction/Divisibility/ProductZerothFirstParts.lean`; `JPL/` = `Formalism/SharpRestriction/Divisibility/JetPolynomialLogs/`; `OP` = `Formalism/SharpRestriction/Divisibility/OrbitPlaces.lean`; `TLM` = `Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean`; `SP/` = `Development/AbelianVarietyTheory/Proofs/SatakeParameters/`; `UTS/` = `Formalism/ThetaLogCoordinates/UniformThetaSubstitution/`; `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`; `MV/` = `Formalism/SharpRestriction/GrowthBounds/MultisetValuation/`; `TPS/` as in `divisibility-trace.md`.

## 1. Direct answers

**(a) The function.** On the path, the jet theorems receive `E.Th u μ w i c c'`, which the tie `KFTie.th` fixes (`Formalism/SharpRestriction/GlobalSchurBounds/GL3Columns.lean:537`). **read**
```
E.Th u μ w i c c' = atLin (k j ↦ [tauPl j.1 = k.1]·c0·λ(dgen k.1)·B(i+1,c')_{k.2.1,j.2.2}·B(i,c)⁻¹_{j.2.1,k.2.2}) X
                          (pSer D (E.lam w) (O.Th i c c'))
```
Here `O.Th i c c' : VC D N_i N_{i+1} → ℂ` is the lift's theta kernel, a function on VC = (embeddings τ) → Mat_{N_{i+1}×N_i}(ℂ) (`GL3Theta.lean:573`). **read** `pSer D lam G α = λ(taylor D G α)` maps its Taylor coefficients at 0 in the complex coordinates through λ : Q̄ → ℂ_ℓ (`TLM:115,211`). **read** So the function is the ℓ-adic image of the Taylor series of a complex theta function, rewritten in local bases B at w, and the variable is the complex-linear uniformising coordinate z. *inferred* Condition `B0` identifies z with a formal-group logarithm. Th(ep·jetLogG X) must be integral times an exponential, where `jetLogG l d v = Σ_e X_{(v.1−2e,v.2)}^{(l²)^e}/l^e` (`Formalism/LocalRingCardinality/DataJet.lean:13`). **read**

**(b) A jet.** `KvalGe N0 N1 l nu Th B` (`PZF:99`) bounds the coefficients of `applyAt0 Th (Gxz I)` (`PZF:92`). **read** This pairs the Taylor coefficients of Th, times factorials, with `Gxz I = ∏_s ∏_c det[Σ_a X(s,i,a)·Z(s,a,I_{s,c}(k))]` (`PZF:82,89`). **read** That is, the operator ∏ det(Y∂_Z) is applied to Th at Z = 0, giving a polynomial in a frame Y. *inferred* The lift law has the same form (`liftTie`, `GL3Theta.lean:575`; `UnfIs`, `Formalism/LocalToGlobal/KernelLattices/FirstKernelLawReading.lean:293`):
```
C.unf i c c' (Q ∘ frm) y' = applyAt0 D (polD D dgen Q (frm (i+1) y')) (O.Th i c c')
applyAt0 D P G = Σ_α coeff_α P · α! · taylor G α      -- GL3Theta.lean:533
```
**read** So a value of a lifted form is a constant-coefficient differential operator applied to the kernel at 0, and a period of the m-fold lift is a polynomial in such jets. *inferred*

**(c) Letters.** A letter is s ∈ ℤ/d. Here d = `nP D p`, the additive order of the Frobenius class `hP D p` in `HH D = D.R.A`, doubled for signal primes (`…/GrowthBounds/IsResidueClassZero.lean:163`). **read** `orbLoc` (`OP:145`) gives letter s four things. **read**
- The position `posPl D p z s.val`, which is s Frobenius steps along the orbit of the CM-type position z.
- That position's Young diagram.
- An N_i × N_{i+1} block of variables.
- Membership in TT when the position is top (`IsTopPl`).

Even and odd letters are the two halves of the CM type, which Frobenius alternates at an inert prime. *inferred* The CM3 proof uses σ(ω) = 1 − ω. **read**

**(d) Inputs of `split_bound_eleven_one`.** All five are bookkeeping. They turn B1–B4 into `BHyp`, undo the logarithm substitution, and identify `applyAt0` with `frameJet` (§2). **proved-by** Theorem A's arithmetic on the path is therefore entirely its hypothesis `L.AdmB`, mainly B0. *inferred*

**(e) The curve is used.** On the path, B0 is proved from an elliptic curve with CM (§4). **proved-by** CM2 (a good model) comes from global Artin reciprocity. CM3 makes the formal group at an inert prime the height-two Honda group. CM4 makes prime-to-ℓ torsion integral. The theta kernel is shown to be an integral combination of torsion translates of the curve's theta function. **proved-by** The Weil representation contributes only the polynomial frame model of forms and the kernel law. *inferred*

**(f) Corrections to `divisibility-trace.md`.**
- The rate-γ gain on served orbits, gB = γ·Σal − Σ min(al/p^e, cap) − de (`FGS:57`), comes from two theorems. `kernel_a_two_generic` gives gB − alEven via `ea_A2U`, and `kernel_b_generic` gives the Hecke-twisted gB via `ea_BU`. **proved-by** `kernel_a_one_generic` supplies only the excess form gA (`FGS:66`). **proved-by**
- `OrbitBoundWithoutOperator` is not a bare hypothesis. On the route through `reciprocity_kernel_of_artin`, `orbitBound_standardSeries_inertPlaces` proves it via `kernel_of_f` (`SP/AtOfTrueColumns.lean:47`). **proved-by**

**(g) Mechanism.** *inferred* Fix an inert ℓ and a Frobenius orbit. Write z = ε·log_F(X), with log_F(X) = Σ_j X^{ℓ^{2j}}/ℓ^j. The kernel is then Θ(z) = U(exp_F z)·exp(β(z)), with U integral and β the orbit-averaged coboundary of the logarithm of the curve's ℓ-adic sigma function.
1. The inverse exp_F of a height-two logarithm has degree-n coefficients of valuation ≥ −ρ(n−1), where ρ = 1/(ℓ²−1) (`LemmaSt`).
2. The n-th derivative at 0 of U(exp_F z) is n! times a coefficient. Its valuation is therefore ≥ v(n!) − ρn ≥ n/(ℓ−1) − ρn − (log_ℓ n + 1).
3. Since 1/(ℓ−1) − 1/(ℓ²−1) = ℓ/(ℓ²−1) = γ = 1/ℓ + 1/ℓ³ + ⋯, this is γn − (log_ℓ n + 1).

The factor exp(β) can only hurt through monomials below weight 1/(ℓ−1) − ρ·deg. `BHyp` confines those to "bipower" even–odd pairs (`LemmaS`), and the radius lemma charges them a radius. With several letters, a derivative along a top letter keeps γ only as Σ_{e odd} a/ℓ^e, each term capped by the partner letter s+e (`topTerm`, `excessGain`). Every other derivative keeps at least ρ (`LemmaFb`).

The served-orbit theorems repeat the count in Y = X/ϖ, where ϖ^{ℓ²−1} = ℓ. There exp(−β) = exp(−(ϖ^{ℓ+1}/ℓ)·h(Y))·V (`RestGc`), with V integral and h = Σ_s u_s Y_s^ℓ Y_{s+1} + ⋯ of degree ≥ ℓ+1. So Θ(ϖY) is a sum of divided powers (h/ℓ)^i times integral series. Finally, `descend` returns to z at a cost of exactly ρ per degree.

## 2. Step 1: Theorem A's frame and its inputs

`Loc` (`PZF:128`) is a `JetLoc` plus diagrams `nu s` and a set TT ⊆ ZMod d. **read** A `JetLoc` (`DataJet.lean:17`) consists of a prime ℓ ≥ 5, an even d ≥ 2, N0 < N1, and a bare series `Th : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_ℓ`. **read** Nothing in `Loc` constrains Th. **read**
```
B0 ep be := ∃ sg = ±1, ∃ U, (∀ m, ‖coeff m U‖ ≤ 1) ∧
            Th(ep·jetLogG X) = U * subst jetLogG (expS (sg • Σ_{a,b} be(X_{·,a,b})))     -- PZF:192 (:182, :186)
AdmB    := ∃ ep, ‖ep‖ = 1 ∧ ∃ be, B0 ep be ∧ B1 be ∧ B2 be ∧ B3 be ∧ B4 be              -- PZF:199
ThmA C  := ∀ a, (ℓ ≤ a ∧ ∀ s, |ν_s| ≤ a ∧ 2 log_ℓ a + 2 ≤ N0 − 1) →
           KvalGe N0 N1 ℓ nu Th (Σ_{s∈TT}(topTerm s − γ·Wc s) + FD − C·d·N0·N1·(log_ℓ a + 1))  -- PZF:205,208
SplitConstantsUniformBound C6 Cd :=
  (∀ L : Loc, L.AdmB → L.ThmA Cd ∧ L.Cor2 C6 Cd) ∧ ∀ L : Loc1, L.AdmB → L.ThmOne Cd   -- LocalBoundElevenComparison.lean:24
```
**read**

The four conditions on be: **read**
- **B1** (`:37`): be has coefficients in the completed maximal unramified extension.
- **B2** (`:43`): be is fixed by X_s ↦ u^{±ℓ^s}X_s, with + for even s and − for odd s, whenever u^{ℓ^d−1} = 1.
- **B3** (`:47`): every monomial has positive even-letter degree and positive odd-letter degree, and bidegree ≠ (1,1).
- **B4** (`:70`): exp of be's two additivity defects (`cobX`, `cobY`) is W-integral with constant term 1 in jetLogG coordinates.

So AdmB says the following about the orbit restriction in log coordinates. *inferred* It is integral times the exponential of a torus-invariant cross term between the two halves of the CM type. That cross term has no bilinear part and is additive up to integral exponentials.

The exponent is built from three pieces. **read**
- `topTerm` (`PZF:166`) is a sum over odd e. Below the first odd distance to another top letter the term is max(A_s/ℓ^e − cap(s+e), 0); beyond it the term is A_s/ℓ^e. Here A_s is the length of the first row.
- `FD = Fnum(Dl)`.
- `Cor2` (`LocalBoundElevenComparison.lean:13`) is the same bound with `baseTerm` in place of `topTerm` and lpF((k−1)w) − C6·Σw/ℓ in place of FD, when Dl = (k−1)w + E.

The translators are defined in `JPL/DworkPowerSeriesWeights.lean`. **read**
```
TieB := ∀ ℓ d, 5 ≤ ℓ → 2 ≤ d → Even d → ∀ be, B1 → B2 → B3 → B4 →
          ∃ K0 ζ, Unram ℓ K0 ∧ IsPrimitiveRoot ζ (ℓ^d−1) ∧ BHyp ℓ d K0 ζ be                         -- :149
KernelFromExponentialTwist := ∀ L ep be, ‖ep‖ = 1 → L.B0 ep be → ∃ g U ε, (∀ y, constantCoeff (g y) = 0) ∧
          (∀ y, subst g (entLog ℓ y) = X y) ∧ Integral U ∧ (ε = ±1) ∧ Th(ep·X) = thetaZ g U ε be          -- :154
TieFrame := … ‖ep‖ = 1 → (∀ I n, ‖coeff n (frameJet … I (Th(ep·X)))‖ ≤ ℓ^{−B}) → KvalGe N0 N1 ℓ nu Th B  -- :165
```
Here `thetaZ g U ε be = U(g(z))·exp(ε·Σ_{a,b} be(z_{·,a,b}))` (`Formalism/GaussJetBounds/StatementP.lean:13`). **read**

Each translator's proof: **proved-by**
- **`tieB`**: equals `tieB_of integrality_of_letter_log` (`JPL/UniformBoundAllData.lean:10,26`).
  - K0 comes from `wfrac_unram`.
  - Torus invariance comes from B2.
  - `NoLowBidegree` comes from B3.
  - The exp(de1)/exp(de2) integrality comes from `unipotent_exp_haar_sqrt_bound` (`JPL/LetterLogIntegrality.lean:304`). Despite its name, that lemma only renames the variables of B4.
- **`kernel_from_twist_holds`** (`JPL/OneLetterJetKernel.lean:54`): takes an inverse g of `entLog` (from `generalized_log_inverse` and `logarithm_weight_comparison`) and substitutes g into B0. This is a change of variables. *inferred*
- **`tieFrame`** (`:418`): matches `applyAt0 Th (Gxz I)` with a renamed `jetPairPoly` (`applyAt0_eq_jet`, `psi_Gxz`). It removes ep using the homogeneity of minors and ‖ep‖ = 1.
- **The one-letter versions** (`:172`, `:534`) are proved the same way.

`thmA_of` (`:177`) calls `thmAGauss` and compares exponents. **proved-by** `split_bound_eleven_one` (`LocalBoundElevenComparison.lean:64`) adds `corollary_split_eleven_one` (`:56`, from `normCor7` and `base_term_le_top_term`) and `thmOne_of`. **proved-by**

## 3. Step 2: the served-orbit theorems

```
KernelValuationBoundUltrametric := ∀ K (ultrametric, char 0) p ν r0 r1 u ϖ Th TT colN hts I,
  2 < p → ‖p‖ = p⁻¹ → ϖ^(p²−1) = p → (∀ s, ‖u s‖ ≤ 1) → InClass p (hhS p u) (Th(ϖ·X)) →
  ∀ n, ‖coeff n (frameJet colN hts hp I Th)‖ ≤ p^{−excessGain(p, TT, dSet TT, alG, capG, deLoss)}   -- UTS/StatementGK.lean:63
InClass pp hh F := ∃ U_i integral, ∀ n, coeff_n F = Σ_{i ≤ deg n} pp^{−i}·coeff_n(hh^i·U_i)         -- UTS/OddLogRelation.lean:76
hhS p u := Σ_s u_s Σ_{ab} sPos(s,ab)^p·sPos(s+1,ab),  sPos(s,ab) = Σ_l (−1)^l X_{(s−2l,ab)}^{p^{2l}}    -- UTS/CyclicPowerClassOfExpEquiv.lean:85,81
excessGain = Σ_{s∈TT} Σ_{e odd, e ∉ dSet s} max(al_s/p^e − cap(s+e), 0) − de                       -- Formalism/GrowthSums/StatementA.lean:108
```
**read** In words: suppose Th, rescaled by a (p²−1)-th root of p, is a sum of divided powers (hh/p)^i of an explicit cross term times integral series. Then its frame jets have valuation at least `excessGain`. *inferred*

The proof has three steps. **proved-by**
1. `kernel_a_one_generic` (`UTS/FrobeniusLiftNorms/EGaussK.lean:213`) bounds F = Th(ϖX), then divides by ϖ^d via `descend` (`:132`), using ‖ϖ^d‖ = p^{−ρd}.
2. `gauss_a_one_generic` (`:186`) passes to a generic Gauss-norm field and applies `Top.entry_a_one`.
3. `entry_a_one` (`UTS/KOneConsequence.lean:43`) is `entryExcessBound_of entryStar hitsCapPos entry_a_one_bound chargeLemma`. Its `entryStar` rests on a Hasse-derivative pairing identity (`termBound`), `hhDecomp`, `classSubst` and `gainFactorialInequality`; these bodies were not read.

The statement of `FormalGroupSystem.Pf.stmt_proved` (`MV/PrvAndKernelCommutationUpToUnitsOfRests.lean:107`): **read**
```
Stmt D := (∀ p X (Y : Pend X), admitted D X Y → Conclusion₂ D X Y) ∧ RelativePresentationLiterature D   -- FGS:779
stmt_proved D := ⟨fun _ _ _ Y hA => packet_statements_hold D Y hA, relative_presentation_of_d7 D⟩
```
All the arithmetic sits in the hypothesis `admitted` (`FGS:771`). **read**
- Its clause `adm2` (`:548`) asks `ExtensionLocalCondition` (`:162`) of each theta series of a `Pend` (`:447`).
- That condition reads ThA = exp(−Ph)·U, with U integral after substituting logF = Σ X^{p^{2j}}/p^j, and Ph ≃ Σ_e be(X_e, X'_e).
- Other clauses of `admitted` tie ThA to the chain map.

`rests` (`:97`) supplies two jet bounds. **proved-by**
- **`VolumeRatio₂`** (≥ gA): `first_theorem_place_bound` → `ea_A1U` → `kernel_a_one_generic`.
- **`Ent`**: `second_lemma_place_bound` → `ea_A2U` → `kernel_a_two_generic` (gB − alEven), and `hecke_place_bound` → `ea_BU` → `kernel_b_generic` (gB). See `MV/FirstTheoremPlaceBound.lean:20–28` and `MV/AuxUOfFirstTheoremPlaceBound.lean:50–56`.

InClass comes from `RestGc` (`MV/DworkExponentialRestrictions.lean:19`). **read** In rescaled log coordinates, `RestGc` gives exp(−Ph) = exp(−(ϖ^{p+1}/p)·hh(u))·V with V integral. **read** `stmt_proved` does not construct a `Pend`; `SysTw` (`…/GaloisGeometry/ModelsOK.lean`) asks for one to exist. **read** On the path that existence comes through `ModelsAt`, from `AdmAtEnt2` and `CurveEx` (`…/GaloisGeometry/ThetaSeriesDataHypothesesBelowMaximalLevel.lean:106,131`). **read** (statements only) Their `Pend` is `pendG … hLT …`, built from a curve with a Lubin–Tate isomorphism. **read** (statements only)

## 4. Step 3: where the curve enters

```
CM3 := ∀ d L, Squarefree d → d % 4 = 3 → HasCMBy d L → ∀ ℓ ≥ 5, ℓ ∤ d → ¬(−d square mod ℓ) →
  ∀ ι g2 g3, IsGoodModel ℓ L ι g2 g3 → ∃ ε ∈ Kur ℓ, ‖ε‖ = 1 ∧
    ∀ n, coeff n (uSer g2 g3 ∘ (ε·ltLog ℓ)) ∈ Kur ℓ with norm ≤ 1      -- …/TorsionIntegrality/CMGoodModels/Statement.lean:49
```
Here uSer = X·wpNum/wpDen (`:32`) and ltLog = Σ_j X^{ℓ^{2j}}/ℓ^j (`:35`). **read** Since uSer is −2℘/℘′ in z, CM3 says the formal group is the height-two Honda group over W. *inferred*

CM3 has two proofs. **proved-by**
- `GlobalTheory.HondaCM3.cm3` (`…/DecoratedLatticeProofs/OneSubTwoOmegaSq.lean:77`) uses the integral CM multiplier [ω], σ(ω) = 1 − ω, height ≤ 2 from good reduction, and `heightTwo_formalGroup_unramified_multiplier`.
- `ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgClose.lean:25` uses `end_integral`, `hon_main` and `lang_semilinear`.

**Use on the path.** `servH_row_of_artin` (`SP/BundleBothPartsOfStandardKernelOfGlobalArtinReci.lean:15`) sets CM2 := `cmGoodModel_of_globalArtinReciprocity hA`. **proved-by** It then supplies `servH_row` (`SP/BundleBothPartsOfStandardKernelAndSixHypotheses.lean:15`) with the following. **proved-by**
- AlgTAll, GenusOneModelExistsLattice and CurveDict come from `torsionTaylorAlgebraic_latticeExists_of_cm` (`SP/TorsionTaylorAlgebraicLatticeExistsOfCm.lean:15`). The last two use CM3 (`cmIntegralityThree`) and `cm4`.
- IntInert = `kernels_integral_inert`, under `Fact CM2` (`…/InertKernelTheory/KernelsIntegralInert.lean:9`).
- AdmAtEnt2 comes from `admissible_entries_small_chain`.
- CurveEx = `curveEx_of_cm h2 HondaCM3.cm3` (`SP/ExistsGenusOneFormalIsoOfUnramifiedGoodReduction.lean:17,23`).

**IntInert** (`…/InertKernelTheory/StatementInt.lean:18`). **read**
- Setting: the CM lattice δ·cc, an inert ℓ ≥ 5, admitted L and L', an integral model of unit discriminant, and an orthonormal local basis b.
- Hypothesis: F is an `IsComb` (`TLM:286`). That means an integral combination of λ-adic Taylor series of prime-to-ℓ torsion translates of the natural theta family `B.eNat χ`.
- Conclusion: substitute z_k = Σ_i u⁻¹·λ(b_i)·flog_W(X_i) into F, where flog_W is the model's formal logarithm (`TLM:207,225`), and multiply by the inverse sigma correction. The result is integral.

**HostAt** (`…/GaloisGeometry/ExistsConstantCoeffOne.lean:37`) restates IntInert in Honda coordinates. **read**
- It supplies curve data: g2 and g3 with unit discriminant; an integral `thetaS` = uSer∘(ε·lgF); a Frobenius lift σ; a formal group law F with logarithm lgF; and a norm relation for phFF.
- For every `IsComb` G, exp(Σ_i phFF(X_i))·G(c·Σ_i λ(b_i)·lgF(X_i)) is then integral.

`hostAt_inert` (`SP/JacobiOfClass.lean:63`) derives HostAt from GenusOneModelExistsLattice, CurveDict and IntInert. **proved-by** I read the setup of its body only.

**The kernel is such a G.** The record `KerEntTied` (`FirstKernelLawReading.lean:395`) has these fields. **read**
- cc = ccK.
- δ, a twelfth root of the discriminant.
- `B : Base D cc δ`, a `PeriodPair` whose lattice is `lamOf D cc δ` (`…/KernelLattices/ColumnData.lean:651`).
- χ.
- `O_Th : (O u μ).Th i c c' = (rd u μ).Th seam (ambOf seam B χ cD) i c c'`.

`comb_of_tied` (`SP/CombOfTied.lean:14`, from AlgTAll) states that `pSer (λ_w) ((t.O u μ).Th i c c')` is an `IsComb` of `t.B.eNat t.χ`. **read** `eNat` (`ColumnData.lean:700`) is built from `thM B.L ω₀ …` by a tensor power and the averaging operators `Iop`. **read** I take `thM` to be the curve's theta function. *inferred* `ThSp` (`TLM:87`) is defined by α(x)·G(z+x)·exp(−πH(z,x) − πH(x,x)/2) = G(z). **read**

**B0 from HostAt.** `exists_beFam_evenConditionsInert_of_kerEnt` (`SP/AdmissibleKernelSeriesInertPrimeNonConjugateFrob.lean:24`) proves `ThetaExpansionAllPlaces` (`OP:186`) for `t.ent.Th` in three steps. **proved-by**
1. Rewrite `t.ent.Th` as `stdSer` of `pSer(O.Th)`.
2. Apply `normalisedFamily_standardBases_integrality` (`SP/NormalisedFamilyStandardBasesIntegrality.lean:19`). Its inputs are HostAt, `exists_of_inertPrimeEllipticCurveLocalData`, a change from standard to orthonormal series, and `orbitIdentity_all_of_integralClass_hostLog_alt`.
3. Take be = `beOf p d σ (cob F (phFF …)) om oms ζ`.

The definition `phFF = −σ_reg(ε·lgF) + (s2/2)(ε·lgF)² − fLog(lU(lgF))` (`…/GaussSumParity/StatementE.lean:24`). **read** So be is an orbit average of the coboundary φ(F(X,Y)) − φ(X) − φ(Y) of a logarithmic sigma function. *inferred*

**`ThetaIntegerIsSSubstitution.lean`.** `kernel_of_f` (`:250`) rewrites `thetaInZ` as `thetaLog` (`:152`). **proved-by** It then applies `kernel_bounds_generic`, which is `theorem_s_uniform` combined with the three kernel bounds. **proved-by** On the path it reaches `orbit_bound_rec` (`SP/OrbitBoundStandardSeriesInertPlaces.lean:22`) through `kvalGe_gainA` (`SP/KvalGeOrbitGainWithoutOperator.lean:106`). **proved-by**

**Decision.** On the path, theorems make the link to the CM curve; it is not assumed. **proved-by** The curve enters three times. *inferred*
1. The lattice δ·cc and its theta function, from which the kernel is built.
2. The Weierstrass model, whose formal logarithm defines integrality.
3. CM3's Honda isomorphism, which converts that logarithm into the explicit lgF used by every jet theorem.

I ran no search for "Fock" or "Hermite". *inferred*: the frame-polynomial model (`evFr`, `polD`, `WtPol`) plays the Fock-model role.

## 5. Chains (producer → consumer)

- **J (jets → lattice):** `KerEnt.kform` (…/LocalRingCardinality/DataKerI.lean:115) → `kgeTw_of` (OP:1464) → `kform_of_ker` (OP:1621). In parallel, `thmA_of` (JPL/DworkPowerSeriesWeights.lean:177) → `split_bound_eleven_one` (JPL/LocalBoundElevenComparison.lean:64). Both feed `OrbitPlaces.admitted` → `lift_bounds_of_essential` (OP:1340) → `sum_over_primes_service` (…/SmoothDesignExistence/SumOverPrimesHypotheses.lean:187). **read** In `kgeTw_of`, all jets of E.Th of norm ≤ ℓ^{−B} make K_i map the local lattice into b·(next lattice), with v_w(b) ≥ ⌈e_w B⌉ − e_w v_ℓ(n). **proved-by**
- **G (curve → B0):** `exists_beFam_evenConditionsInert_of_kerEnt` → `at_of_true_columns` (SP/AtOfTrueColumns.lean:30) → `at_of_stdTie` → `rowAt_of_stdTie` → `servH_row` → `servH_row_of_artin` (CM2 from `cmGoodModel_of_globalArtinReciprocity`) → `servH_row_linkR_alt` (TPS/ServHRowLinkR.lean) → `reciprocity_kernel_of_artin` (TPS/ServHRowLinkRStatement.lean:14) → `row_hServ_of_link_alt` (TPS/RowHServOfLink.lean:17) → `HypsAlt.hServ` → `SelectionServed.pdv` → `sum_over_primes_service`. **read**
- **S (served):** `kernel_a_one/a_two/b_generic` (EGaussK.lean) → `ea_A1U`/`ea_A2U`/`ea_BU` (MV/EaGeCOfNorm.lean:198,211,224) → `rests` → `stmt_proved` → `UAt_of`. **read** In parallel, `tuplesHaveLocalModels_at_constructedPoint_over_trueColumns` (AdmAtEnt2, CurveEx) → `ModelsAt` → `rowTwU` → `SysTw` → `UAt_of`. **read**
- **U (unserved):** `kernel_of_f` → `kvalGe_gainA` → `orbit_bound_rec` → `at_of_true_columns` → `OrbitBoundWithoutOperator`. **read**

## 6. Degenerate or vacuous points

- `Loc` and `JetLoc` hold a bare Th. **read** D7's `ThetaJet` admits `jetToy` with `Sit := Empty` (`…/SpanPowerMembership/ExampleNewtypesIdempotentZero.lean:15`). **read** So the `D.jet`/`Prov` route in PZF is vacuous for such D. *inferred* On the path, ThmA is applied universally to orbit restrictions of the tied kernel, so the empty case does not arise. *inferred* (`orbit_entry_bounds_hold` not read.)
- ThmA requires N0 ≥ 2 log_ℓ a + 3. **read** Whether its consumers meet this was not checked. *inferred*
- The kernel law and the ties (`UnfIs`, `KFTie`, `O_Th`) are fields of `KerEntTied`. **read** I did not read where that record is built. **read**

## 7. Not read

Each item was seen at a call site or as a signature only. **read**
- How `KerEntTied` is built: `linkR_stdTie_entry`, `row_hServ_of_kerServ_alt`, `serv_t_iff_formalism_serv_t`.
- `orbit_entry_bounds_hold`, where AdmB for `orbLoc` is assembled.
- `standard_series_b_conditions_large_prime`.
- The bodies of `comb_of_tied`, `admissible_entries_small_chain`, `curveDict_of_cm`, `rowTwU_of_models`.
- The components of IntInert: `intInert_of`, `thFourInt_of`, `four_products_from_one`.
- The inputs of CM2: `cmLattice_good_model_unramified`.
- The CM3 lemmas: `heightTwo_formalGroup_unramified_multiplier`, `hon_main`, `end_integral`.
- `generalized_log_inverse`, `logarithm_weight_comparison`.
- The proofs of `entryStar`, `chargeLemma`, `RestGc` and `theorem_s_uniform`.
- `ea_lowN`, `restEnt_of`.
- The `JetTorsionCompatibility` route (`FormalGroupJets.lean:175`); whether it lies on the path is open.
