# Determinants and Weil positivity: where they are in the source

Read 2026-11-20 from the Lean source (`src/` of the archive); the build is unfinished. Continues `spine-first-reading.md` and `second-reading-the-analytic-step.md`. Tags: **read** (statement transcribed), **proved-by** (theorem of that type located), *inferred* (my interpretation). Paths are relative to `src/`.

**How path status was decided.** Imports decide nothing: 175,179 of 175,187 files are in the import closure of `Supplements/Kernels/MainTheorems.lean`, where `rhOfAll` lives. I used references instead. (i) `rg -w` finds every mention of a name. (ii) I built a reference cone: from `riemannHypothesis`, `rhOfAll` and `allChi`, every identifier in every declaration body was resolved, aware of namespaces and `open`, with a permissive fallback for dot notation. The cone over-approximates (831,160 of 1,059,499 names). "Not in cone" therefore means off path, except for use through typeclass instances or attribute-driven tactics, which the cone does not follow. I claim "on path" only for chains whose hops I read; chains run from the leaf up to the top.

## 1. Summary

- No Weil explicit-formula functional appears. `Guinand` and `Stepanov` have 0 hits, and the `Weil` names are about the Weil representation or Siegel–Weil. **read**
- The determinant statements in the suggested places have no proof and no user: `DetChain`, `DetBlocks` and `DetSwap` (ThetaLiftIndependence), `SymGramPosSemidef` and `DetSymPow` (FockGram), `GramZ` and `TruncDet` (SmithDeterminants), and `DetGain` (ProductFormula). All are off path.
- The determinant statements on the path are elsewhere:
  - a p-adic Gram-matrix window bound with Stepanov's shape (`GramWindow2`);
  - the slope of a lattice computed as −log det of a Fock Gram matrix (`col_mu`);
  - a Bessel-model function written as a Gram determinant and shown to be ≥ 0 (`GGram`, `GNonneg`);
  - the iterated Rallis scalar (`BForm`);
  - index and covolume identities (`HermDual`, `CovolGram`).
- The end-games in ProductFormula (exponent 3/4), HalfLinks and the root `Zeta*`/`Statement{CM,FL,U}` files are off path.

## 2. Positivity and determinant statements

### 2.1 The product formula as positivity: off path

`Formalism/ProductFormula/StatementOCCM.lean:157-160`
```
def DetGain : Prop := ∀ (Δ : ℤ) (S : Finset ℕ) (g : ℕ → ℝ), Δ ≠ 0 → (∀ p ∈ S, p.Prime) →
    (∀ p ∈ S, g p ≤ (Δ.natAbs.factorization p : ℝ)) → ∑ p ∈ S, g p * Real.log p ≤ Real.log |(Δ : ℝ)|
```
**read**: if each gain g_p is at most v_p(Δ) for a nonzero integer Δ, then Σ g_p log p ≤ log|Δ|. `ProductFormula` (153-155) states log|Δ| = Σ v_p(Δ) log p. *inferred*: "W(1_S) ≥ 0 via a determinant" in its barest form, with the p-adic gains paid for by archimedean size. Neither has a proof, and neither is referenced anywhere.

The record `TypeParams` (37-104) carries the same mechanism. **read**: `slope : muQ ≤ muMaxR + hInf + hFin` (74); `hFin = -∑ p ∈ S, 2 * log p * vt p` (84); valuations bounded below by gains at good primes (87, 92-93); `sK j ≤ a log a − a − a·logOm + …` (79-80). *inferred*: an earlier, one-type form of the second note's `SlopesN`, `SlopeIneq` and `DIV`.

### 2.2 Gram positivity for Fock pairings: off path

`SmithDeterminants/StatementGram.lean:37-56`, `GramZ`, **read**. Take integer polynomials E_a·x^{α_a} that are homogeneous of degree s, have ℓ¹-norm at most k^{e_a}, and are linearly independent. Under the Fock pairing Σ f_m g_m m! (`fockZ`, 12-13), the Gram matrix has these properties:
- it is positive definite, with 0 < det ≤ ∏ diagonal (Hadamard's bound);
- ∏ α_a! divides det, and det/∏ α_a! ≤ ∏ (k²s)^{e_a};
- v_p(det) ≤ Σ (v_p(α_a!) + e_a·log(k²s)/log p).

`GramGauss` (58-77) is the Gaussian-integer version. *inferred*: the classical determinant method. There is no proof: `AssembleZ` (`DefsGram.lean:54`) is an unproved implication. `GramZ` is unreferenced, and so are `TruncDet` and `TruncFinal` (`StatementDVR.lean:99-114`, ϖ^{dS} ∣ ϖ^ℓ·det L).

### 2.3 On path: a Gram-determinant window bound (Stepanov's shape)

`SharpRestriction/GrowthBounds/FockGramWindow/GramWindow2.lean:12-29`, condensed:
```
def GramWindow2 : Prop := ∀ p … Ψ e s c, LinearIndependent ℤ_[p] e → (each Ψ j bilinear) →
  0 < Y0 → Y0 ≤ p ^ h → del + 1 ≤ p ^ h → 0 ≤ k → (∀ a b i, ‖c a b i‖ ≤ 1) →
  (binMatK ℚ_[p] del c).det ≠ 0 →
  -Real.logb p ‖(binMatK ℚ_[p] del c).det.leadingCoeff‖ + (binMatK ℚ_[p] del c).det.natDegree / (p - 1) ≤ n * La0 →
  (∀ j ∈ range Y0, s j ≠ 0 ∧ ‖s j‖ ≤ 1 ∧ ∀ a b, s j * Ψ j (e a) (e b) = (binMatK ℚ_[p] del c).map (eval (t0 + j)) a b) →
  ∑ j ∈ range Y0, M.bad p (Ψ j) (span ℤ_[p] (range e)) k ≤ Y0 * (n * (del / Y0 + (La0 + del * h / Y0) / (k + 1)))
```
**read**: `binMatK K del c` is the n×n matrix Σ_{k≤del} c_{ijk}·binom(X, k) (`MahlerMeasure/StatementD.lean:26-28`). `M.bad p Ψ L D` is rank L minus the largest number of pairs x_i, y_i ∈ L with Ψ(x_i, y_j) = p^D·δ_ij (`MahlerMeasure/GoodCount.lean:94-101`).

In words: suppose that, up to nonzero scalars of norm at most 1, the Gram matrices of p-adic pairings on one lattice are the values at t0, …, t0+Y0−1 of a single polynomial matrix of degree at most del, and that its determinant is a nonzero polynomial with controlled leading coefficient and degree. Then, on average over the window, the pairings fail to be p^k-unimodular on at most n(del/Y0 + (La0 + del·h/Y0)/(k+1)) directions.

**proved-by** `gramWindow2_proved` (`GramWindow2Proved.lean:138`). The proof uses the Smith normal form (`GM.Top.smithZp`, line 151; `Formalism.A.smithExists`). `WinLvl` (`FockGramWindow/LvlDef.lean:18-30`) applies the bound to polynomial pairings `bejj` shifted by z0+i. *inferred*: Stepanov's argument through a determinant: a nonzero polynomial of degree del cannot vanish p-adically to high order at many points of a window.

**Chain (each hop read):** `gramWindow2_proved` ← `winLvl` (WinLvl.lean:87) ← `restWinE_proved` (FockGramWindow.lean:21) ← `theorem_A_closed_form_holds` (:25) ← `local_flatness_results` (LocalToGlobal/GroupLattices/AdmissibleFamilyNoKernel.lean:64) ← `link_of_local_closed` (:279) ← `linkG_concrete_noKer` (LinkGConcreteNoKer.lean:51) ← `linkG_concrete5` (:56) ← `closed_linkG_of_duty` (ThirdPlaceSeries/LinkG.lean:23) ← `shape_closed_link_n_of_green` (TopShape.lean:54) ← `zero_free_all_of_green_v_win` (TopPlug.lean:15) ← `every_character_of_green_v_win` (:18). **On path.**

### 2.4 On path: the slope of a column lattice as a Gram determinant

`LocalToGlobal/GlobalTheory/GL4/PColSlope.lean:82-85`
```
theorem col_mu (Z : ZBasis ((D.fm u).lam 0)) [Nonempty Z.J0] :
  (card Z.J0 * card ((D.mem u).C.cls 0)) * ((D.fm u).lat 0).mu =
    -(card ((D.mem u).C.cls 0) * Real.log (gramZ ((D.fm u).lam 0) Z).det) + ∑ c, ∑ τ, (wsum … * card Z.J0) * (CV.Q c τ).mu
```
**read**: `gramZ` is the real Gram matrix of an integral basis of a representation space under `nfAll`, a pairing built from the Fock pairing `fockF` (PColInf.lean:125-126). In words: the slope of the column lattice equals −log det(Gram)/rank plus a weighted sum of local slopes. **proved-by**: `standard_basis_z` (PZBasis.lean:291) proves `ZBasisStd` (PColSlopeEq.lean:17-19), which evaluates that determinant. *inferred*: the determinant computes the archimedean side of the slope inequality in the second note.

**Chain (read):** `col_mu` ← `colSlopeEq_of` (PColSlopeEq.lean:36) ← `colSlopeEq_of_Q` (PZBasis.lean:307) ← `column_lattice_exact_slope` (ColumnLatticeExactSlope.lean:204) ← `lower_slope_inequality_family` (LowerSlopeInequalityFamily.lean:12-15) ← field `hZa` (TuSizeOfRealPlaceSecondLayer.lean:21) ← `link_gl` (LinkGl.lean:26) ← `shape_closed_link_n_of_green` (TopShape.lean:35) ← TopPlug. **On path.**

### 2.5 On path: an archimedean Gram determinant that is ≥ 0

`FormalDegreeBessel/StatementG.lean:165-174`
```
def GGram : Prop := ∀ k r z z', inWb k r z → inWb k r z' → ∀ g ∈ UH (Hpk k r),
    ((Gf k r z z' g : ℝ) : ℂ) = (-1) ^ (r + 1) * (gramM k r z z' g).det
def GNonneg : Prop := ∀ k r z z', inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ g ∈ UH (Hpk k r), 0 ≤ Gf k r z z' g
```
**read**: `Hpk` is an indefinite Hermitian form, and g ranges over its unitary group. Gf(g) = |D_{r+1}|² − T(z)T(z′)|D_r|², where D_l is the leading l×l minor of the matrix of pairings ⟨g f′_b, f_a⟩ (64-88). `GGram` says Gf is ± the Gram determinant of the 2(r+1) vectors f_a and g f′_b; `GNonneg` says Gf ≥ 0. **proved-by** `gGram`, `gNonneg` (FinalG.lean:21-22).

**Chain (read):** `gNonneg` and `gGram` ← `regular_pos_compl` (FlagMeasures/RegularPosCompl.lean:15, 20) ← Bessel orbital-integral bounds (IsometryOpNormBoundedByTwoFrames.lean:343; BesselOrbitalIntegralEqInvDegSmul.lean:203; LintegralHilbertSchmidtNormSqBesselAmplitudeLe.lean:131) ← amplitude Schur bounds (RowAmplitudeBoundsUniformSingletonWidth.lean:94) ← DiagonalRowOfSiegelWeilUnitary.lean:53 ← MainTheoremPublishedInputsThird.lean:25 ← OpenOrbitOfUnramifiedExponents.lean:50 ← `nonempty_hyps_definite_side_of_closed_bound` (SiegelEisensteinSecondTermHypotheses.lean:58) ← :72-73, which calls `every_character_of_green_v_win`. **On path.**

### 2.6 On path: the iterated Rallis scalar

`Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/RealLowestKTypeCoeffSquareIntegrable.lean:46-48`
```
def BForm : Prop := ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ t c (z : Fin D.R.m → ℝ), (∀ i, IsLval R i t c (z i)) →
    ∀ x ∈ GlobalTheory.Hk3.EEc R SF c, R.Th t (LinearMap.adjoint (R.Th t) x) = ((κ₀ * ∏ i, z i : ℝ) : ℂ) • x
```
**read**: on the c-eigenspace, the composite lift followed by its adjoint is the scalar κ₀·∏ z_i, where z_i satisfies `IsLval` at step i. **proved-by** `GlobalTheory.ChainScalar.bForm` (TwistedOperators/LevelGroupActionOnAdelicFunctionsEqZeroOfNoLift.lean:350). It is proved from `Scalars` (LabelSettingScalars.lean:74), which says that each lift step multiplies inner products by κ(k+1)·l (`StepScalar`, 57-60). *inferred*: Rallis's inner product formula, iterated. The Gram determinant of the lift would then be a power of κ₀∏z_i, but I found no statement on this chain that takes it.

**Chain (read):** `bForm` ← `upInj` (ThetaLiftAdjointScalarFormulaInjective.lean:37) ← `thetaLift_adjoint_scalarFormula_injective` (…Statement.lean:27; its hypotheses include published Weil–Siegel for unitary groups) ← `scal_matchUp_upInj` (ThetaLiftScalarIdentityMatchingAdjointInjective.lean:38). The chain continues through HoldsLOfTies.lean:44, HoldsOfMultiplicityEqual.lean:20, ExistsBareFormOfSaturation.lean:22, CompatibleSystemWeightOneSaturated.lean:15, MemberBundlesLargeUnramifiedExponents.lean:54 and HypothesesNonemptyOfUnramifiedExponents.lean:43 to `nonempty_hyps_definite_side_of_closed_bound` (:68), then TopPlug. **On path.**

Three tidier statements in terms of the datum D7 are not in the cone, so they are off path. `InnerProductFormulaField.ExactRallisProduct` (SharpRestriction/Divisibility/InnerProductFormulaField.lean:290) says ι∘θ_Up = κ∏λ. `PointsLemma` (:299) says ι_Qι_Q* = κ∏λ on an orthonormal basis. `CayleySignature.TowerRallisLemma` (CuspSpanNormBounds/CayleySignature.lean:204) says the iterated lift pairs nontrivially.

### 2.7 Index and covolume as determinants: on path

- `HermDual` (FockGram/StatementHerm.lean:14-28), **read**: [hdual L : L] = |N(det G_S)|, and L is self-dual exactly when det G_S is a unit. **proved-by** `hermDual` (SymGramPosSemidef.lean:21). Chain (read): `stdLat_unimod` (Spaces.lean:106) → `stdSpace` (:140) → `posSpace` (:150) → IwasawaDecompositionUnitary.lean:33 → SiegelWeilSchrodinger/Bridge.lean:31 → CoefND.lean:25 → EveryCharacterOfLiteratureOfVWin.lean:512 → :716, a field of `published_results_eigen` (:666) → :811. On path, inside a literature item (Siegel–Weil for unitary Schrödinger models).
- `CovolGram` (StatementLat.lean:75-78), **read**: covolume = √det Gram. **proved-by** `covolumeEqSqrtDetGram` (CovolGram.lean:10). Chain (read): GenusCovolBound.lean:149 → DecoFin.lean:86, 195 → ColFormsLemmas.lean:85 → RowFormsLemmas.lean:38 → HeckeCSDICommTrRep.lean:139 → SquareIntegrableColumnsTied.lean:43 → `BundleCondition` (ColumnChoiceWithTies.lean:53) → `HypsAlt` (Hyps.lean:24), which is a hypothesis of `every_character_of_green_v_win`. On path.

## 3. ThetaLiftIndependence and FockGram, in words

These are in `ThetaLiftIndependence/Statement.lean` unless noted. **read**

- `chainOpM` (52-57): the m-fold composite of kernel operators f ↦ (j ↦ Σ_i w_i·K_{ij}(f_i)). *inferred*: the iterated theta lift as weighted sums over genus classes. On path (read): PerCol.lean:12 → AdmissibleAtGeneratorPlaces.lean:294, 338 → ClosedFamilyAdmissibleTwistLink.lean:31 → TopShape.lean:40.
- `RallisHyp` (232-235): ⟨θx, θy⟩ = c·L·∏Z_v·⟨x, y⟩ on S. `RallisAdj` (237-242): then θ*θ = (cL∏Z_v)·id.
- `ChainScalar` (244-251): if T_jT_j* = c_j on S_j and T_j* maps S_j into S_{j+1}, then the composite T of the m maps satisfies TT* = ∏c_j on S_0. This is not the namespace `GlobalTheory.ChainScalar` of §2.6.
- `DetBlocks` (260-264): if A acts by c_s on the pieces E_s of a direct sum, det A = ∏ c_s^{dim E_s}.
- `DetChain` (266-276): if A acts on E_s by κ∏_j λ_{j,s} and B_j acts on W_{j,s} (same dimensions) by λ_{j,s}, then det A = κ^{dim E}·∏_j det B_j.
- `DetSwap` (284-292): det(T*T on (ker T)^⊥) = det(TT* on (ker T*)^⊥). `EigenSwap` (294-299): BA and AB have nonzero eigenspaces of equal dimension.
- `LatSeeSaw` (186-198): ⟨Lift f, g⟩ = ⟨f, Lift* g⟩ for finite lattice sums, the seesaw in finite form. `RowsQuot` (253-258) and `GaussOpAdj` (278-282, the adjoint of the Gauss operator) belong to the same group.
- `ChainInt` (40-45): multiplying the composite by ∏D_j makes it integral.

None of `RallisHyp` through `ChainInt`, nor `RowsQuot` or `GaussOpAdj`, has a proof, and none is referenced: DetSwap.lean builds only an isomorphism (line 45), and EigenSwap.lean proves one inequality (line 7). Off path.

- `GaussOp` (208-213), **proved-by** `gaussOp_eq` (GaussOp.lean:37), restated as `final_gaussOp` (FinalThetaLiftAMFKIndep.lean:13): used only at RankBoundMonotoneInDimension.lean:223, which is not in the cone. Off path.
- `ClassRepsDefinite` (175-184) and `LatLiftIndep` (158-165), **proved-by** ClassRepsDefinite.lean:82 and LatLiftIndep.lean:78: used by `massBasic` (MassBasic.lean:43), which leads through UnramifiedOfIsCMUnram.lean:151 and `genusMassAt_two` to HypothesesNonemptyOfUnramifiedExponents.lean:60. On path; this chain comes from the trace, and I read only its first, second and last hops.

FockGram: `SymGramPosSemidef` and `SymGramPosDef` (StatementSymPos.lean:10-16) say that Sym^a of a positive (semi)definite Gram matrix, times diag(symFact), is again positive (semi)definite. `DetSymPow` (StatementFock.lean:54-56) says det Sym^a(A) = (det A)^{C(n+a−1, n)}. `DetFockSym` (63-68) is its Fock-Gram form. `FockStd` (70-75) says monomials are Fock-orthogonal with multifactorial norms. None has a proof: the file `SymGramPosSemidef.lean` proves only `fockHerm`, `subIndexNorm` and `hermDual`. All are unreferenced and off path.

## 4. Alternative end-games (no proof, unreferenced, not in cone)

- **ProductFormula.** `OCCMEstimate` (StatementOCCM.lean:114-122), **read**: take a prime l = 2f+1, a CM type Φ ∋ 1 of (ℤ/l)^×, a set Bad outside which no prime power below x is ±1 mod l, parameters `Params`, and `TypeParams` for Φ and for its dual type with mean logOm ≥ γ + log(π/v) − ℓ. Then G(x) ≤ xℓ + 2xΣ_{Bad} log p/p + K·MainCM, where MainCM = (xL/m + xmL/k)/r + xη/m + xL/f + kfL² (111-112). `OCCMToZeta` (124-135): such data at all large x give ζ ≠ 0 for Re s > θ. `ZetaQuarterPowerCorollary` (137-151): with m ≍ x^{1/4}, k ≍ x^{1/2} and l ≍ x^{1/4}, ζ ≠ 0 for Re s > 3/4. *inferred*: with those sizes every term of MainCM is about x^{3/4}.
- **HalfLinks.** `HalfLinksCore` (HalfLinks/Statement.lean:84-116) bounds the prime-power count at x/c_j for the m Chebyshev nodes c_j by xB(log(x/c_j) − 1 − γ + Σ coef·ell) plus errors (102-106), with Σ top ≤ Cx^ε·mB(x/m + xm/k) (108). `HalfCore` (128-134) concludes chebAvg(G) − Σ coef·chebAvg(G_ψ) ≤ K′x^{θ+3ε}. `RiemannHypothesisOfHalfLinks` (144-149) concludes RH. Two further unproved end-games mention `HalfLinksCore`: JacobiWeightFamilies/Statement.lean:57 and WideWeightTheorem/Statement.lean:66.
- **Root files.** `ZetaLandau` (StatementU.lean:14-17): if s₀G(x) ≤ Cx^θ eventually, then ζ ≠ 0 for Re s > θ. **proved-by** `zetaLandau` (ZetaNonvanishing/ZetaLandau.lean:258). Its only users are outside the cone; the path's Landau step is `Deduction.zeroFree_of_rpow_window` (LandauTheorems/ZeroFreeOfRpowWindow.lean:11). The following variants have no proof:
  - `ZetaNonvanishingGeneralWeights` and `…SpreadWeights` (12-24), and `ZetaNonvanishingChebyshevWeights` (30-34): the same conclusion from weighted averages of G at m ≥ x^{1−θ−ε} points.
  - `FamilyLandauC(W3)` (StatementFL.lean:21-42): ζ(ρ) ≠ 0 where all L(χ_i, ρ) ≠ 0.
  - `ForcedSumCM` (StatementCM.lean:35-39): b·S(a/b) minus the sums over the classes counted by Φ and by its dual type lies in [0, 3(a/l)log(a/b)(1+log(a/b)) + a log l/(l−1)].

  `ZetaRealNonvanish` (ZetaRealNonvanish.lean:63) and `RHofHalfPlane` (:74) are proved (ZetaNonvanishing/ZetaRealNonvanish.lean:322; RHofHalfPlane.lean:44) but are not in the cone.

## 5. Other candidates

- `ThetaPos` (LatticeTheta/Statement.lean:71-72): θ_Λ(t) ≥ 1. **proved-by** ThetaShiftInversion.lean:33; unreferenced.
- `WeilFinite` (HermitianLattices/StatementTheta.lean:39-44): the identities of the finite Weil representation. No proof; unreferenced.
- `MassTelescope` (StatementMass.lean:78-88): the Prop has no proof, but its step lemma `massTelescope_step` (MassTelescope.lean:116, which assumes `SiegelMassRatio`) is used at UnimodularHermitianMassMulLeMass.lean:149. That use leads through RowsPosTypeP.lean:10 to HypothesesNonemptyOfUnramifiedExponents.lean:58; I read those hops only. On path.
- `DetDivides` (SubspaceCounting/StatementW.lean:43-49): a power of the letter determinant divides a polynomial that vanishes to high order. **proved-by** DetDivides.lean:730. Not in the cone; not about periods.
- `BesselPeriodGGP` (PeriodIntegrals/BesselPeriodGGP.lean:105-120): under `InterlacingCondition` (27-30: v_i < u_i and u_{i+1} < v_i), the local Bessel period integral is nonzero. *inferred*: the note's "values 0, 1 meaning interlacing". No proof was located. Its only use, `besselPeriod_iff` (SymmetricMeasureL2NormEqResolutionL2.lean:382), is not in the cone, so it is off path. Two copies of `InterlacingCondition`, in BesselL2FixAtZero.lean and CayleySignature.lean, lie inside the cone with no verified chain: undetermined.

## Not read

- Proofs of `gramWindow2_proved`, `GGram` and `bForm`.
- The meaning of `IsLval`, `EEc`, `bejj` and `nfAll` beyond their types, so whether the z_i are central L-values is not established.
- The namespace `GlobalTheory.SeeSaw` (Definitions/LatticeFrames/), which files on the path open.
- The path status of LatticeSlopes (`GramDetLe`): the trace's chain runs through a mis-resolved field name, so it is undetermined.
- How `MeanBoundSecondForm` is consumed: no declaration names it; `ChainTied` uses `Data` and the `Tie*` records.
