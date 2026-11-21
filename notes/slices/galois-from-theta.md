# Galois representations from theta lifts: how `Row0b` is proved

Read 2026-11-20 from source text only (build unfinished); continues `spine-first-reading.md` §6–7. Tags: **[R]** statement or definition read and transcribed; **[P]** proving theorem located; **[I]** my interpretation. Paths are under `lean/src/Development/`: `GR` = `AutomorphicArithmetic/Foundations/GaloisRepresentations`, `GF` = `GR/IntegralStructures/GeometricFlagBases`, `CD` = `GR/IntegralStructures/CrystallineDescent`, `TP` = `GR/ThetaParseval`, `GG` = `AbelianVarietyTheory/Definitions/GaloisGeometry`.

## 0. The shape

Every unitary group here is `UA n := UJ (conjAd E) 1` (`AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BaseChangeDefiniteUnitary.lean:71`), the unitary group of the identity Hermitian form over the CM field E. [R] It is definite at every infinite place. [I]

## 1. From `TLiftK` + `GeoOne` to `Row0b`

`GR/IntegralStructures/Development.lean:20-31` [P]:
```
coreAll_of seed cong up := coreAll_of_core (toCoreK up congPhi_holds descOffT (limFinOdd_of seed cong))
galoisLocalGlobal_of_geometry_lift geo up := rest (coreAll_of (seedFinOdd_of_geoOne geo) (congFinOdd_of_ex wtLacEx_holds) up)
```
`toCore` (`CD/LimOddOfLimFinOdd.lean:48-61`) composes `limU_of_limOdd`, `joinU`, `joinAll`, `joinGL`, `joinUp`, `joinEnd`. [P] In order:

1. **`SeedFinOdd := SeedWU4 Odd TyEll (GenOf DGen) WtLac`** (`GG/LimWU4OfLimWU3.lean:103`, body :15). [R] Hypotheses on U′ on U(a), a odd: `TyEll` (`AbelianVarietyTheory/Definitions/Divisors/GenOf.lean:14`), a vector transforming under a compact open J ⊂ GL_a(E_{w₀}), w₀ | l split, by a non-trivial character of l-power order, such that every smooth irreducible representation containing it is supercuspidal; `WtLac` (`GG/LimWPhi.lean:24`), U's weights at embeddings not over w₀, v′ (`SameWtOff`) and gapped jumps at a second l-adic place v′; Satake parameters at chosen places not killing the polynomial `DGen` (`GG/LimWPhi.lean:14`). [R] Conclusion: continuous semisimple r : G_E → GL_a(Q̄_l) with char r(Frob_w⁻¹) = ∏(X − b) over the Satake parameters scaled by q_w^{(a−1)/2} (`algSat`, `AutomorphicArithmetic/AutomorphicVarieties/AutomorphicForms/BlochKatoSelmerVanishes.lean:74`) at almost all split places of type `UsPl d`, and crystalline/de Rham with the right jumps (`CrysDRU`) at chosen l-adic places. [R] Proof: `seedFinOdd_of_geoOne` (`GR/IntegralStructures/ZetaCharacterDivisibility/MainFin.lean:13`). [P]
2. **`CongFinOdd := CongUW4 …`** (:105, body :37): for every U on U(a), a odd, its Hecke eigenvalues θ lie in the `PolyApprox`-closure of eigen-systems of forms U′ meeting the hypotheses of step 1. [R] `PolyApprox θ S` (`GG/PolyApproxZeroPadic.lean:10`): `∀ ε>0, ∃ finite s ⊆ S, c, ∀ P ∈ ℤ[X_J], ‖P(θ) − Σ_{η∈s} c_η P(η)‖ ≤ ε`, ultrametric. [R] Proof: `congFinOdd_of_ex wtLacEx_holds` (`GR/IntegralStructures/CongruenceOddLevel/CongFinOddOfLvLac.lean:15`), `wtLacEx_holds = top_of famEx_holds famProj_holds famWt_holds` (`GR/WeightCharacters/LadicWeightEmbeddingOverPlace.lean:73`). [P] `FamEx` (`GR/WeightCharacters/DeltaNear.lean:175`): an algebraic modular form on U(a) is l-adically approximated, within any ε, by a family of forms whose weight at v′ is within 2d of any prescribed ν (`FamWt`, :114). [R] This is the classical weight-changing congruence on a definite group. [I]
3. **`LimFinOdd := LimWU4 Odd`** (:107, body :57): every U on U(a), a odd, has an a-dimensional r with Frobenius = Satake at `UsPl d` places, `CrysDRU` at l-adic places away from w₀, v′, and l-adic approximation of its Weil–Deligne Frobenius traces there. [R] Proof: `limFinOdd_of seed cong := limWU4_of …` (`GR/TraceLimits/LimFinOddOf.lean:197`). [P] r is a limit of traces (`LinApprox`, `PolyApproxZeroPadic.lean:17`). [I]
4. **`LimU`** (`CD/LimOddOfLimWU3.lean:37`): Weil–Deligne char polys at l equal the Satake ones, via `ClosedPhi` (`congPhi_holds`). [P]
5. **`JoinU : LimU → CoreUd`** (`CD/PatchOneAlt.lean:107`): odd rank, all clauses at all `UsPl d` places. [R]
6. **`JoinAll : TwoUpOK → CoreUd → AllUd`** (:109): all ranks, via `SubtractQ` (`TP/CoreAtQIffRowQ.lean:195`: `(∀ d odd, CoreAtQ d) → TwoUp E n → CoreAtQ n`). [R]
7. **`JoinGL : DescOffT → AllUd → CoreGLu`** (:111): from U(n) to GL_n. [R]
8. **`JoinUp : JacquetShalikaRigidity → GelfandKazhdanDual → QuadLift → CoreGLu → RowCsd`** (:113): to all CM fields, by quadratic CM extensions and patching (`StepDown`, :85). [R]
9. `JoinEnd` yields `Core := Ex .csd ∧ ∀ c, SphericalLevelCondition .csd c` (`GG/CyclicStrongAtCusp.lean:94`): an attached continuous ρ (`Weak`) obeying the unramified, de Rham, crystalline and Weil–Deligne clauses at split unramified places. [R] `coreAll_of_core` gives `CoreAll` (:96): any polarization, every such place. [P]
10. `rest` (`Development.lean:24`) gives `Row0` via `R1` (`AbelianVarietyTheory/Statements/EllipticCurveLevels/IsQg.lean:13`) and `LocalGlobalCompatAtIwahoriFixedPlaces` (`GR/SphericalGaloisCompatibility/PAdicSplitting/LocalGlobalCompatAtIwahoriFixedPlaces.lean:16`); `Row0.row0b` weakens it to `Row0b`. [P]

**Base change.** `DescOffT` (`GG/MatchOfMatchOffTEmpty.lean:32`) [R]:
```
∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) → ∀ Z, ∃ T, NonSplitSet T ∧ Disjoint T Z ∧ ∃ U, MatchOffT U π T
```
`MatchOffT` (:26): U automorphic on U(a), unramified at non-split places off T, with π's split local components and infinitesimal character. [R] Proof: `desc_of speh compUnique oneFactor jacquetShalikaBound cuspidalMultiplicityOne splitRigid thin unitOf weakAll` (`GR/BaseChangeDescent/BcBackOffT.lean:28-31`). [P] Labesse-type descent. [I] `QuadLift` (`GG/IsWeight.lean:90`) enters step 8 as `quadLift strongTC_holds jacquetShalikaRigidity`. [P]

**Local–global compatibility.** Away from l, `Row0b` asserts, for every rc with `IsRecT`, `AwayB (WD of r at w) (rc π_w)` (`GR/TypeConditions/WeightsConjBis.lean:26-31`) [R]:
```
dim : x.lpDim = y.lpDim
tor : Tor y → y.mono0 → x = y
tame0 : IsQpBig w y.lpDim → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g, deg g = 0 → x.charPol g = y.charPol g
```
`Tor y`: commutators of the Weil group act trivially (`WeightsConjAlt.lean:27`); `IsQpBig w n`: E_w ≅ ℚ_g with n = 1 or 16n² < g (`WeightsConjBis.lean:15`). [R] So: exact match when π_w's parameter is a sum of characters with N = 0; inertia char polys for tame "square-free" parameters at large ℚ_g places; nothing for other ramified π_w. [I] At l, `AboveB` gives crystalline and de Rham with the infinitesimal character's jumps where π_w is spherical, and potentially semistable with the same `AwayB` comparison in the toral and tame cases. [R]

## 2. `GeoOne` and its proof

**Statement** (`GF/HodgeTrAt.lean:79`, trimmed) [R]:
```
∀ E l ι (a odd) d, FieldOK E l d → ∀ x, x^2 = −d → ∀ T, NonSplitSet T → ∀ w₀ v' above l, Apart v' w₀ → OneK x w₀ v' →
 ∀ S U, AutOffT T U → TyEll E l a w₀ U → SphOffU w₀ S U → (∃ B, SatU U v' B) → LacWtAt ι v' U →
 (∃ dd ρ, VBase ι d U ρ) ∧
 (∀ w, UsPl d w → l ∉ w → (∃ B, SatU U w B) → ∃ dd ρ, VBase ι d U ρ ∧ ∀ B, SatU U w B → ESAt ι ρ w (algSat a (normV w) B)) ∧
 ∀ w ∋ l, OneK x w v' → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) →
   (∃ dd ρ, VBase ι d U ρ ∧ CrysAt ρ w ∧ JumpsOcc U ι ρ w) ∧ ∃ dd ρ, VBase ι d U ρ ∧ ∀ B, SatU U w B → PhiKilled ι ρ w a B
```
Data: x = √−d (`FieldOK`, `GG/LatticeDataThicknessBound.lean:16`); w₀, v′ | l over different places of F⁺, one place of ℚ(x) (`OneK`, `HodgeTrAt.lean:49`); U of type `TyEll` at w₀, spherical off w₀ and S, lacunary weight at v′ (`LacWtAt`, `GG/DivisionOfDeterminantCharacter.lean:125`). [R] Conclusion: continuous semisimple ρ of some dimension dd with `VBase` (`GR/IntegralStructures/ZetaCharacterDivisibility/InsideRefl.lean:73`): at almost all split w ∤ l with −d square below w (`UsPl`), `ESAt` (`DivisionOfDeterminantCharacter.lean:94`), i.e. ρ is unramified and ∏(X − b) over U's normalized Satake parameters annihilates ρ(Frob_w⁻¹); and Hodge–Tate jumps containing a lacunary set of a integers at some l-adic place (`HTRichEx`, `InsideRefl.lean:54`). [R] Also `ESAt` at any prescribed such w; at l-adic w, crystalline with jumps containing U's weights (`JumpsOcc`, :64), or crystalline with Frobenius char poly dividing a power of the Satake one (`PhiKilled`, :48). [R] So GeoOne only places Frobenius eigenvalues among Satake parameters; step 1 of §1 cuts the a-dimensional r out by genericity and lacunarity. [I]

**Proof term.** `geoOne_holds := geometric_realization_of_weight_one weight_one_geometric_realization` (`GF/WeightOneGeometricRealization.lean:11`), the second being `lefschetz_fixedPoint_finite_etale_correspondence : HolomorphicLefschetzFormula` (:7; `AbelianVarietyTheory/Proofs/SatakeParameters/LefschetzFixedPointFiniteEtaleCorrespondence.lean:8`). [P] `geometric_realization_of_weight_one hW := geoOne_of_parts steps_holds (kodaira_spencer_of_weight_one hW) planEx_holds` (`GF/GeometricRealizationOfWeightOne.lean:25`) `= geoOne_of Steps (packEx_of KSAll PlanEx)` (`GF/GeoOneOfParts.lean:7`). [P]

**Geometric objects.** [R]
- `HTower k` (`AbelianVarietyTheory/Definitions/Divisors/IdTower.lean:9`): a k-scheme Z with correspondences s_g, t_g : Y_g → Z; `Nice`: Z smooth projective, s_g finite étale (`GF/IsGrRefl.lean:31`).
- `piece` (`IsGrRefl.lean:54`): joint eigenspace, eigenvalues θ(g), of `hop g` on L ⊗ `Htot l` of Z over Ω; `IsMat`, `IsGr` (:60, :66): ρ is the block-diagonal part of the Galois action on it.
- `KS L gb k` (`GF/IntegOfMem.lean:48`): Z_N ≅ k-fold fibre power of the universal abelian scheme over `Model b N` (`AbelianVarietyTheory/Definitions/Divisors/NotCompactOfMEqOne.lean:200`: smooth of relative dimension D.a·(D.n−1), representing abelian schemes with O-action, polarization, level structure), with Hecke correspondences.
- `Sc` (`IntegOfMem.lean:193`): `D.a = 1, D.m = 1, G.a = 1, Odd G.n, D.CompactB`; `HTGroup` (`AbelianVarietyTheory/Definitions/Divisors/IsCyclotomicExtensionQI.lean:395`) has signature (1, n−1) or (0, n) at each infinite place (:433).

These are Kuga–Sato varieties over compact Harris–Taylor-type Shimura varieties of dimension a−1, and `Htot` is l-adic étale cohomology. [I]

**Steps** (`GF/MapInvMul.lean:19`). [R] `RepEx` (`HodgeTrAt.lean:103`): pieces carry continuous semisimple Galois representations. `ESStep` (:107): `CongAt` (`IsGrRefl.lean:114,133`) plus `HasRoots` gives `ESAt`. `CrysStep` (:112): a finite étale Galois cover, through Hecke correspondences, of the generic fibre of a smooth projective O_w-scheme gives crystalline. `JumpStep` (:117): a θ-eigenvector in Hodge cohomology H^{j,·} gives jump j. `PhiStep` (:122): the congruence relation gives `PhiK` at l. [R] Proofs: `SmoothModelCrystalline` (`WeilBound/CoreStatements/PadicHodgeComparison/EtaleCohomologyComparison/SemistableModelSemistable.lean:46`: étale H^n of a smooth good model is B_cris-admissible) for `CrysStep`, `PhiStep`; `htSpecGood` (`GR/CrystallineTowers/ClosedHT.lean:21`) for `JumpStep`. [P] `KSCong` (`IntegOfMem.lean:222`) supplies `CongAtW` from `CongGrp` (:183), whose Hecke operators have index `Nat.card (Gr (𝓞/𝔴) ((𝓞/𝔴)^n) i)`. [R] With `PtId` (`GR/AnnihilatorModels/GenericMulOfProd.lean:149`, an alternating identity between q-Frobenius-twisted points and the correspondences) this is the Eichler–Shimura relation at split places. [I]

**Hodge numbers.** `KSAll` (`GF/PackExOf.lean:93`) = `StdEx, KSEx, KSNice, KSGood, KSCong, KSHodge`; `KSHodge` (:25): the eigenpiece's Hodge cohomology is nonzero in the degrees h_i of `IsHExp` (`GR/LefschetzSigmaSums/InvPol.lean:21`). [R] Proof: `ksHodge_of_geo hW FixK_holds` (`GR/LefschetzSigmaSums/KsHodgeOfGeo.lean:7`). [P] `HolomorphicLefschetzFormula` (`GR/LefschetzSigmaSums/HodgeTraceFromLefschetzAndGroupSide.lean:102`): for Z smooth projective over ℂ and a finite étale correspondence with isolated non-degenerate coincidences y (tangent map A_y), Σ_b (−1)^b tr(c₁* c₂^* | H^b(Z, Ω^a)) = Σ_y [X^a]det(1 + X·A_y)/det(1 − A_y). [R] `FixK` (:125) equates these terms, for Hecke correspondences composed with fibre endomorphisms α, with a group-theoretic sum `cxTotalM`; `GroupTop` (`GR/LefschetzSigmaSums/HeckeTraceSemi.lean:122`) equates that with `dTrace ξ f · Σ_i y^{h_i}`. [R] Hodge numbers are thus read off a fixed-point count. [I]

**Placing U.** `PlanEx` (`PackExOf.lean:82`) gives a `Plan` (:43): a prime p, PEL data with `Sc` and D.n = a, Hecke eigenvalues θ, and f with `Spec` (`HeckeTraceSemi.lean:24`: every polynomial s in the Hecke operators with s(θ) ≠ 0 has nonzero discrete trace `dTrace` in weight λ). [R] `planEx_holds` (`GF/PrimeLevelLocalization/SpecTopHolds.lean:9`) uses `Frame` (`PrimeProj.lean:23`): `j : GUf E n →* S.G.GAf`, surjective, kernel the elements trivial away from p. [P] `FrameEx` (`PrimeProj.lean:145`) assumes `Odd n`. [R]

## 3. Why lift: `TwoUp`

`FrameEx` needs odd rank, so even rank is lifted. [I] `TwoUp E n` (`TP/SplitLineSubtraction/RowDefOfOdd.lean:98`), n even: odd t, a Hecke character κ and two lifts U₁, U₂ on U(n+t), n+t odd, with `IsUp` and `∀ i j, ψ₁ i ≠ ψ₂ j`. [R] `IsUp` (:85) [R]:
```
sat : ∀ w split, κ, ψ_i unramified → SatU U w B → ∃ B', SatU U' w B' ∧ algSat (n+t) B' = (algSat n B)·κ(w)⁻¹ + {ψ_i(w)}
inf : wtJumps λ' = (wtJumps λ).map (· + m) + {−p_i}
```
By `Dict` (`TwoUpOKOf.lean:14`), ψ_i(w) = χ_X(w)·N(w)^{(n+2t−2)/2 − i}, a segment of the splitting character. [R] So ρ_{U_j} = ρ_U ⊗ κ⁻¹ ⊕ (t known characters), which `SubtractQ` removes; disjoint lifts make that unambiguous. [I] `twoUpOK_of_steps` (`TP/TwoUpOKOfSteps.lean:13`) takes t = 2(d₀+n)+1 and χ_W with infinity type m_W ≤ 2b − (n+t), b a lower bound for U's weights, so `TLiftK`'s weight hypothesis never restricts U. [R]

## 4. How the lift exists

`TLiftK` (`TP/HalfIndexLattices/TLiftK.lean:12`, trimmed) [R]:
```
∀ E B, W.GoodK (cj E) B → ∀ n ≥ 1, ∀ X, X.J = 1 → X.IsHerm (cj E) B n 0 → ∃ d₀, ∀ d ≥ d₀, ∀ W δ, W.J = δ • 1 →
 W.IsSkew (cj E) B d 0 → ∀ χX χW mX mW, IsHecke χX → IsHecke χW → ResEtaPow χX n → ResEtaPow χW d →
 HasExp χX mX → HasExp χW mW → ∀ U λ, IsAutRepU U → (∀ w, HasWeightAt U w (λ w)) →
 (∀ w k, d + mW w ≤ 2·(λ w)_k) → ∃ U', IsLift B χX χW mX mW λ U U'
```
Both groups are compact at infinity. [I] `IsLift` (`TP/SchurStep.lean:106`): U′ automorphic; weights by `IsLiftWt` (:103: 2λ′_k = 2λ_k − d − m_W + n + m_X for k < n, else n + m_X); at split places, `LocPair` (:93), a nonzero GL_n × GL_d-intertwiner out of the local Weil representation twisted by χ_W⁻¹, χ_X. [R]

Proof: `tLiftK := tLift_holds_k` (`TP/ThetaKernels/TLiftK.lean:4`) `= tLift_of_tools_k tools_holds_k (hgtEx_of_k stab2Cpt_k)` (`TPGHolds.lean:58`) `= tLift_of_k T hH brEx hgtFst realPair (nonVan_k T rallis decomp bumpAny datum tail absNe schurStep) liftAut projEx readLift` (`TPGTop.lean:46`). [P] `tLift_of_k` (`GalTPDefs.lean:141`) sets d₀ = max(N, 2n), N > 2t₀, t₀ an integrability exponent of a height on U(X). [R] `lift Φ φ h = ∫_{dom} θ(Φ)(g,h)·conj φ(g)`, `mc φ g = ⟨R(g)φ, φ⟩` (`SchurStep.lean:22,25`). [R]
- `Rallis_k` (`GalTPDefs.lean:61`): if t₀ < d/2, coef(Φ)·conj mc(φ) is integrable and `lift Φ φ = 0 → ∫ coef·conj mc = 0`. [R] `rallis_k` (`TPGRallis.lean:99`) uses `SWFullX_k` (`ThkBaseStmtX.lean:33`: an Eisenstein series `Ê` of the doubled section continues to s₀ = (d−n)/2 and `Ê s₀` is 1 or 2 times the U(W)-average of `thetaSum`), `DblX_k` (:17), and an identity-theorem step from Re s large to s₀. [P] This is the Rallis inner product formula by doubling and Siegel–Weil, in its absolutely convergent range. [I]
- `SchurStep_k` (`GalTPDefs.lean:106`): `∃ κ ≠ 0, ∀ c, ∫_{U(X)_∞} coef(x)·conj mc(φ)(x c) = κ·coef(1)·conj mc(φ)(c)` for vectors of one K-type. [R] Schur orthogonality on the compact archimedean group. [I]
- `NonVan_k` (:114): for d ≥ 2n, t₀ < d/2, some finite-place Schwartz data φ_f gives `lift (pure f₀ φ_f) φ ≠ 0`. [R] `nonVan_k` (`TPGNonVan.lean:26`): bumps concentrate coef near 1 (`BumpAny`, `Datum`), `Tail` bounds the rest, `AbsNe` gives ∫ coef·conj mc ≠ 0, `Rallis` gives lift ≠ 0. [P] No L-value is computed; it is a direct stable-range estimate, as in J.-S. Li. [I]
- `LiftAut`, `ProjEx`, `ReadLift` (`SchurStep.lean:234, 243, 258`) project to an irreducible U′ and read weights and `LocPair`. [R]
- `SplitStab.lean` holds `GoodK` (:18, used by `TLiftK`) and `IsLatRepK` (:26, field `splitStab` :43), which grep finds unused elsewhere. [R]

## 5. Against the published constructions [I]

Shared with Clozel, Harris–Taylor, Shin: descent to definite U(n), a signature-(1, n−1) group matching it at finite places, cohomology of compact PEL Shimura varieties with Kuga–Sato coefficients, Eichler–Shimura, crystalline comparison (odd rank only). Different: Hodge numbers by holomorphic Lefschetz, not Faltings's BGG; no stable trace formula named; even rank by theta lift; hypotheses removed by l-adic congruences and trace limits, doing eigenvarieties' work for Chenevier–Harris though none is named; away from l only `AwayB`, short of Caraiani.

## 6. The three literature rows

`OpenLiteratureStatements` (`AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215-218`) [R]:
```
caraianiLocalGlobalDual : UpperTheory.One.M.Row
localLanglandsExists : UpperTheory.Zero.LLC.RecTExists
galoisRepOfPolarizedPairLit : UpperTheory.One.M.Row
```
`UpperTheory.One.M.Row := Row0b (fun h rc => IsRecT h rc)` (`AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/RecT.lean:6`): both named rows are `Row0b recT`. [R] `RecTExists`: each place carries an rc with `IsRecT` (`AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:76`), whose laws `LawsT` (:55) cover dimension, characters, segments, twists, central characters, duals, injectivity, depth, but no L- or ε-factors; `RecTUnique` (:82) asserts uniqueness only on `Good` representations. [R]

Discharge (`AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7-14`) [P]:
```
everyCharacter_of_row h := every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ (vwin_of_row h)
everyCharacter := everyCharacter_of_row galoisLocalGlobalStrong_recParameter
riemannHypothesis := riemannHypothesis_of_everyCharacter everyCharacter
```
`galoisLocalGlobalStrong_recParameter := galoisRepresentations_of_thetaLift tLiftK` (`GR/IntegralStructures/RowSrc.lean:6`). [P] `recTExists` (`AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20`) is built from `artEx`, `cuspEx`, `exists_isLExt`. [P] `goodMap` picks its map by `Classical.epsilon` of a relation (`AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/GoodMap.lean:144-149`). [R] So no row is an assumption of `riemannHypothesis`: two are the theta-lift theorem under a label naming Caraiani, the third an in-tree construction. [I]

## Not read

Proofs of `seedFinOdd_of`, `limWU4_of`, `congUW4`, the `join*` lemmas, `coreAll_of_core_inp`, `rest`'s inputs, `esStep`, `KSEx`, `KSGood`, `KSCong`, `specTopG`, `desc_of`, `QuadLift`; `GeoCount`, `FixBridge` (`AbelianVarietyTheory/Definitions/Divisors/HasDivPlace.lean`); `ClosedPhi`, `ClosedAtL`; `IsHerm`, `IsSkew`, `ResEtaPow`, `HasExp`, `coef` beyond their uses.
