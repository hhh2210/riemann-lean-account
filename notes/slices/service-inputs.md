# The service inputs behind `hServ`: SysTw, the orbit bound without operator, jet integrality

Read 2026-11-20 from the source text only; the build is unfinished. Tags: **read** means the quoted text was read; **proved-by** means the proof was read and its inputs are named; *inferred* means my interpretation. Paths are relative to `src/`. Abbreviations:

- TPS = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- SAT = `Development/AbelianVarietyTheory/Proofs/SatakeParameters/`
- OP = `Formalism/SharpRestriction/Divisibility/OrbitPlaces.lean`
- WJSL = `Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`
- FGS = `…/GrowthBounds/FormalGroupSystem.lean`
- IRZ = `…/GrowthBounds/IsResidueClassZero.lean`
- SOP = `Formalism/SharpRestriction/SmoothDesignExistence/SumOverPrimesHypotheses.lean`
- G7 = `Formalism/ThetaLogCoordinates/UniformThetaSubstitution/`

## Direct answers

1. `hServ` has two fields. The field `twU` holds CmpV and SysTw at sp = 1. The field `pdv` holds ten conditions on the selected theta kernel, among them OrbitBoundWithoutOperator and JetIntegralityBis. **read** One proof produces both fields, in this order **proved-by**:
   - Artin reciprocity gives CM2.
   - CM2 gives six CM statements.
   - Those give `ServH`.
   - `ServH` is repackaged as `hServ`.
2. **Artin reciprocity.** Take K = ℚ(√−d) and Ω an algebraic closure of K. Reciprocity supplies an Artin map Gal(Ω/K) → Cl(𝒪_K), trivial on inertia and sending the Frobenius at v to [v]. With an in-tree Chebotarev statement this shows that inertia fixes j(L), which gives CM2: CM curves have good models over ℚ_l^ur. **proved-by** On this route reciprocity is a hypothesis, the field `P.globalArtinReciprocity` of a bundle. **read** The tree also proves it, as `globalArtinReciprocity_holds := CompanionTheory.FamInh.globalArtin` on the in-tree `GroundTheory` idelic Artin map, not on Mathlib. I did not check whether the bundle field is filled with that proof. **read**
3. **OrbitBoundWithoutOperator** is a local p-adic statement about all power series of a given theta shape; the automorphic kernel does not enter it. **read** Its bound comes from `kernel_a_one_generic`, the ThetaLogCoordinates "no-operator Gauss bound" that the served branch also uses. **proved-by** The kernel's own theta shape is the separate field EvenConditionsInert. **read**
4. **JetIntegralityBis** says the actual kernel's jets are p-integral at every level-free place with p ≠ d. **read** It follows from integrality of the Taylor coefficients of normalised theta translates of a CM lattice, in the formal-group logarithm coordinate. It uses neither CM2 nor reciprocity. **proved-by**
5. **SysTw** asks, at each place, for a local formal-group system with a theta datum that is `admitted` (13 axioms, including adm11, jet integrality at every vertex). It also asks for jet lower bounds at vertices that are not orbit representatives, adding up to at least lowS. **read** It comes from AdmAtEnt2 and CurveEx, which come from CM2 and the in-tree CM3. **proved-by**
6. `sum_over_primes_service` concludes `ServF`: TypePrimeSizeConds ∧ Conclusion1 ∧ ColumnValuationAwayFromTypePrimes, all at sp = 1 (§4). **read**
7. Several inputs are true by construction or are never used (§5). **read**

## 1. Definitions

**SysTw**, at SOP:116, with an identical copy at `…/Definitions/GaloisGeometry/ModelsOK.lean:25`. **read**
```
ErrDefs … → ∀ μ, Used μ → ∀ hT, LatTied hT X (W.Yt μ) → ∀ u w (hg : GIdx host T_u p), p ∉ Dx.Qp μ →
 ∃ _prime std vp unif eO eO_spec dG dG_spec om (Y5 : Pend (Sys.mk (D.gat u w hg) Fl Lv Ch std … om)),
   FormalGroupSystem.admitted D _ Y5 ∧ ∃ Fn, (∀ v ∉ (reps X p).image vOf, ∀ j < m, Y5.LowAt j v (Fn v (j+1))) ∧
   lowS … sp u w ≤ ∑_{j=1}^{m} ∑_{v ∉ image} Fn v j − ∑_{j<m} dG j
```
- `LowAt j v g` (FGS:529): for every U integral in the parameter, every column-choice jet of exp(−PhAt j v)·U has valuation ≥ g. Here PhAt is the sum over e of `sub2 p be` evaluated at the variable pair at v. **read**
- `adm11 := ∀ v, ∀ j < mm, LowAt j v 0` (FGS:627). **read**
- `admitted` (FGS:771) is adm1 (`DworkLemma` for every p) ∧ adm2 ∧ adm2b ∧ adm2c (`BeProp be`) ∧ adm3 ∧ adm3b ∧ ArchimedeanSignatureMatching ∧ adm5 ∧ MinkowskiCounting ∧ adm6 ∧ adm7 ∧ adm8 ∧ adm11. **read**
- `lowS = Σ_j (F_j(w) − ES_j(u,w)) + sp·v_p(DGam)` (WJSL:73). **read**
- `lowAt_max` (FGS:718) uses adm11 for orbit vertices with g0 ≤ 0 and `VolumeRatio₂` for those with g0 ≥ 0. **proved-by**

**OrbitBoundWithoutOperator** (OP:333). **read**
```
∀ w (h : OrbOK D p), IsResidueClassZero D p → hP D p ≠ 0 → p ≤ X'' → ∀ u, ∀ i < m, ∀ t0 ∈ reps X p,
  OrbGe E p h u i (false,t0) (E.ep w) (E.sg w (false,t0)) (E.be w (false,t0)) (max (g0 X K a b p (i+1) t0) 0)
OrbGe … β := ∀ Th, OrbitThetaExpansion (orbLoc E p h u i z Th) ep sg be → KvalGe N_i N_{i+1} p (nu on orbit) Th β
OrbitThetaExpansion Lc ep sg be := ∃ U integral, Lc.Tht ep = U * subst (jetLogG l d) (expS (sg • beSum be))
```
- `KvalGe … B` (`…/Divisibility/ProductZerothFirstParts.lean:99`): every jet `applyAt0 Th (Gxz nu I)` has norm ≤ l^(−B). Such a jet is a derivative at 0 paired with a product of minors of shape nu. **read**
- `g0` (IRZ:247): sum over top letters s on the orbit of Σ over odd e not `Excl` of max(0, (a_s − 2cG)/p^e − capU(s,e)), less dl. **read**
- In words: let p be inert, with Frobenius orbits of even length, p ≥ 5 and p ≤ X″. Take a series on one orbit whose substitution into ep·(height-two logarithm) factors as an integral series times exp(sg·Σ be). Its jets then have valuation ≥ max(g0(t0), 0). *inferred*

**JetIntegralityBis** (OP:339). **read**
```
∀ u μ w, LevelFree Dx u μ w → p ≠ d → ∀ i < m, Even (N_i·N_{i+1}) → ∀ L L', KvalGe N_i N_{i+1} p (E.nu u i) (E.Th u μ w i L L') 0
```
`LevelFree` means p ≠ T_u, p ∉ {g₀, g₁} and p ∉ Qp μ (OP:64). **read**

**ServH** (`…/GaloisGeometry/HasPartAnd.lean:45`) and **Pdv.At** (`…/GaloisGeometry/IsEntC.lean:19`). **read**
```
ServH ker 𝒜 σ := (Closed 𝒜 fun Fm _ => TwU.RowTwU Fm) ∧ AtAll (fun D O c b => Pdv.At O.ex (ker D O c b).ent) 𝒜 σ
Pdv.At ex E := (UnUnit ∧ KmapRat ∧ KFi ∧ Stab0) ∧ ∃ ep be sg, EvenConditionsInert ∧ EvenConditionsAtC ∧
  OrbitBoundWithoutOperator ∧ JetIntegralityBis ∧ ThetaKernelShapeAtD ∧ Shape     -- for ofKer (nuRowOK D) E ep be sg
```
- `RowTwU` (ModelsOK.lean:41): eventually in x there is LC with CmpV ∧ SysTw at sp = 1. **read**
- `SlotServiceCondition := Row Q Lk SelectionServesFamily` (TPS/CountsIrreducibilityConstants.lean:104). The record `SelectionServed` (:48) has the same two fields on `D3 3 𝒜`, with kernel `((sel Fm hc).2 x hx h0 i).T.ker.ent` (TPS/Hyps.lean:76). **read**
- `Row Q Lk H`: some per-bundle property E holds for every linked bundle, and H holds for every selection of E-bundles. **read**

**Conclusion1** (WJSL:97). **read**
```
Ties9 → ErrDefs → ∀ u w, p ≠ T_u → p ∉ {g₀,g₁} → ∀ μ, Used μ → p ∉ Qp μ → ∀ x, InNP X Y K c u w x → ColGe T u μ w x totS
InNP := (∃ hg, c.cmp u w hg x ∈ NP X Y K u w hg) ∨ (VV … p = ∅ ∧ x ∈ LT.Sram D u w)
totS := Σ_j (gainS p j + F_j(w) − ES_j(u,w)) + sp·vDG
```
`ColGe` holds when the m-fold column (lift-chain) map sends x to a·z, with z in the top lattice at w and a = 0 or v_w(a) ≥ e_w·totS. **read**

**Orbit, served, operator.**
- HH D is D.R.A, the factor A of the host Galois group GG = {±1}² × A. hP(p) is the A-part of a Frobenius at p (IRZ:93,97). **read**
- Places are Bool × A, standing for the embeddings τ₁(t) and τ₂(t). The Frobenius step is `posPl p z e = (z.1 xor [p signal ∧ e odd], z.2 + e·hP p)` (`…/LocalRingCardinality/DataForced.lean:19`). `reps` picks one representative per coset of ⟨stepP p⟩ (IRZ:166). **read**
- An orbit is thus a cycle of Frob_p acting by translation on the index set of the CM embeddings. *inferred*
- Served orbits are those with t0 ∈ `VV` (IRZ:292). VV = goodReps when `Cand` holds and Sig ≤ x^(−ε), and VV = ∅ otherwise. `Cand` requires p < X′, p inert and an orbit of length ≥ x^(ε/4). **read**
- The "operator" is the local Hecke operator `yv v F = p^{ArV v}·Σ_{L'' : IsEdge p (n' v) r (L'', L v)} F(update L v L'')` (`…/GrowthBounds/DataG.lean:148,196`). Its iterates on served orbits span NP. **read**
- Served orbits gain max(gU − Pr, max(g0, 0)), where gU runs at rate γ. The others gain max(g0, 0). **read** The G7 exponent `excessGain` is the conclusion of `GaussBoundNoOperatorGeneric` (G7/StatementGK.lean:22). **read**

## 2. The Artin chain

- `hServ := LinkedAt.of_row (hServ_of_linkR hA … (linkR_of_isLinked' _))` (TPS/LinkROfIsLinked.lean:76), with `hA = P.globalArtinReciprocity` (TPS/HypothesesNonemptyOfUnramifiedExponents.lean:54). **read**
- Each link only passes the proof on. `hServ_of_linkR` (TPS/RowHServOfLinkStatement.lean:14) is `row_hServ_of_link_alt` (TPS/RowHServOfLink.lean:17). That is `Row.map` along b ↦ b.R applied to `reciprocity_kernel_of_artin` (TPS/ServHRowLinkRStatement.lean:14), then `row_hServ_of_kerServ_alt` (TPS/RowHServOfKerServ.lean:13). **read** `reciprocity_kernel_of_artin` is `servH_row_linkR_alt` (TPS/ServHRowLinkR.lean:14), which uses `linkR_stdTie_entry` (TPS/LinkRStdTie.lean:20). **read**
- `servH_row_of_artin` (SAT/BundleBothPartsOfStandardKernelOfGlobalArtinReci.lean:15) sets h2 := `cmGoodModel_of_globalArtinReciprocity hA`. It obtains AlgTAll (`ThLoc.algTAll`, which does not use h2), GenusOneModelExistsLattice and CurveDict from h2. It also obtains IntInert, AdmAtEnt2, and CurveEx = `curveEx_of_cm h2 HondaCM3.cm3`. It then calls `servH_row` (SAT/BundleBothPartsOfStandardKernelAndSixHypotheses.lean:15) = `Row.and (rowTwU …) (rowAt_of_stdTie …)`. **proved-by**
- `IsGlobalArtin art` (`…/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:25`): art : 𝔸_E^× → Gal(Ω/E)^ab is an open quotient map. Its kernel is the closure of E^×·(𝔸_∞^×)°. Units map onto inertia, uniformisers map to inverse Frobenii, and local images are dense in decomposition groups. **read**
- `cmGoodModel_of_globalArtinReciprocity` (`…/DecoratedLatticeProofs/CmGoodModelOfGlobalArtinReciprocity.lean:10`) feeds the class-group Artin symbol and `chebotarev_degreeOne_valuationSubrings` to `good_model` (SAT/CmLatticeGoodModelUnramified.lean:64). **proved-by**
- `inertia_fixes` (:10) takes σ in inertia and uses Chebotarev to pick a Frobenius φ ≡ σ modulo ker(art) ∩ Stab. Then art φ = 1, `frobCong` gives φ(j) ≡ j mod v, so φ j = j and σ j = j. **proved-by**
- This is the classical statement that j(L) lies in the Hilbert class field and is unramified everywhere. *inferred*
- `CM2` (`…/TorsionIntegrality/CMGoodModels/Statement.lean:45`): let d be squarefree with d ≡ 3 mod 4, and L have CM by (1+√−d)/2. For every prime l ≥ 5 with l ∤ d and every ι : ℂ ≅ ℂ_l there are integral g₂, g₃ in ℚ_l^ur with unit discriminant, equal to λ⁴ι g₂(L) and λ⁶ι g₃(L). **read**

## 3. What proves the three inputs

**OrbitBoundWithoutOperator.**
- `at_of_true_columns` (SAT/AtOfTrueColumns.lean:30) sets sg := −1. It takes ep, be, `BeFam` and EvenConditionsInert from `admissibleKernelSeries_inertPrime_nonConjugateFrobenius hAlg (hostAt_inert …)`. **proved-by**
- `orbit_bound_rec` (SAT/OrbitBoundStandardSeriesInertPlaces.lean:22) has two cases. **proved-by**
  - If g0 ≤ 0, it uses `standardOrbitSeries_valuationBound_zero`, which gives valuation ≥ 0.
  - Otherwise it uses `kvalGe_orbitGainWithoutOperator`, which gives valuation ≥ gainA, together with `wordFreeNumber_le_orbitBound`, which gives g0 ≤ gainA.
- `kvalGe_gainA` (SAT/KvalGeOrbitGainWithoutOperator.lean:106) starts by unpacking `BeStd`. **proved-by**
  - be is built from an unramified Frobenius lift σ, a height-two law of logarithm F, dual bases, and a primitive (l^d − 1)-th root of unity ζ.
  - `exists_integral_orbit_series` rewrites Th as thetaInZ(exp(−sumE be0)·U₀) with U₀ integral.
  - `kernel_bound` (:86) then applies `Th1.D.kernelOfF`.
- `kernel_of_f` (`…/GaussSumParity/KummerThetaLogarithms/ThetaIntegerIsSSubstitution.lean:250`) calls `G7.Top.kernel_from_k_one_k` = `kernel_bounds_generic` (G7/FrobeniusLiftNorms/EGaussK.lean:255). Its first component is `kernel_a_one_generic` (:213), which comes from `gauss_a_one_generic : GaussBoundNoOperatorGeneric` (:186). **proved-by**
- `gainA` (`…/GaloisGeometry/BeData.lean:55`) is Σ_{s∈TT} Σ′_{e odd, s+e ∉ TT within one period} max(al_s/l^e − cap(s+e), 0), less a log loss. **read** Each top letter contributes al/l + al/l³ + ⋯, capped by its partner's capacity. *inferred*

**JetIntegralityBis.**
- `kernelDatum_entries_integral_away_from_d` (SAT/KernelDatumEntriesIntegralAwayFromD.lean:25) chains four results. **proved-by**
  - `comb_of_tied` shows the kernel is a combination of theta translates.
  - `integralJets_normalisedThetaCombinations_away_d` handles p ≠ d, and needs d ≡ 2 mod 3 when p = 3.
  - `integral_jets_realPlace_local_bases`.
  - `kvalGe_zero_of_integral_jets`.
- The central statement: every combination of normalised translates G(z+t)·exp(−πH(z,t) − πH(t,t)/2) of theta functions of the CM torus `B.tor` has integral jets in the logarithm coordinate. **read**
- Its input `ThLoc.Inputs` (`…/GaloisGeometry/ThetaZJetsThree.lean:34`) comes from `inputs_of_algT`. It provides `cm1` (j integral), a good ordinary model at 2 when d ≡ 7 mod 8, `locJets_all`, `thetaZJetsThree` and `place_extends_to_iso`. **read**

**SysTw.**
- `rowTwU` (SAT/RowTwUHolds.lean:15) calls `rowTwU_of_models split_bound_eleven_one`, which reaches `sysTw_sites` (`…/LocalSystemsLowerBoundsSecondRealPlace.lean:48`). **proved-by**
- `sysTw_sites` takes Y5 and `admitted` from `SiteAdm` and sets Fn := FOrb(true, r v) − errF when p ≤ X″, and 0 otherwise. **proved-by**
  - For p ≤ X″ it proves `LowAt` by `local_model_bound_place_over_second_embedding`, using Theorem A through h01, Shape and adm2c.
  - For p > X″ it uses adm11.
- `AdmAtEnt2` (`…/ThetaSeriesDataHypothesesBelowMaximalLevel.lean:106`): given CM-curve data at p (`CurveIn`) and the theta-series hypotheses, the explicit theta datum `pendG …` is `admitted`. `CurveEx` (:131) supplies `CurveIn` at every inert p ≥ 5. **read**

## 4. `sum_over_primes_service` (SOP:187), input by input

1. `hD : DGamSize` goes to `admissible_size_family` (SOP:57), with `szCt_fam` and `szEatI_fam`. It returns TypePrimeSizeConds. **proved-by**
2. `h01 := split_bound_eleven_one` gives Theorem A, Cor2 and ThmOne at (11, 1). **read**
3. `num_closed 𝒞 stmtNumE` gives NumCmpF: gU ≤ gB, g0 ≤ gA and Pr ≤ Pr. **read**
4. The fixed constants give `CLarge 11 1`. **read**
5. `twU` provides CmpV and SysTw. `unit_bound_of_sum_over_primes` (`…/GrowthBounds/JointsTw.lean:243`) combines SysTw with `FormalGroupSystem.Pf.stmt_proved` and `hLarge_proved`, and returns the served-orbit unit bound `hU`. **proved-by**
6. `pdv` provides E with UnUnit, KmapRat, KFi and Stab0, together with ep, be, sg and the six conditions. **read**
7. The proof assembles `OrbitPlaces.admitted` at (sp, C6, Cd) = (1, 11, 1) from four results: `typeG_ne_d`, `orbit_admissible_of_split_bound`, `theta_isometry_facts_hold` and `kform_of_ker`. **proved-by**
8. `lift_bounds_of_essential` (OP:1340) applies `orbit_entry_bounds_hold`. `four_orbit_conditions_of_proof` keeps four results: OrbitsWithoutOperator, MediumInertPrimeLengthBound, LossAtDiscriminant and IsotypicPartsInternalDirectSum. **proved-by**
9. `serv_of (Proof.stmt_proved)` (WJSL:376) receives `⟨hU, local_theorem_of_statement …, it, n, c, d⟩` and returns `Serv`. `serv_re` then moves it from `reY Y LC` back to Y. **proved-by**

How each input is used:
- **OrbitBoundWithoutOperator** covers the kind-A representatives (false, t0), through `entI_of` (OP:1090) → `liftI_of` → `noOp_of` → OrbitsWithoutOperator. **proved-by**
- **Kind-B/C representatives** carry the F-terms, through OrbitValuationBound and GaussJetBounds' Cor2. **read**
- **JetIntegralityBis** goes through `int_of` (OP:934) → LiftIntegrality → `restComp_proved`. At the remaining primes this gives ColGe ≥ −(m − sp)·v_p(DGam). **proved-by**
- **SysTw** gives the served branch: UAt → `kernel_valuation_served`. **proved-by**

## 5. Vacuous, degenerate, by construction, unused

1. **StdTie by construction.** `RecordCompatibleExtended` (TPS/CoreAltAltBis.lean:56) has the field `std : StdAt … R.T.ker` (:58). `ReciprocityLinkage` (:60) is defined from it, and `linkR_stdTie_entry` only projects that field. **read** So whether the kernel is the standard CM theta kernel rests on the existence of linked bundles, which this chain does not prove. *inferred*
2. **DGamSize by class membership.** It is discharged as `hc.2.2.2` (TPS/ClosedFamilyAdmissibleTwistLink.lean:26): the class `Des` contains DGamSize as a conjunct (`…/DesignExistsDes.lean:10`). **read**
3. **Discarded argument.** `num_closed (_hN)` ignores `stmtNumE` and uses `numCmpF_fixed` instead (`…/PlaneCountTheoremWithConstants.lean:1828,1833`). **read** This corrects the divisibility trace, which credited stmtNumE. **read**
4. **Unused conjunct.** SmallInertPrimeSmallOrderLengthBound is supplied but never consumed: the destructuring is `⟨hU, _, _, hNo, hC, hD⟩`, and only `hA.2.2.1` is used besides (`…/StatementsOfRemainingBound.lean:196,209`). **read**
5. **OrbitBoundWithoutOperator is kernel-free.** It reads E only through ep, be, sg and the Young diagrams nuD, which `Ent.nu_row` pins. **read**
6. **Zero instance.** `entStd D := ⟨nuD D, nuRowOK D, nuD_rows D, 0, 0, 0, 0⟩` has Th = ep = be = sg = 0 and witnesses Shape in `rowTwU` (RowTwUHolds.lean:13). **read** This is harmless for Shape. *inferred* It is also passed to `local_model_bound_place_over_second_embedding`, which I did not read. **read**
7. **Fixed or trivial.** sg ≡ −1 is chosen, not derived. `Even (N_i·N_{i+1})` always holds. `rowTwU` witnesses `Closed` with zero thresholds. **read**
8. **Duplicates.** SysTw and reW appear twice, at ModelsOK.lean:25 and SOP:116. SelectionServed appears twice, at TPS/CountsIrreducibilityConstants.lean:48 and TPS/GServT.lean:13. `serv_t_iff_formalism_serv_t` (TPS/ShapeOf.lean:30) bridges the copies. **read**

## Not read

- **Kernel-shape proofs:** `admissibleKernelSeries_inertPrime_nonConjugateFrobenius` (EvenConditionsInert, BeFam), `frobeniusConjugation_conditions_adaptedKernelDatum`, `kernelDatum_thetaSeries_shape_at_d_adaptedBases`, `hostAt_inert`, `exists_integral_orbit_series`, `wordFreeNumber_le_orbitBound`, and the core of `standardOrbitSeries_valuationBound_zero`.
- **CM lemmas:** `admissible_entries_small_chain`, `kernels_integral_inert`, `datum_exists_lattice`, `curveDict_of_cm`, `HondaCM3.cm3`, `ThLoc.algTAll`, `comb_of_tied`, `locJets_all`, `cm1`.
- **SysTw lemmas:** `modelsAt_bpt`, `local_model_bound_place_over_second_embedding`, `low_term_le_second_real_place_bounds`.
- **Reciprocity and Chebotarev:** `exists_artinSymbol`, `chebOmSt_holds`, `frobCong`, GroundTheory's `artinMap`, and which term fills `P.globalArtinReciprocity`.
- **ThetaLogCoordinates and the rest:** `Top.entry_a_one`, `theorem_s_uniform`, `remaining_primes_of_admitted`, `numeric_comparison_of_constants`, `hLarge_proved`.
- **Open checks:** whether all 13 conjuncts of `admitted` are consumed, and whether linked bundles exist.
