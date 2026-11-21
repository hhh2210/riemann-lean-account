# The definite-side record `HypsAlt`: its fields, their suppliers, and the route into `SizeData₂`

Read 2026-11-20 from source text only; nothing was built. Paths are relative to `src/`. Abbreviations: TPS = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`, GI = `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/`, FM = `Development/AbelianVarietyTheory/Proofs/FlagMeasures/`, GT = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/`, CB = `Development/AutomorphicArithmetic/CharacterBoxes/`, GSB = `Formalism/SharpRestriction/GlobalSchurBounds/`, AGP = `Formalism/LocalToGlobal/GroupLattices/AdmissibleAtGeneratorPlaces.lean`, WDS = `Formalism/SharpRestriction/Divisibility/WeightDegreeSizes.lean`, PFZ = `GSB/ProductFirstZerothParts.lean`, CIC = `TPS/CountsIrreducibilityConstants.lean`, GTI = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`.

Tags: **[R]** read and transcribed; **[P]** proved-by (I read the proof and name what supplies it); **[I]** my interpretation. In the §1 table, the "says" and "supplier" cells are [R] unless marked otherwise, and the "class" cell is [I].

## 0. Direct answers

1. The record on the used path is `GlobalTheory.Fc.HypsAlt N DR` (TPS/Hyps.lean:22). Here N = `S0.NL` = `fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm` (GT/GeometricWeakTiesOfStrong.lean:36) and DR = `DefiniteSideCondition` (TPS/DefiniteSideCondition.lean:25). [R] It has exactly **46 fields**: 5 are data (`𝒜`, `σ`, `cT`, `c30`, `cIc`) and 41 are propositions. [R] `AllRowsAlt` (TPS/AllRows.lean:12) has 26 fields. [R]
2. The non-Alt `Hyps` (GT/APerTw.lean:23) has the same 46 field names; `σ`, `hRB`, `selJ`, `rRows` and `hServ` have different types there. [R] It is built by `nonempty_hyps_of_allRows` (GI/NonemptyHypsOfAllRows.lean:14) and consumed through `shape_of` (GI/ShapeOf.lean:6) by `plugWin`/`plugAll` (CB/EveryCharacter.lean:8,16) → `shapeWin`. Those are reached from `everyE₂` (`…/ThetaCorrespondence/FockModels/EveryCharacterE.lean:67`), and I found no use of them on the `riemannHypothesis` path. [R] The route that `UpperTheory.FinalTheorems.riemannHypothesis` takes (§5) uses `HypsAlt` and `shape_closed_link_n_of_green` (TPS/TopShape.lean:33), the `_alt` twin of `shapeWin`. [R]
3. Because of how the record is filled, **28 of the 41 propositional fields hold by construction**. `classSel` (CB/ClassSel.lean:14) defines 𝒜 to be the class of families whose points are constructed points satisfying every row property, so each such field follows from a theorem of the form "every constructed point has the property". [P] Five more fields come from that class definition or from its existence statement (`𝒜`, `σ`, `hEx`, `hduty`, `hMt`). [P] Five are chosen constants together with their positivity (`cT`, `c30`, `hc30`, `cIc`, `hcI`). [R] Eight are global theorems passed in directly (`hLit`, `hWu`, `hRF`, `sTy`, `sNG`, `sM`, `hU`, `hG`). [R]
4. The prior assumption about routing holds: `topDesWin` assembles the family-level links into `GlobalTheoremInputs`, and `link_gl` turns those into `ChainTied`. It needs three corrections, given in §3. [P]
5. Deep inputs (§4):
   - Siegel–Weil in the convergent range, stated in two forms. [R]
   - An identity "definite period = unit × nonzero scalar × inner product of a theta lift" (`MIid`) inside `rRows`. It is supplied from Siegel–Weil, doubling zeta integrals and unramified Howe duality. [R]
   - Archimedean Bessel multiplicity one in a large-gap range, behind `sTy`. [R]
   - Mass and volume formulas behind `hU`, `hG`, `hn4` and `hInstR`. [R]
   - The theory of CM elliptic curves, reached through global Artin reciprocity, behind `hServ`. [R]
   - A Selmer-length bound (`LinkN`) behind `nRest`. [R]
   - Zero-density estimates near Re s = 1 behind `hLit`. [R]
   - No global period formula of Ichino–Ikeda or Waldspurger type appears among the record's types or the supplier statements I read. The scalar a(u) in `MIid` is only asserted to be nonzero. [R]
6. Degeneracy. No field type is vacuous on its face. [R] There are three caveats:
   - The period-integrality fields `aPer0` and `aPerTw` are derived from `RowInt`, which is a structure field of every constructed point (`RowsT.rowInt`, `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonzeroPlacesOverPrimes.lean:61`). [P] The integrality is therefore assumed of the points. Its cost is paid wherever such points are shown to exist: in `hEx`, and in the builder inputs `hMem` and `ExBL` from `large_unramified_exponent_bundles_exist_alt` (TPS/MemberBundlesLargeUnramifiedExponents.lean:69). I did not read that proof. [R]
   - The constants `cT`, `c30` and `cIc` are chosen so that their inequalities hold. [R]
   - On the used path `LinkG` is built from `hduty` alone (TPS/TopShape.lean:54). [R]

## 1. The 46 fields

| # | field : type (definition) | says | supplier on the used path | class |
|---|---|---|---|---|
| **A** | *class, selection, constants* | | | |
| 1 | `𝒜 : FamClass` | the class of families | `classSel`: `cls (sAnd Q' R) Lk E` [P] | by construction |
| 2 | `σ : RawSel BundleCondition 𝒜` | a bundle chosen at each point | `pick` (Classical.choose), ClassSel.lean:20 [P] | by construction |
| 3 | `cT` | threshold for `CTu` | `cTmin y = max 11 (16 + 3·max 5 (y+1))` (GSB/TheoremThreeFamilyOfFormalDegreeInput.lean:93) | constant |
| 4 | `hEx : MinkDiv → ExS 𝒜 cT` (CB/ExS.lean:10) | Assume Minkowski's divisibility. Then for every la > 1 and every host requirement G, at every small ε there are families in 𝒜 ∩ G.cls la with all the `DesignChoices` properties (`Formalism/SharpRestriction/DesignExistsOfChoices.lean:22`: Large, ChosenTT/Bad/QD/Code, cT ≤ CTu, CYL ≤ 9, …) | `classSel` → `memberTop_final_contextParameters` (uses `SiegelMassRatioCM`, `VolumeRatio₂` and `hMem`) → `working_classes_frozen` [P] | Development; this is the existence burden |
| 5 | `hduty : Duty` (GT/CountsIrreducibilityConstants.lean:48) | `PageFix ∧ PageWin ∧ SmallFirstModulusBelowScale ∧ TameDistinctF ∧ ChosenWall ∧ TupUsedF ∧ TwAllF` | `familyClass_sevenDuties_and_stableLattices` (GT/FamilyClassSevenDutiesAndStableLattices.lean:55) [P] | by construction (`cls7`) |
| 6 | `hMt` (TPS/Hyps.lean:62) | each `Mtilde μ` is an 𝒪_LL-module | same, `MtStableF` [P] | by construction |
| 7–10 | `c30`, `hc30`, `cIc`, `hcI` | counting constants with `0 ≤ C`, `2(CYL+1) ≤ A` and `0 < cIc` | witnesses produced by `row_counts_of_labels_alt` (TPS/RowCountsOfLabels.lean:13) | constants |
| **B** | *period integrality* | | | |
| 11 | `aPt0 : ∀ u, Conclusion6` (PFZ:334) | `til` is injective and every `stabMap c` is bijective. `Pt = lowerMap ∘ evz` sends level-m forms into `ptC`. There is an integral rational structure with ‖PtL x‖² ≤ ptB·‖x‖² at every infinite place, and ⟨Pt φ, Pt φ⟩ ≤ ptB·⟨φ, φ⟩, where ptB = ∏_τ T^(−deg τ)·beOn(τ)². | `six_rows_at_member_alt` (TPS/SixRowsAtMember.lean:11) → `formsMap_at_every_trueColumnMember` (GI/FormsMapAtEveryTrueColumnMember.lean:15) [P] | Development, from construction data |
| 12 | `aPtTw : TwistedPointIntegral` (AGP:11) | every twisted period map has an integral rational structure | six → `row_aPtTw_of_overCols` (GI/TwistedChainEvaluationRationalIntegralBundlePoin.lean:13) [P] | construction |
| 13 | `aPer0 : PeriodClassSumWeyl` (WDS:723) | Pair a point of the period lattice with F ∈ Mtilde ∩ V0. The period is 0, or at every place it has valuation ≥ −e_w·v_p(DGam). | six → `periodAdmissible_of_integralPeriodRows` (GI/PeriodAdmissibleOfIntegralPeriodRows.lean:10): `RowInt` plus a class-sum decomposition [P] | construction (`RowInt`) |
| 14 | `aPerTw : TwistedPeriodAdmissible` (AGP:14) | the same for twisted μ ≠ μ0, at places outside `Qp μ` | six → `admissible_period_twist_of_integral_rows` (uses `cv.rowInt`) [P] | construction |
| 15 | `aP10 : Conclusion5Sharp ∧ TwistedColumnBoundAtT` (PFZ:315, AGP:20) | Let w lie over T(u). If v_w(c) ≥ e_w·m·E_T, then c·colT maps N_λ into `S m w`. The twisted column values of N_λ have valuation ≥ −m·E_T. | six → `closing_true_cols` (uses `ColPin.jets`) [P] | construction |
| 16 | `aAtG : UsedTuplesBoundByConstant ∧ familySizeBoundAtTypePrime` (AGP:25; `SgAtG`, WDS:1002) | Take places w with `Over D i w` (over g_i [I]) that do not lie over T(u). There the periods of `MramL` are 0 or have v ≥ −Σ_j vNN − C1·errC. Over g_i, Σ_j(F − E) ≤ −Σ_j vNN − C1·errC. | `row_aAtG_at_built_alt` (TPS/RowAAtGAtBuilt.lean:10), from the slot component `RX` that `Built` carries [P] | construction |
| 17 | `aC2 : FamilySecondComplementInputs` (WDS:683) | eight size bounds, each ≤ C·B0 (`SecondComplementInputs`, WDS:673) | `divisionSecondComplement_constructedPoints` (GI/…ConstructedPoints.lean:9), from TuSize ∧ DGamSize [P] | elementary bookkeeping |
| 18 | `hServ : SelectionServed` (CIC:48) | `twU`: the column-valuation transfer `CmpV` and `SysTw`. `pdv`: unit and rational kernel entries, `OrbitBoundWithoutOperator`, `JetIntegralityBis`, and the theta-kernel shape. | `row_hServ_of_link_alt` (TPS/RowHServOfLink.lean:17) → `servH_row_of_artin` [P] | Development ← Published (`GlobalArtinReciprocity`) |
| 19 | `tie : RealPlaceSecondLayerConditions` (GSB/LinkTied.lean:51) | eventually `RealTied`, and symmetric tied column forms whose character has finite order at step 0 | six → `row_tie_of_overCols` (GI/RealSideColumnsCompatible…lean:14) [P] | construction |
| **C** | *indefinite-side ties (local representation theory)* | | | |
| 20 | `hRB` (TPS/IndefRRealTB.lean:39) | `IoExt`, and `OneMapRowR` row by row | `row_hRB_univ_alt` (TPS/RowHRBUniv.lean:19): DiscreteSeriesCover, HarishChandraModules, CuspRapidDecay, CasselmanWallach | Development ← Published |
| 21 | `hTw : TieTwRec` (`Formalism/LocalToGlobal/Divisibility/LinkDefN.lean:36`) | each twisted place lies in `supp` and has μ ≠ μ0 | `row_hTw_of_tie_alt` from `o.tie` | bookkeeping |
| 22 | `hPA : PrimRows3 ∧ TypesSep3` | `OkH` and inert rational adjoints for rows and lifts, plus `PHecke`, `PGUnit`, `PGEquiv`, row and lift tests, positivity, `PrincipalLevelBijective` and `PThmB`. Distinct types are separated. | `o.hPA` ← `linkedAt_hPA_prmR` (TPS/HermWCell…Statement.lean:15), which takes no literature argument | construction |
| 23 | `hLamP : RowsHoldLam3` | the definite isotypic pieces match the indefinite weights λ and the row counts | `real_group_inputs_combined_alt_alt` (TPS/RealGroupInputsCombined.lean:39), using the Weil representation, discrete series, Harish-Chandra, Dixmier–Malliavin, Flath, Zelevinsky and Green | Development ← Published |
| 24 | `hDivG : DivRows3G` (GT/CountsIrreducibilityConstants.lean:91) | The lattices `RR` are tied across sides and the rational lifts span. `thetaP` matches the indefinite θ, and `Ij`, `jw`, `etaJ` match. `Bk u` equals the indefinite column pairing. | `bk_law_entries_alt` (TPS/AtHDivGOfMiStatement.lean:20), using the `MIstar2` rows | Development ← Published |
| 25 | `hDcPtG : DcPtG` (same file:72) | the indefinite `Pt` equals the definite `perCol` | `linkedAt_hDcPtG_prmR` (TPS/RowEDcPtLinkedStatement.lean:15) | construction |
| 26 | `selJ` (TPS/ColJoinSOfSTiesR.lean:67) | chain, row, norm and pair ties between the spectral side and the realisation | `entries_combined_real_alt` (TPS/JoinLinkedRealizationStatement.lean:15) | Development ← Published |
| 27–28 | `jOn`, `zL` | ι(V0 μ0) = ⊤, and the level projections `lPrj` are surjective | `row_jOn_of_row_hPA_alt` and `zL_of_hPA` (TPS/LPrjSurjAt.lean:18), from `hPA` | construction |
| 29 | `rRows : SelectionDefiniteRows DefiniteSideCondition` (CIC:91) | Eventually `IndefiniteRealisationConstantBounds` holds (CIC:35: w1, covolume, onto, λ lower bound, isometry, `MIstar2`, FUN, pass, κ). So does `RowsU` (`Formalism/LocalToGlobal/PtKOfReal.lean:141`), which bounds the operator norm of the period map at each infinite place by heights. | `row_rRows_stage0_alt` (TPS/TupAllUsedAtPart.lean:46) | Development ← Published (§4c) |
| **D** | *mass, volume, dimension* | | | |
| 30 | `hU : ∀ D, MassRatioUnderVolume D` | `VolTie → VolumeRatio₂` (§4b) | `VolRatioFromSiegelWeil.volumeRatio P.siegelWeilUnitaryConvergent2` (FM/UnitaryHyperplaneVolumeRatioSiegelWeil.lean:10) | Development ← Siegel–Weil |
| 31 | `hG : ∀ D, GenusMassAt D 2` | the mass of every positive-definite rank-2 lattice `L0` equals the mass of 𝒪_E² (§4b) | `genusMassAt_two` (GI/GenusMassAtTwo.lean:7) ← `genusMassStd_of_landherrHasse` | Development (Landherr's Hasse principle [I]) |
| 32 | `hInstR : VolSigIndep ∧ ClassItemsAt` | Fundamental-domain volumes depend on the rank, not the signature. At Y0's rank, `ClassItemsAt` bundles the genus-mass formula, finiteness of classes and the class-mass identity. | `row_hInstR_of_hU hU` (GI/RowHInstROfHU.lean:8) | Development ← hU |
| 33 | `hn4 : ClassNumberFormula₂` (GSB/StandardLattice.lean:453) | #cls₀ = massI(D,k)·idxPi(g₀,g₁)·(T^k−1)^f | `classNumber_all` (`…/FoundationProofs/ClassNumberAll.lean:11`), for every D | Development |
| 34 | `hTu` | if cT(ε, CYL) ≤ CTu then `TuSize` holds: log T(u) ≤ CTu·m·L | `row_hTu_cTmin_alt hU hG` (TPS/RowHTuCTmin.lean:11) [P] | Development ← hU, hG |
| 35 | `h30 : CountAllPointsClass` (`…/CuspSpanNormBounds/BridgeCountE.lean:72`) | When the weight gap is ≥ C·n¹⁹f⁵·log(b·rd), \|Dcount − D*\| ≤ exp(−c·n·f·log n)·D* (`CountIdempotentsClass`, :45). | `row_counts_of_labels_alt hSW` | Development ← Siegel–Weil |
| 36 | `irrC` | There is an `AllRows` A whose labels are counted injectively and whose rows are joined. Every cylinder set S of local types at g₀ and g₁ has \|dim − D*_S\| ≤ exp(−c·r·f·log r)·D*_S (`CountAllRows`, `Formalism/LocalToGlobal/GlobalTheory/IrreducibleOfCountSizes.lean:183`). | same, using `o.lab` (Green, Zelevinsky) | Development ← Siegel–Weil |
| **E** | *archimedean and spectral bounds on the kernels* | | | |
| 37 | `hWu : WuDecayOfGap` | under a gap hypothesis, every `HidaSetting` satisfies `WuDecay` and has integrable `ph` | `CompanionTheory.Lime.BM.wuDecayOfGap_holds'` (FM/WuDecayOfGap.lean:7) | in-tree CompanionTheory |
| 38 | `hRF : RowsFinDim` | Given irreducible unitary σ_v with formal degrees d_v, let T be the operator integral of the archimedean coefficient `phInf`. Then `evAt` at `tens w` is injective, with range `HH … T`. | `CompanionTheory.D.gk.RF.automorphic_forms_finite_dimensional` (FM/RowsFinDimLink.lean:7) | CompanionTheory (Harish-Chandra [I]) |
| 39 | `hTF : TFrame` (`…/CuspSpanNormBounds/PExtra.lean:247`) | 1 ≤ Tr(D,w)·kaS^(2rS) under `Hyp0` | `at_choice_alt` (TPS/AtChoice.lean:16) via `bothRowsFromSiegelWeil_alt` [P] | Development ← Siegel–Weil |
| 40 | `sTy : TypeP` (`…/FlagStabilizerTensors/RowsPos.lean:18`) | a bound `TypeAt` on the kernel data, uniform in D | `rowsPos_typeP` (FM/RowsPosTypeP.lean:9) ← `UniqGap ∧ BesselOfW` (§4e) [P] | Development ← Bessel multiplicity one |
| 41–42 | `sNG`, `sM : RowNGP`, `RowMainEqP` (:37, :43) | the uniform estimates `RowNG` and `RowMain` for `tO u u'` | `rowNGP_of_siegelWeil` and `rowMainEqP_of_siegelWeil` (FM/…:10), with `uniqGap_holds` and "Theorem B" | Development ← Siegel–Weil |
| 43 | `sLp : LoopRowS` (ThmSOwn.lean:1015) | `RowBig ∧ RowNotScalar` for each `tO u u'` | `at_choice_alt`: `loopRows_of_rowsFinDim_alt rowsFinDim_link (volumeRatio hSW)` [P] | Development |
| 44 | `sO : TheoremSSelected` (ThmSOwn.lean:669) | near-orthogonality of the kernels (§4d) | `at_choice_alt`: `CarrierGap.offDiag (swxs_of_siegelWeil hSW) (rowNGP_of_siegelWeil hSW) …` [P] | Development ← Siegel–Weil |
| **F** | *Galois cohomology and analytic number theory* | | | |
| 45 | `nRest : Closed (D3 3 𝒜) LinkN` (GTI:45) | η at the twisted places is bounded by the Sha lengths (§4f) | `final_alt_alt` (TPS/CFinal.lean:19), using local Tate duality, local Euler characteristic, local finiteness and `nLink` | Development ← Published |
| 46 | `hLit : LitThin` (GSB/MainSup.lean:88) | `adm6`, `adm7`, `adm11` (§4g) | `litThin` (GI/LitThin.lean:8) = ⟨`ZerosNearOne.main`, `ZeroBounds.explicit_formula_and_window_count`⟩ | Development (analytic number theory) |

The literature bundle `P : UnitaryGroupThirdPlaceHypotheses` (TPS/BernsteinUnitaryProductIrreducible.lean:22) supplies every `Published` item above. [R] `published_results_eigen` (TPS/EveryCharacterOfLiteratureOfVWin.lean:666) fills it from in-tree proofs: for instance `globalArtinReciprocity_holds` = `CompanionTheory.FamInh.globalArtin`, and `siegelWeilU_unitary_convergent_of_literature` = `GlobalTheory.CompanionTheory.SW.siegelWeilUnitaryConvergent`. [R]

## 2. How the record is assembled

- `nonempty_hyps_of_allRows_alt` (TPS/NonemptyHypsOfAllRows.lean:19) chains 27 `RowL` rows with `RowL.and` (:23–48) and passes them to `classSel` (:51). [P] It fills the fields from the outputs of `classSel` (:55–101). [P] The eight direct inputs come from its caller (TPS/HypothesesNonemptyOfUnramifiedExponents.lean:57–60): `litThin`, `wuDecayOfGap`, `rowsFinDim_link`, `rowsPos_typeP`, `rowNGP_of_siegelWeil`, `rowMainEqP_of_siegelWeil`, `volumeRatio`, `genusMassAt_two`. [R]
- `classSel` (CB/ClassSel.lean:14–28) works as follows. [P]
  - `RowL.elim` and `Row.elim` (GT/ValidForConstructedPointClassesEventuallyWorking.lean:364) give a property E that holds at every constructed point. [P]
  - 𝒜 := `cls (sAnd Q' R) Lk E` (:257), the class of families whose points are built points satisfying E. `σ := pick` (:278). [P]
  - Each row field H holds for (𝒜, σ) by `pick_isSel` (:280). [P]
  - Existence comes from `memberTop_final_contextParameters`, which takes `SiegelMassRatioCM`, `VolumeRatio₂` and the retwisting conditions `hMem`. [P]
- `allRows_of_open0_alt` (TPS/LinkROfIsLinked.lean:50–86) fills the rows as follows. [P]
  - Six rows come from `six` (:52), i.e. `six_rows_at_member_alt`, which takes no literature argument. Its proofs start from `overCols_goodE` (GI/GoodTwistCoresOverTrueColumns.lean:15): every good point has a `ColView`, whose `jets` and `rowInt` are copied from the `Built` structure (GI/ColViewOfBuilt.lean:13–18). [P]
  - `hPA`, `hLamP`, `hDivG`, `hDcPtG` and `selJ` come directly from `o : OpenParameterStatements` (TPS/GeometricWeakTies.lean:39). `jOn`, `zL`, `hTw`, `c30` and `rRows` are derived from parts of `o`. [P]
  - `open_orbit_of_unramified_exponents_alt` (TPS/OpenOrbitOfUnramifiedExponents.lean:39) proves `o` from P. [P]
  - `hServ` comes from Artin reciprocity. `sLp`, `sO` and `hTF` come from Siegel–Weil. [P]
  - `hn4`, `hInstR` and `aC2` are proved for every class by `Row.of_sel` and `Row0.of_all`, without using the construction. [P]
- `servH_row_of_artin` (`Development/AbelianVarietyTheory/Proofs/SatakeParameters/BundleBothPartsOfStandardKernelOfGlobalArtinReci.lean:15`) runs in four steps. [P]
  - Global Artin reciprocity gives `CM2`, good models of CM curves (`cmGoodModel_of_globalArtinReciprocity`). [P]
  - From `CM2` come torsion-Taylor lattices, integrality at inert primes, admissibility of inert theta functions, and a formal isomorphism from good reduction. [P]
  - Those feed `bundle_bothParts_of_standardKernel_and_six_hypotheses`. [P]
  - This is where the jet divisibility of the divisibility slice (`SysTw`, `JetIntegralityBis`, `OrbitBoundWithoutOperator`) enters the record. [I]

## 3. `shapeWin` / `topDesWin` / `TopG`, and the eleven conjuncts

**Producers.** Both shapes call `topDesWin` with the same argument pattern (CB/ShapeWin.lean:46–49; TPS/TopShape.lean:52–55). [R]

| `topDesWin` slot | `shapeWin` (off path) | used path |
|---|---|---|
| `DesignExists` | `link_ex` | `designExists_of_tuSize_aux4n_litThin` (cT, hEx, hduty, hTu, hn4, hLit; `MinkDiv` discharged by `minkowski_bound_rat`) |
| `LinkEta` | `link_eta` | `closed_linkEta_of_duty` (hduty) |
| `LinkIRR` | `link_irr` | `closed_linkIRR_of_join_count` (Green, cIc, hcI, irrC) |
| `SmallLevelRankEq` | `smallLevelRankEq_closed_of_levelProjection_surjective` | `link_alt_alt_alt` (hPA, hLamP, hDivG, zL) |
| `LinkDIVt` | `linkDIVt_closedK` | `closed_linkDIVt_of_closed_bridge_kernel`; consumes 20 fields: hRB, hTw, hPA, hDivG, hDcPtG, rRows, tie, hMt, the six `a…` period fields, aC2, hServ, hWu, hRF, selJ, jOn |
| `LinkG` | `link_g` | `closed_linkG_of_duty` (hduty) |
| `LinkS` | `link_alt` | `link_alt_alt_bis` (hWu, hRF, hTF, c30, hc30, sTy, sNG, sM, sLp, sO, h30, hInstR) |
| `LinkN` | `nRest` | `nRest` |
| `NuFullF ∧ MuRank`, `LinkGLOBAL` | `link_gl` | `link_gl 𝒜 hduty tie hU hG` (GI/LinkGl.lean:14), shared |

**Inside `topDesWin`** (CB/DesWin.lean:23–31). [P]
- `LinkDIV` = `aD hT hDG aE (divinN_of_hypV … (hV …) aN aZ)`: `LinkDIVt` is applied to `LinkEta` and to `DIVinN`. `DIVinN` is built from `HypV` (the VWin premise of `TopG`), `LinkN` and `SmallLevelRankEq`. [P]
- `LinkMu` = `J.linkMu_of_linkDIV`, from `LinkDIV`, `NuFullF ∧ MuRank`, `TuSize` and `DGamSize`. [P]
- `GlobalTheoremInputs` = ⟨LinkG, LinkS, LinkIRR, LinkDIV, LinkMu⟩ (GTI:158) is handed to `LinkGLOBAL` (GTI:162). [R]

`LinkGLOBAL` runs through `FamGLmin.link8` (GSB/LogXLowerFamilyOfTheorems.lean:71) → `linkGLOBAL7_min` (GSB/LinkMin.lean:723) → `linkGLOBAL7_items` (:693) → `linkCore` (GSB/LossesSmallShares.lean:38). [P]

**The eleven conjuncts** (`SizeData₂`, `Formalism/SizeWindowBrackets/SChain.lean:17`), as assembled in `linkCore`: [P]

| conjunct | line | built from |
|---|---|---|
| `HidaSetting` | :158 | positivity only: WinF, NodesF, LatF, the SlopesNF constant, and FrameF's η and e |
| `DIV` | :169 | `LinkDIV_at` clause 7 (`muDual + h − Fo ≤ MAIN + …`) |
| `EComp5` | :184 | `LinkDIV_at` clause 8 |
| `HComp` | :188 | `LinkDIV_at` clause 9 |
| `Count5` | :194 | `CountF` ← `family_part_five_of_explicit_constants`, from `siegel_mass_ratio_family`, `volume_eq_mass_rank_two` (`tie`, `hU`, `hG`) and `explicit_bound_family` |
| `Slopes` | :196 | `SlopesMF` ← `slopesMF_of_count_fam`, from the all-family slope inequalities, `CountF`, `ChosenQD` and `tie` |
| `QuotientSlopeBoundsWith` | :198 | `SlopesNF` ← `placesF_min'` (LinkG, LinkMu) |
| `LossBounds` | :201 | `LossFS` ← `stLoss7` (LinkG), with `ChosenWall` from `hduty` |
| `SlopeIneq` | :207 | `FrameF` ← `frameRealF_of''` (LinkDIV, LinkIRR, LinkS) |
| `HHBound` | :208 | `LinkDIV_at` clause 2 (`sFrame + μmax ≤ x^CH·b`) and LatF |
| `FParams` | :210 | `LinkIRR` (both clauses) and FrameF's parameters |

**Corrections to the prior notes.** [P]
- (a) The path to `riemannHypothesis` uses the `_alt` producers in the right-hand column of the producer table, not `shapeWin`'s. The lattices note's chain "plugAll → shapeWin" is off-path at those two hops. Its downstream hops, from `link_gl` to `linkCore`, are shared and remain valid.
- (b) `LinkN` and `SmallLevelRankEq` never reach `LinkGLOBAL` directly. They are spent inside `topDesWin` to make `DIVinN`. `LinkMu` is derived there rather than supplied.
- (c) `Count5` and `Slopes` come from `link_gl`'s own inputs (`tie`, `hU`, `hG` and all-family theorems), not from any of the five links. `HidaSetting` is positivity bookkeeping.

## 4. Deep inputs, transcribed

**(a) Siegel–Weil, density form** (`Formalism/UnipotentAdelicQuotients/SiegelWeilUnitaryConvergent.lean:19,46`), condensed: [R]
```lean
def SiegelDensities : Prop := ∀ n, 2 * n < M → ∀ T (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → … Φ factorisable, Φinf smooth, rapidly decaying … →
  … ∃ ginf gv, … ∧ meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) = ginf (hermOf (Ainf F) σ T hT) * ∏' v, gv v (hermOf (Fv F v) σ T hT)
def SiegelWeilUnitaryConvergent : Prop := ∀ F E σ, IsCMExt F E σ → ∀ M J, IsHermND σ J → FinVol F E σ M J ∧ SiegelDensities F E σ M J
```
In words, for 2n < M the average over the unitary group of the T-th theta coefficient is a product of local densities. This is Siegel's main theorem in Weil's convergent range. [I] It is proved by `GlobalTheory.CompanionTheory.SW.siegelWeilUnitaryConvergent` (`CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/Imports.lean:10`), from `finVol_unitaryGroup` and `siegel_densities_of_hermitian_form`. [R] It feeds `hU`, `sNG`, `sM`, `sLp`, `sO`, `hTF`, `h30` and `irrC`. [R]

The second form is `GlobalTheory.Published.SiegelWeilUnitaryConvergent` (`Development/AbelianVarietyTheory/PublishedTheorems/SiegelWeil₂/SiegelWeilUnitaryConvergent.lean:18`). [R] Under `A.rank < B.rank ≤ 2·A.rank` and `A.rank + wittIdx B < B.rank`, it states that the theta integral is integrable ∧ `EisValueAt A (flat … (swSec A B ω μ 𝓨 f)) (sZero A B) (thetaMean ω ν f)`. [R] So the Siegel Eisenstein series on the doubled group, at the point s₀, equals the theta integral. [I]

**(b) Mass and volume.** [R]
```lean
def MassRatioUnderVolume (D) := VolTie D → VolumeRatio₂ D          -- GSB/MassRatioUnfoldedOfTheoremTwo.lean:12
VolumeRatio₂ D : ∀ W P Q, sig = (P,Q), 3 ≤ n = W.rank → ∃ x, h(x,x) = ±1 ∧ ∃ W' = x^⊥, … ∧
  vol W' / vol W = ((2π)^n/(n-1)!)^f * ((2v)^f)^(1/2 - n) / lValEta E n     -- GSB/ThickPlacesCorollaryOfAnyTranslate.lean:2330
GenusMassAt D n : ∀ W positive definite of rank n, mass W.hT W.L0 = massI D n   -- …/GL5/DiscreteSeriesOfFormalDegree.lean:112
massI D M = mass (stdForm E M) (stdLat E M)                                       -- GSB/GeneralLinearActions/GapAtLeast.lean:20
SiegelMassRatioCM : mass(std_M)/mass(std_{M-1}) = massRatioRightSide K M        -- GSB/StandardLattice.lean:281 (builder input)
lValEta K M = ∏' P, (1 - (-1)^M N(P)^(-M/2))⁻¹ [P̄ = P]  or  (1 - N(P)^(-M))^(-1/2)  -- Formalism/HermitianLattices/StatementMass.lean:37
```
These are Siegel-type mass formulas for unitary groups, with the Euler product of L(M, η^M) over E. [I]

**(c) The period identity in `rRows`** (`Formalism/LocalToGlobal/IndefiniteReal/IsometricPeriodsOfHypotheses.lean:99`; `MIstar2` at `IsometricPeriodsOfUnitHypotheses.lean:27`): [R]
```lean
def MIid eV sEE d := ∀ u t φ F, d.ζC u t * v0 ((fc X.zs).Dc.Pt u t φ F)
    = d.a u * ⟪sEE (d.V (X.Θ t (X.jR t (eV t F)))), (fc X.zs).Sp.Pu u ((d.U u).mulVec (cpt v0 φ))⟫_ℂ
def MIstar2 eV sEE := ∃ d, MIUnit2 d ∧ MIid eV sEE d ∧ AuNZ d      -- AuNZ: ∀ u, d.a u ≠ 0
```
`MIUnit2` says the following. [R]
- V is an isometry of `EEl`, and each U_u preserves the frame norm. [R]
- ζC never vanishes, has valuation 0 at every finite place, and ζC(u, μ0) = 1. [R]

So the definite period of φ against F equals, up to a unit and a nonzero constant, the inner product of the theta lift Θ_t(F) with φ's image. The shape is Rallis-like, but no L-value is attached. [I] The supplier is `miStarRow_alt_alt` (TPS/MainTheoremPublishedInputsThird.lean:22). [R] It takes HoweUnram, WeilRepresentationUnitaryPair, WeilSiegelFormulaUnitary, both forms of Siegel–Weil, DoublingMethodLocalZetaIntegrals, UnramifiedDoublingGL, StrongApproxSU and the Harish-Chandra items. [R]

**(d) `sO`** (`…/FlagStabilizerTensors/ThmSOwn.lean:669`): [R]
```lean
… → ∀ u u', u ≠ u' → ‖((s.2 x hx h0 i).Y.tO u u').K0‖ ^ 2 ≤ (1 + (b ^ 6)⁻¹) * (duS u * duS u' / Dstar)
```

**(e) Bessel multiplicity one** (`UniqGap`, `Development/AbelianVarietyTheory/Definitions/SemilocalFrames/UniqGapOfUniq.lean:17`). [R] Take a discrete series σ of U(p,q), n = 2r+k+1, with Harish-Chandra gap h ≥ 120·n³. [R] Then any two Bessel maps B₁, B₂ from σ to π satisfy `∃ a b, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v smooth, a • B₁ v + b • B₂ v = 0`. [R] This is a local GGP-type multiplicity-one statement. [I] It is supplied by `CompanionTheory.Lime.BM.uniqGap_holds` (FM/BesselMultiplicityOneLargeGapAndWhittakerBessel.lean:9). [R]

**(f) `LinkN`** (GTI:40–47): [R]
```lean
LinkN_at L j C := Summable (vvTerm D) → etaSum L j ≤ dZ0 j * (C * (f m b L² + log² x · Nc) + ∑' l, vvTerm D l)
vvTerm D l := log l * Σ_{1 ≤ e < t} shaLen l e   (l prime)
```

**(g) `LitThin`** (GSB/ShortIntervalPrimes.lean:128–158). [R]
- `adm6`: there are at most C1·Q^(1/4) zeros of primitive L(s,χ) with conductor ≤ Q in [1 − 1/400, 1] × [−Q, Q]. Outside the region 1 − c/log(N·|t|) only a simple real exceptional zero occurs. [R]
- `adm7`: a truncated explicit formula for ψ(u, χ). [R]
- `adm11`: the number of zeros near height t is ≤ C·log(N(|t|+2)). [R]

No statement here concerns the critical line. [I]

## 5. Chains

- `UpperTheory.FinalTheorems.riemannHypothesis` (CB/MainConclusion.lean:13) → `everyCharacter_of_row` (:7) → `every_character_of_literature_of_vWin` (TPS/EveryCharacterOfLiteratureOfVWin.lean:810) → `every_character_of_theta_integrals_local_matching` (TPS/SiegelEisensteinSecondTermHypotheses.lean:69) → `every_character_of_green_v_win` (TPS/TopPlug.lean:16). [R]
- The record comes from `nonempty_hyps_definite_side_of_closed_bound` (TPS/SiegelEisensteinSecondTermHypotheses.lean:44) → `hypotheses_nonempty_of_unramified_exponents_alt` (TPS/HypothesesNonemptyOfUnramifiedExponents.lean:41) → `nonempty_hyps_of_allRows_alt` (TPS/NonemptyHypsOfAllRows.lean:19) ∘ `allRows_of_open0_alt` (TPS/LinkROfIsLinked.lean:50). [R]
- The record is consumed by `forall_goal_of_shape_of_hyps` (TPS/ShapeOf.lean:31) → `shape_closed_link_n_of_green` (TPS/TopShape.lean:33) → `topDesWin` (CB/DesWin.lean:11) → `link_gl` (GI/LinkGl.lean:14) → `famGLmin_of_realPlaceSecondLayer` (GSB/TuSizeOfRealPlaceSecondLayer.lean:14) → `FamGLmin.link8` → `linkGLOBAL7_min` → `linkGLOBAL7_items` → `linkCore` → `ChainTied` (GSB/TieGlobal.lean:97) → `zeroFreeAll_of_topG` (CB/ZeroFreeAllOfTopG.lean:26). [R]

## Not read

- The existence proofs behind `hEx` and `hMem`/`ExBL`: `member_bundles_large_unramified_exponents_alt` and `memberTop_final_contextParameters`. This is where built points carrying `RowInt` and `jets` would have to be constructed.
- The bodies below the one-line wrappers: `formsMap_of_symmetricComparison_lowerMap_finiteChar`, `closing_true_cols`, `admissible_period_twist_of_integral_rows`, `rowFormsMatchPeriodMap_of_furtherProperties`, `bundle_bothParts_of_standardKernel_and_six_hypotheses`, `cmGoodModel_of_globalArtinReciprocity`, `main_theorem_published_inputs_variant_alt_alt`, `bothRowsFromSiegelWeil_alt`, `CarrierGap.offDiag`, `row_counts_of_ties_alt`, `row_rRows_of_parts_alt`, `linkedAt_hPA_prmR`, `linkedAt_hDcPtG_prmR`, `real_group_inputs_combined_alt_alt`, `bk_law_entries_alt`, `entries_combined_real_alt`, `row_hRB_univ_alt`, `volume_signature_indep_and_classNumberItems`, `classNumber_of_index`, `genusMassStd_of_landherrHasse`, `final_of_alt`.
- The CompanionTheory proofs of Siegel–Weil, `uniqGap_holds`, `wuDecayOfGap_holds'` and `automorphic_forms_finite_dimensional`. Also `ZerosNearOne.main` and `explicit_formula_and_window_count`.
- The bodies of the `_alt` link producers. I read only their arguments.
- `countF_fam`, `slopesMF_of_count_fam`, `slopesNF_of`, `frameF_of`, `lossF_of_7`, `latF`, and the `M.data_*` helpers.
- The definitions `TypeAt`, `RowNG`, `RowMain`, `WuDecay`, `OneMapRowR`, `PrimRows3`'s subfields, and `CountData`.
- `Main.lean:4` (`riemannHypothesis := rhOfAll`, from `Supplements`). I followed `UpperTheory.FinalTheorems.riemannHypothesis` instead.
