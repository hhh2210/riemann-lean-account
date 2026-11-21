# Four vacuity flags, settled from the source text

Read 2026-11-20 from the source text only; nothing was built. **read**

Paths are under `lean/src/`, with these abbreviations:
- DV = `Formalism/LocalToGlobal/Divisibility/`
- AM = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/`
- IW = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/`
- IE = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`
- TPS = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- TC = `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/`
- LLC = `Formalism/SharpRestriction/LevelLetterCocycles/`
- FST = `Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/`
- TD = `Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean`
- GTI = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`

Tags: **read** means the statement or definition was transcribed; **proved-by** means the proof body was read and its inputs are named; *inferred* means my interpretation or my own derivation.

## Verdicts

| # | Question | Verdict | What settles it |
|---|---|---|---|
| 1 | Is the quantity bounded by the Sha lengths the real congruence length of the lift lattices, or can a record declare it zero? | **EXCLUDED** | `congruenceLength_twistedPlaces_of_heckeIntegrality` proves `D.what₂.etaJ (i+1) w = ite (D.plEq w ∈ S0.Tw) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0` for the localised record. That record's `etaJ` is by definition Σ `etaLoc`, and its local data must cover every maximal ideal (`mx_all`). |
| 2 | Is the abstract `D.s` the concrete Bessel–Poincaré setting, or could other data be substituted? | **EXCLUDED** | On the path, `D.s = mix _ (sOf P.fin)` by definition (`reStage`, `SPack.toNew`), and `SIso.Pu_eq : eHH (s.Pu u x) = s'.Pu u (eCu u x)` holds with linear isometries. A zero `Pu` would contradict clause 4 of Theorem S. |
| 3 | Do zero blocks B_u = 0, whose heights the guard leaves unconstrained, distort s? | **TOLERATED-HARMLESS** | The family field `h_eq` fixes `div.h u = hExpl6 … u` for every word. Then s = `sFrame` and u = `uFrame` are computed over all words, `theoremF` allows zero maps, and the rank share of zero blocks is at most (√e + √c)², where c = (1+√e)·√((1+η)δ). |
| 4 | Who fills `CuspUAlt` and `CarUAlt`, and is partial compatibility enough? | **TOLERATED-HARMLESS** | Both come from `galoisRepresentations_of_thetaLift tLiftK`, a single `Row0b recT` used twice. The consumer `GoodR` needs only Frobenius characteristic polynomials at split places away from ℓ, S and Q, and `RelW.eq_of_unr` supplies them. |

## Flag 1: the Sha-bounded η is the lattice's congruence length

**What is charged.** **proved-by**
- `inEta_num` (DV/SumLeEtaSumNum.lean:60) turns `DIVinN_at` into `InEta`: Σ_{y∈S0.Tw} lw(y)·etaJW ≤ divSize·dZ. Here `etaJW` is the local length of `Tl` modulo `cutZ` (DV/LiftLat.lean, `BlockDat.etaW`).
- `sum_le_etaSum_num` (:28) links the two sides in exactly one place: `h3 : D.what₂.etaJ (i+1) (D.plEq.symm y) = A.fam.etaJ … y`, obtained by `rw [hnum.etaJ i …]`.
- `BoundsIVAt` (DV/LiftLat.lean) states `jT ≤ etaW + dZ·(JexpW + vw DG + vw s)`, where `jT = jw (HZ) w (Tl)`. **read**
- So the Sha bound controls the congruence module T_j/cut_j, and that module bounds the discriminant index. *inferred* The proof of `biv` is taken from slices/main-term.md.

**Who builds the `NumTie`.**
- `inpAt_of` (Formalism/LocalToGlobal/InpAtOf.lean:14, call at :46) takes `hT.num` from the `DivTied3` antecedent of `InpAt` (Formalism/LocalToGlobal/PtKOfReal.lean:61). **proved-by**
- `ptK_of_real` (PtKOfReal.lean:112) passes that antecedent along (`hInp NuC I hT' hI'`, :137). **read** The row package builds the antecedent as `DivTied3.ofSplit P.tied.div hR` (DV/RecBridgeSel.lean:60). **read** I read that line, but not all of `pkg_of_rowsK`. *inferred*
- The `num : NumTie` field of `hR : DivRows3` (DV/DivisionCompatibleToSub2Indef2.lean:285) matches the record row `hDivG : DivRows3G` (`Development/AbelianVarietyTheory/Definitions/GlobalTwisting/CountsIrreducibilityConstants.lean:91`), whose field is `NumTieG` (:80). **read** `numTie_of_G` (DV/TupUsed.lean:108) converts back under `TupAllUsed`. **read** I did not read which conversion is invoked at this call site. *inferred*
- Its supplier chain: **proved-by**
  - `bk_law_entries_alt` (TPS/AtHDivGOfMiStatement.lean:20);
  - → `hDivG_of_mIstar2` (TPS/AtHDivGOfMi.lean:50);
  - → `divisionRows_pairing_vanishes_of_rational_pairing_law` (`Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BkLawEntries.lean:40`);
  - → `num := numbers_eq_concreteNumbers_at_baseLevel` (IW/DivisionCompatibleAtReadIdentifications.lean:45);
  - → `numTie_of_read` (IW/NumbersEqConcreteNumbersAtBaseLevel.lean:64).
- Inside `numTie_of_read`: **proved-by**
  - `Ij` and `jw` are proved by lattice comparisons (`ijIdx_eq`, `lattice_jw_index_eq_concrete_lift_index`).
  - `etaJ` is `rw [Z.etaJ]` (:88). This is the field `ReadL.etaJ` (AM/StableIffCarrierEq.lean:216) of the bundle's `TwIn`, reached through `TwIn.Z` (AM/DivisionPairOfAdelicFormsFaceColumnsData.lean:42) and `BundleWitness.x` (TPS/TwistedBundle.lean:58).

**Who fills `ReadL.etaJ`.**
- `RationalReadingWithoutCongruence.full Z h` (AM/RowsRestWordColumnUnitBaseTupleAlt.lean:301) builds the `ReadL` from `h : D.what₂.etaJ j w = etaOf R F j w`. **read**
- `etaOf` (:273) is `A3.A.fam.etaJ F.P0 F.ψ0 … (R.mu (D.plEq w)) (D.plEq w)` at twisted places and 0 elsewhere: the lattice length. **read**
- The row stage `Pk.what₂ … η hη` sets `etaJ := η` (:412). So the record holds whatever η the construction passes in. **read**
- `RowsAt P` (IW/FinitenessOfHyp.lean:194) produces rows only under the hypothesis `x.o.η j v = P.q.eta j v`. The right side is `RowPk.eta := etaOf z₀.R z₀.F` (AM/ReadPk.lean:94). **read**
- On the path, `lv3_of_third_alt_alt` (TPS/FinitenessOfHyp.lean:61) applies `RowsAt` at `oL x L` (IW/TwistDataAgreeAcrossCoefficientsLocalized.lean:50) and returns the point `(oL x L).Z` (TPS/FinitenessOfHyp.lean:81). **proved-by** The η of `oL x L` is `etaL x L := L.lay.fixZ.eta` (:20). **proved-by**
- For 1 ≤ j ≤ m, `NLay0.eta` (AM/NStageTrivialCharacterCoeffEqAlt.lean:79) is Σ_{i∈locs j w} etaLoc i. **read** `setN` and `withLoc` (:125; AM/RingSpecNormalisedCharacterEq.lean:367) install it, so `etaJ_tie` holds by `if_pos`. **read**
- The needed equality `etaL x L = P.q.eta` is the argument `he`. It comes from `EtaStatement'`, proved by `sEta_alt_alt_alt` (TPS/SLarge.lean:56). That calls `eventually_etaJ_eq_eta_of_levelC`, then `etaJ_local_compatibility_alt` (TPS/EtaJLocalCompatibility.lean:50). The latter's `key` (:29) is `congruenceLength_twistedPlaces_of_heckeIntegrality (withLoc L) …` (IE/CongruenceLengthTwistedPlacesOfHeckeIntegralityStatement.lean:6). **proved-by**
- That theorem goes through `etaJ_join_closed` to `etaJ_join` (IE/EtaJEqZeroOfUntwisted.lean:15). **proved-by**
  - At a twisted place it rewrites twice: Σ etaLoc = `etaRat` (`sum_localCongruenceLength_eq_rationalLength`), then `etaRat` = `A.fam.etaJ` (`rationalFormLength_eq_definiteFamily`).
  - Elsewhere it uses `etaJ_eq_zero_of_untwisted`.

**What forces the local data to be non-empty.**
- `sum_etaLoc_eq_etaRat` (IE/SumLocalCongruenceLengthEqRationalLength.lean:102) opens with `rw [D.etaJ_tie j w h1 h2]` (:105). It then decomposes the record's own rational lift lattice over `locs j w`, using `rationalForm_eq_sum_localisation_projections` (:225) and `integralFormLattice_eq_sum_localised_lattices` (:284). **proved-by**
- The first of these is `iV_eq_sum_Psi` (IE/RationalFormEqSumLocalisationProjections.lean:16), which calls `T.mx_all` (:26). **proved-by**
- `mx_all` (`Formalism/LocalToGlobal/NormalizedHeckeFactors/HeckeStdTwOfStd.lean:106`) reads: `∀ j w, 1 ≤ j → j ≤ m → muAt w ≠ mu0 → ∀ I maximal in heckeAlg B j w, ∃ i ∈ locs j w, mx j w i = I`. **read**
- So if `locs j w = ∅` at a twisted place, the proved identity forces the lattice length there to be 0. Empty local data cannot sit beside a non-zero congruence module. *inferred*
- This is what `LinkEta` (`LocsCoverTw`, a rank-coverage statement, LLC/LocsCoverTw.lean:7) would have supplied. `linkDIVt_of_rowsF` (DV/RecBridge.lean:656) discards it (`intro _ hN`). Losing it costs nothing, because the stronger coverage `mx_all` already sits inside the proof of the η tie. *inferred*
- The toy stage the earlier reading found does exist. `stepW_bare` (IW/LocalizationFreeStageTrueGroupColumnChoiceStep.lean:195) gives an N-stage with `IsEmpty N.nd.Loc` and η = 0. **read** It is the stage before localisation, and `nL x L` inside `oL x L` replaces it before the rows are read. **proved-by**

**The same record value feeds `LinkN`.**
- The family's datum on the path is `DL x L = withLoc L` (`DL_eq`, IW/TwistDataAgreeAcrossCoefficientsLocalized.lean:55). **read**
- The later re-staging `reL a Z := ⟨a.W, setV a Z, reStage a.st Z.Z, a.N, a.G⟩` (AM/RelabelledWeight.lean:38) keeps both the W stage and the N stage. **read**
- `LinkN` bounds `etaSum` of that datum through `etaJ_tie` and the local Ribet bound (slices/congruence-sha.md). So the number `LinkN` bounds and the number `inEta_num` charges to the lattice are one and the same record value, proved equal to the congruence length at every twisted place. *inferred*

**`IndefData` and `TieTwRec`.**
- `S0 = s0Of R F = (R.toCx3 F).data F.cr false` (AM/StableIffCarrierEq.lean). **read**
- In the η-tie proof, `y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0` is proved from `pins.char.tup.mu_ne`/`mu_off` (IE/CoefficientBuiltLocalHypothesis.lean, `hTw`). **proved-by**
- `TieTwRec L Tw` (DV/LinkDefN.lean:36) states only that each y ∈ Tw lies in `L.supp` with `muAt ≠ mu0`. It is supplied by `row_hTw_of_tie_alt` (TPS/RowHTwOfTie.lean:17) and serves only to dominate the `InEta` sum by `etaSum`. **read**

**Verdict: EXCLUDED.** No instantiation on the path can make the record's η zero while the congruence module T_j/cut_j is non-zero: the identity above is proved, and coverage is a field of the type it is proved under. *inferred*

## Flag 2: `D.s` is the concrete Poincaré setting by definition

**The slot and the record.** **read**
- `SAt` (AM/See.lean:16) carries `P : SPack D F0`, `S : SRest P` and `rowJ : RowJ R eE P.X P.inst P.G t S.j` (:26).
- `SRest` (AM/SameDegreeZeroFormsSelf.lean:39) has four relevant fields:
  - `hI : SIso D.s (sOf P.fin)`;
  - `colPin` (:42): `colDict … (hI.eCu u x) = D.s_Cu u x`;
  - `j`;
  - `rowPin` (:45).
- `SIso` (FST/ParametersTermRelations.lean:286) requires:
  - `eHH : s.HH ≃ₗᵢ s'.HH` and `eCu : s.Cu u ≃ₗᵢ s'.Cu u`;
  - `Pu_eq` (:292);
  - `volN = volN` and `volH = volH`;
  - matching term data.
- `sOf` (:238) sets `Pu u := puC hF u` (:251). That is `PoincareInHH.PoincareSetting.Pu X u Y.hK (Y.Dt u) (Y.reps u) …` (`puL`, :213).

**Who builds it on the path.** **proved-by**
- `has4_of_has3_of_sExt_none` (TPS/LevelThreeToFour.lean:19) supplies the theorem `has4_of_has3_of_lv3Mv` that `memberE_closing_alt_alt` uses (TPS/MemberEClosing.lean:20). It calls `satOfDiscreteSeries` (IW/ExistsSpectralObjectsOverReplacedStages.lean:63).
- `satOfDiscreteSeries` calls `exists_sRest_top` (IW/ExistsSpectralLevelObjectsReplacedStages.lean:24), which calls `exists_sRest_re` (IW/ExistsSRestRe.lean:82) with `hI := sIsoRe …` (:29).
- `nonempty_sAtL` (:42) packages the result for the re-staged point `reL a Z`, where `Z = ⟨P.toNew hD j, N, hh⟩`.

**Why the identification holds by construction.**
- `reStage` sets `s := mix X.S.s Z.s` (AM/RefilledStagesRecord.lean:41). `SPack.toNew` sets `s := sOf P.fin` (AM/SameDegreeZeroFormsSelf.lean:66), `s_Cu := colDictT …` and `sEE := (conjHH P.X P.G).comp j`. **read**
- `mix s t` (AM/RefilledStagesRecord.lean:20) is `{ t with … }`. It takes only `cdScale`, `Del`, `cloud_gap`, `letter`, `letter_inj`, `u_letter` and `atP` from the old record. **read**
- So `HH`, `Cu`, `Pu`, `volN`, `volH` and the term data are those of `sOf P.fin`, and on the path `D.s.Pu u = puC P.fin u` holds definitionally. *inferred*
- `D.s_Cu` is the concrete column dictionary into `(mem u).A.Mu0`, the space `Fi`. It is bijective and isometric (`P.bij`, `P.isom`). *inferred*
- `sIsoRe` supplies `Pu_eq` from `keep_pu_vol_aR` (:38). It compares with `sOf hF` for the re-indexed setting `reY Z P.Y`, which is the one Theorem S is proved for. **proved-by**
- In `exists_sRest_re`, `colPin` is discharged by `colDictL_reTr` and `rowPin` by `conjHH_eEECre`. **proved-by**
- `BundleWitness.s` (TPS/TwistedBundle.lean:63) pins the bundle's spectral ties to this slot's `SRest`. **read** `STies.hI` (FST/SpectralTiesReal.lean:249) is that `SRest.hI` (`SRest.toSTies`). **read**

**Remaining freedom.**
- What remains free is the isometries `eHH`, `eCu`, `j` and the `U`, `V` of `BesselId`, together with the scalar a ≠ 0 there. They conjugate the Gram blocks by unitaries and leave every Hilbert–Schmidt norm unchanged. *inferred*
- Trivial data cannot be substituted. If `D.s.Pu u = 0`, then `Pu_eq` gives `(sOf …).Pu u ∘ eCu = 0`, so the concrete map would be zero. That contradicts clause 4 of Theorem S, which is proved for the concrete setting together with the size window. *inferred*

**Verdict: EXCLUDED.** *inferred*

## Flag 3: zero blocks are tolerated, and their share is negligible

**The theorem as stated.** **read**
- `TheoremF` (Formalism/HarderNarasimhan/StatementFrameF.lean:26) has these hypotheses:
  - the height guard `(∀ i, B i ≠ 0 → htMap … ≤ h i)` (:42);
  - s·Σ card ≤ Σ card·(μ(N_i) − h_i);
  - `muMax(N_i) − h_i ≤ s + u`;
  - a frame on `Ball i : Matrix (κ ⊕ κ₁) (ι i) ℂ` whose κ-rows are `Y'⁻¹·B_i(v)·Y_i`;
  - `(1−δ)·|κ⊕κ₁| ≤ |κ|`.
- `theoremF : TheoremF := frame_theorem_log_ideal` (Formalism/HarderNarasimhan/ShiftInvariance.lean:61) holds for every family of maps, zero maps included.

**How h is supplied.**
- At the call site `frame_at_of` (TD:538), s and u are equalities, not choices: `s := sFrame D.div.Nu D.div.h` and `u := uFrame …`. The frame data are `Ball u = Bf u * Vr u` with `InputSG Bf γ D* η0 η1 e0`, and δ := `delp` through `LatGeom` (`Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean:59`). **proved-by**
- `sFrame` is the rank-weighted mean of μ − h over all words, and `uFrame` is sup(μmax − h) − `sFrame` (Formalism/LocalRingCardinality/DataArith.lean:131, :134). **read**
- The count-bound record sets `h u0 u := (Fm.D x (M.pt u0)).div.h u` (Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean:487). The family field `h_eq` (Formalism/SharpRestriction/ParConsts.lean:73) forces `div.h u = DV.hExpl6 …` for every word. **read**
- `hExpl6` (Formalism/LocalRingCardinality/KernelPlaceMeanBound.lean:25) is an explicit formula with no reference to `Bk`. **read**
- The count bound requires `DIV` at every word (Formalism/RankGapBounds/MeanBoundSecondForm.lean:118, `∀ u0 (u : W u0)`, no guard). It uses `HComp` (:126) and the same mean s (:92). **read**
- In the proof, `s_lower5` (`Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:50`) bounds s from below word by word from `DIV` and `SlopesN`. `u_function_le_mean` (:81) bounds uF, and `Ga_bound5` (:113) combines both with `SlopeIneq`. **proved-by**
- So a zero block carries the same h as every other word, it enters s and u, and `DIV` is proved for it. The freedom the guard leaves in the abstract theorem is not available at the call site. *inferred*

**Quantitative statement.** This is my derivation from the hypotheses of `TheoremF`. *inferred*
- Let n = |κ⊕κ₁|, Π the coordinate projection onto κ₁, D = Σ d_i, Z the set of words with B_i = 0, and z = Σ_Z d_i / D. Let Q = Σ γ_i Ball_i Ball_i*.
- (i) For i ∈ Z, Ball_i = Π·Ball_i. So Σ_Z γ_i‖Ball_i‖² ≤ tr(ΠQ) ≤ ‖Π‖_HS·‖Q‖_HS ≤ √(δn)·√((1+η)/n)·tr Q.
- (ii) tr Q ≤ (1+√e)·D, by Cauchy–Schwarz on the frame defect.
- (iii) Σ_Z tr(γ_i Ball_i* Ball_i) ≥ D_Z − √(D_Z·e·D), where D_Z = Σ_Z d_i.
- (iv) Hence z − √(ez) ≤ c with c = (1+√e)·√((1+η)δ), and so **z ≤ (√e + √c)² ≤ 2e + 2c**.
- Equivalently, the EE blocks carry at least (1 − √((1+η)δ))(1 − √e)·D of the frame mass.
- With the tree's numbers: e = 2e0 with √e0 ≤ exp(−x^{ε/8}); η ≤ 5x^{−CH} + 3exp(−x^{ε/8}); δ = delp ≤ exp(−x^{ez/7}). The bound on `delp` is **read** in GTI `LinkIRR`; the others are from slices/frame-and-glue.md. This gives z ≲ 4exp(−2x^{ε/8}) + 7exp(−x^{ez/7}/2). *inferred*

**A single zero block is still possible.**
- Each word satisfies `hsSq (Kd (Bram B V) ga u − 1) ≤ e0·(d u)` (`Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean:460`). **read**
- So B_u = 0 requires (1 − 8e0)·d_u ≤ |κ₁| ≤ δ·Dall. *inferred*
- The size window d_u ≈ D*/Γ² does not rule that out, because Γ² is far larger than 1/δ. *inferred*

**Verdict: TOLERATED-HARMLESS.** Zero blocks can occur, but Theorem F is proved for them, h is not chosen per map, and their share of the total rank is exponentially small. *inferred*

## Flag 4: the Galois fields are the in-tree theta-lift theorem, and the use is unramified

**Suppliers.**
- `ThetaLocalInputsAlt` (TPS/ThetaLocalInputs.lean:13) has the fields `gal : CuspUAlt` (:21) and `car : CarUAlt` (:22). **read**
- `localLanglandsGL_and_purity_at_member_alt` (TPS/LocalLanglandsGLAndPurityAtMember.lean:18) sets `what₂ := published_inputs_combined_alt_alt … A.gk A.gal A.car …` (:25). That theorem is `locComp_of_isRc_classMapD_cenLoc` (TPS/PublishedInputsCombined.lean:18). **proved-by**
  - `hCSD := bridgeStar_alt hGK` (:20);
  - `gal := hCSD.2 hGRP` (:29);
  - `car := carU_of_finite_gl_recT hFin hLL (hCSD.1 hCLGD)` (:30).
- `bridgeStar_alt hGK = ⟨ofDual_star_alt hGK, cusp_of_pair_alt hGK⟩` (TPS/SOneRow.lean:11). **read** The pieces: **read**
  - `carU_of_finite_gl_recT := fun _ _ h => h` (TPS/SPairs.lean:15);
  - `ofDual_star_alt` (TPS/SOfStar.lean:54), which is `carU_of_star_alt` (:44);
  - `cusp_of_pair_alt` (SPairs.lean:11), which passes from "polarized" to "polarized pair" by Gelfand–Kazhdan duality.
- `A = literature_automorphy O` (TPS/EveryCharacterOfLiteratureOfVWin.lean:609). **proved-by**
  - `gal := pair_u_of_literature O` (:617), which is `pairU_of_star_alt O.galoisRepOfPolarizedPairLit` (:285; SOfStar.lean:52, :41).
  - `car := O.caraianiLocalGlobalDual` (:618).
  - The record is reached through `litN := literature_nonexistence O` (:720) and `hyps_e_third_layer_ser_n_of_geometric_galois P.litN …` (TPS/HypothesesNonemptyOfUnramifiedExponents.lean:44).
- `O = ⟨h, recTExists, h⟩` with `h = galoisLocalGlobalStrong_recParameter` (Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7, :11). **read**
  - That is `galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK` (`…/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`);
  - which is `galoisLocalGlobalStrong_of_geometry_lift geoOne_holds up` (`…/IntegralStructures/GaloisRepresentationsOfThetaLift.lean:6`).
- So both fields are the in-tree theta-lift theorem, a single `Row0b recT`. It is used once as the polarized-pair row and once under the Caraiani label. Neither field is an assumption. *inferred*

**Compatibility asked for.** **read**
- `IsGalUAlt.away` (TPS/WeightsConj.lean:31, :35) requires `Aw (wdOf h hl ι r) (rc (algNorm σ))` at every place away from ℓ.
- `Aw` (TC/WeightsConj.lean:29) has four fields:
  - `dim`;
  - `unr : y.unr → x = y`;
  - `ine : NcW y → ∀ g, deg g = 0 → x.charPol g = y.charPol g`;
  - `mono : NcW y → x.mono0`.
- `isGalU_of_props_alt` (TPS/SOfStar.lean:33) builds `away` with `aw_of_away` (TC/OfStar.lean:43) from `AwayB` (TC/WeightsConjBis.lean:26). The `unr` field comes from `tor`, through `tor_of_unr` and `unr_mono0`.
- `AutomorphicGaloisAdmissible` (TC/AutomorphicGaloisAdmissible.lean:133) asks, away from ℓ, only for `RelW` (:23): `eq_of_unr : A.unr y → x = y` (:25), plus inertia polynomials under `Nc` only (:26).

**Compatibility the consumer uses.**
- `GoodR` (LLC/DataN.lean:1232) is `∀ x, IsHeckeGalois` (:1224): continuity, semisimplicity, and `charpoly (r σ) = heckePol N i x w` for Frobenius σ at w with `SplitOut` (:504). `SplitOut` means split, not above ℓ, not in S, not in Q. **read**
- `heckeQ` (TC/SplitBCOfGalIso.lean:71) proves this from `(hwd w …).eq_of_unr` (:87) alone. **proved-by**
- The characteristic-polynomial clause: **proved-by**
  - G1 (LLC/SumRepresentations.lean:115) says the coefficients of r_x(g) are the values of an element of T.
  - It comes from `charpoly_clause_of_chebotarev` applied to `GoodR` (TC/ConstituentConditionAtDistinguishedPrime.lean:240).
  - `CharpolyCoeffsInSubalgebra` (LLC/QuotientHomNonvanishingBound.lean:431) is built from this data. *inferred*
- `UnrOut`: **proved-by**
  - G4 (LLC/SumRepresentations.lean:142) asserts `UnramAt (r x) w` off ℓ, S and Q.
  - `crys_unram_of_lgc` (TC/ConstituentConditionAtDistinguishedPrime.lean:82, called at :242) gives it from `RelW.unr`, which is `eq_of_unr`.
  - `UnrNoChi.main_alt_alt` (TPS/ImportsExtraFurther.lean:15) uses it through `admG4_of_goodR`.
- `NoChiOff` (Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GlobalCore.lean:68): **proved-by**
  - `UnrNoChi.main_alt_alt` derives it from `galois_condition_six_of … hF.Conclusion2.2.1`.
  - That is `ConclusionG6` (LLC/SumRepresentations.lean:268): a χ₁-eigenline in r_x forces x ∈ ZN.
  - `facts_of_galois_preconditions_of_cutRec` sets this field to `prvG6_of_admissible'` (TPS/CFacts.lean:52). Its proof is `conclusionG6_of_adm_alt` (TPS/PrvG6OfAdm.lean:16), whose inputs are string decomposition, purity of string weights, and ℓ-adic realisation of Hecke characters.
  - I read this wiring only, not the proofs of those inputs.
- At ℓ, crystallinity and Hodge–Tate jumps are used only where the isobaric parameter is unramified, through `Nc.of_unr (iso_unr_l …)` (TC/ConstituentConditionAtDistinguishedPrime.lean:248). **proved-by**

**Verdict: TOLERATED-HARMLESS.** The compatibility proved is partial, and the uses read here need only equality at unramified places plus the Nc-gated cases. *inferred* One use remains open: the inertia condition at the places of S (`QuadAt`/`PolyAt`). `quadratic_unit_at_ramified_place` (IE/QuadraticUnitAtRamifiedPlace.lean:21) takes it from `ConclusionG5` (`prvG5_of_admissible_cutRec`, TPS/CFacts.lean:52) and `TameDesign.main`. **proved-by** I did not read whether those use only the Nc-gated clause.

## Not read

- `builtEx_of_published_inputs'` and the construction of `NdSpec` (`Sp.B`, `Sp.mx_all`). These show that a localisation with full coverage exists.
- The package `p : PkB`: whether `(p.sL μ j).lat`, which is `D.what₂.MtLat`, is the integral lattice of the real lift-level forms. That is the far end of `Read.latL` and `formsL`.
- The bodies of:
  - `rationalFormLength_eq_definiteFamily`;
  - `integralFormLattice_eq_sum_localised_lattices`;
  - `heckeStableLocalLattice_of_rationalIntegrality`;
  - `good_part_projector_spectral_at_every_localisation`;
  - `pkg_of_rowsK` beyond line 60;
  - `biv`.
- `keep_pu_vol_aR`, `eRT_keeps_term_data`, `colDictL_reTr`, `exists_rowIsometry_conjugatedGoodRows_finrank`, and the definition of `RowJ`.
- The proof of `frame_theorem_log_ideal`. The share bound above is my derivation from the statement, not the tree's.
- `conclusionG6_of_adm_alt`'s inputs, `prvG5_of_admissible_cutRec`, `TameDesign.main`, and `exists_globalStep_objects_of_cyclotomic_generator_inertia`.
- Whether any stage after Has4 rebuilds the W or N stage of the family's datum. The η argument assumes it does not, beyond `reL`.
