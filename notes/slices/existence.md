# The existence side: what is shown to exist, and by what means

Read 2026-11-20 from source text only; nothing was built. Paths are relative to `src/`. Abbreviations: TPS = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`, CB = `Development/AutomorphicArithmetic/CharacterBoxes/`, AM = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/`, GT = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/`, IW = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/`, GSB = `Formalism/SharpRestriction/GlobalSchurBounds/`, LRC = `Formalism/LocalRingCardinality/`.

Tags: **[R]** read and transcribed; **[P]** proved-by (I read the proof body and name what supplies it); **[I]** my interpretation.

## 0. Direct answers

**What exists.** `hEx : MinkDiv → ExS 𝒜 cT` asserts this: for every window exponent la > 1 and every host requirement G with `HostExW la G.req`, at every small ε there are families `Fm` in `𝒜 ∧ G.cls la` with all the `DesignChoices` properties. [R] The proof builds those families from explicit objects, in four layers. [P]
- A base field and a column input: genus classes of Hermitian lattices, a CM elliptic "ambient", and theta-kernel jets. These come from class field theory (`step_pinned`, `evLg_canonical`). [P]
- An indefinite-side real datum, from archimedean representation theory: discrete series, Harish-Chandra modules, Casselman–Wallach (`datExS_evLg`). [P]
- A level prime T(u) in a short window, from an in-tree theorem on primes of a norm form in short intervals (`levelPrime_unconditional`). [P]
- Hosts on windows. These are not constructed: `HostExW` is a hypothesis of `ExS`, supplied at the top from `VWin` by `supplyChi` (TPS/TopPlug.lean:13). [R]

**(a) The definite forms are not produced by an existence theorem.**
- `Mu0 := (I.S 0).Fi emb σ (lamT hc 0)` (AM/PredMemGamRanks.lean:656). [R]
- `Fi` (:151) is `{φ : Cl → (Fr → ℂ) | ∀ c, φ c ∈ ValC Gr λ ∧ ∀ g ∈ Stab c, tr g (φ c) = φ c}`. [R] Here `ValC` (`Formalism/LocalToGlobal/HermitianForms/IsLocBasis.lean:49`) is the polynomial model of `VV = ⊗_τ ∇(λ_τ)` (`Formalism/LocalToGlobal/Divisibility/CoefMod.lean:67`). [R]
- So the space is all stabiliser-invariant V_λ-valued functions on a finite class set: every algebraic modular form of weight λ on the definite group, with no Hecke-eigen selection. [I]
- M_u is `Mram = Mu0 ⊓ ⨅ v, ker(Σ_{c∈(F_v)ˣ} rhoT v c)` (LRC/DataKernels.lean:149), the forms with no invariants under the T-torus. [R]
- The lifts are finite sums `K(φ)(c') = Σ_c |Stab c|⁻¹·Kmap c c' (φ c)` (`kerOpM`, `Formalism/ThetaLiftIndependence/Statement.lean:47`). Here `unf` is a jet at 0 of theta functions `thAt … I.A …` of the CM ambient (AM/LatAtLattice.lean, `chIn`; PredMemGamRanks.lean:442). [R]
- The substance is a dimension count. [P]
  - `ClassNumberFormula₂` (GSB/StandardLattice.lean:453): `#cls₀ = massI D k · idxPi g₀ g₁ · (T^k − 1)^f`. [R]
  - `Mu0Tie` (:458): if the level-0 stabilisers are trivial, `finrank Mu0 = #cls₀ · ∏ dimV`. [R] Hence `Conclusion4f` (:463): `finrank Mu0 = du* · (T^k − 1)^f`. [R]
  - `family_property_and` (GSB/LinkMin.lean:463): `du = duS·(1 − 1/(T−1))^f`. [R]
  - T is chosen so that `C0⁻¹ ≤ duS·Γ²/D* ≤ C0` (`ChProviso_at`, GSB/Chosen.lean:53), proved by `chosenProviso_min` from `hn4` and `RankTiesF`. [P]
- I met no automorphy lifting, Galois-to-automorphic existence, or trace-formula count on this path; the scope of that claim is limited by the "Not read" list. [I]
- One global statement does appear. `MultEq` (`Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinRepApply.lean:118`) says that cuspidal multiplicities agree for two unitary groups with isomorphic finite-adelic points. It serves the indefinite realisation; its proof, `twisted_multiplicity_one`, was not read. [R]

**(b) Where the three hypotheses go.**
- The literature bundle P (`UnitaryGroupThirdPlaceHypotheses`) is used only in `member_bundles_large_unramified_exponents_alt` (TPS/MemberBundlesLargeUnramifiedExponents.lean:34). [R]
  - It fills `HypAAlt` (`…/LocalTypeDictionary/HypA.lean:13`). That record holds ray class fields, principal ideals, good reduction of CM curves, Harish-Chandra modules, cusp decay, Casselman–Wallach, the Weil representation, discrete-series existence and uniqueness, formal degrees, convergent Siegel–Weil, `SiegelMassRatioCM`, Artin reciprocity and Weber ray fields. [R]
  - It also fills `MemberHypotheses`, `MultiplicityCoverHypotheses` and `EllipticHypothesis` (TPS/MultQ.lean:24). The last is Galois cohomology: Poitou–Tate, Greenberg–Wiles, Chebotarev, local Tate duality, Euler characteristics. [R]
  - Its outputs are three. `SiegelMassRatioCM := hA.a18`. `MemberE` comes through `member_exists_baseLattice_alt`. `ExBL` comes through `compatibleSystem_weilBlock_ne_alt`. [R]
  - *Reading:* class field theory builds the fields and the CM ambient; archimedean representation theory builds the indefinite datum; Galois cohomology proves `ExportF` (next item). [I]
- **"Automorphy" here is a Galois-side export, not the creation of forms.**
  - The theorem named `automorphy_of_hypotheses_alt_alt` has type `ExportF KPx (IsBuiltE …)` (TPS/AutomorphyOfHyp.lean:44). [R]
  - `ExportF` says every built core satisfies `ExportAt` (AM/AmbientBaseHeq.lean:36): good twists exist for the Bloch–Kato reduction. [R]
- **`RowRat`** (GT/GeometricWeakTiesOfStrong.lean:18) requires, at every start datum, the rational row test `RowTest (z.R.toCx3 z.F)`. [R]
  - `RowTest` (`Formalism/LocalToGlobal/IndefiniteReal/RationalAdjoints/RatZOfTests.lean:18`) asks for a finite family of functionals that separates points of the target `EE`. Applied to the theta lift `Θ_t(j_R x)` of any K-rational vector x, each functional must take a value in K. [R]
  - `RowRat` is supplied by `test_vector_assembly_holds` (TPS/SiegelEisensteinSecondTermHypotheses.lean:49). [R]
  - Its only consumer is `compatibleSystem_member_rationalWeights … hR`, which produces `MultiplicityCoverHypotheses`. That record's `multW` field pairs `MultEq` with `RowTest` (`…/LocalTypeDictionary/MultiplicityCoverHypotheses.lean:15`), and through `w_of_weight_residue_char` it gives `WeightCaseCondition`, which `has3` needs. [R]
- **`RecTExists`** (`Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:78`) is a weak local Langlands correspondence. [R]
  - For each number field E and finite place w it gives a map `rc` from irreducible representations of GL_n(E_w) to Weil–Deligne representations. [R]
  - The map obeys `LawsT`: dimension, characters through the local Artin map, Langlands segments, cuspidal ↦ irreducible, twist by |·|^s, central characters, contragredient, injectivity on "Good" representations, depth zero ↦ tame, and a type law through Green's characters. [R]
  - It is supplied by `UpperTheory.Zero.LLC.recTExists` (CB/MainConclusion.lean:8). [R]
  - On this path it is a parameter of the slot types. `Nx := NX hL N`, and `NCore hL t n` carries `a : NAt hL …` together with a row that ties the local parameters `a.all.gal.lp` to the indefinite rows (AM/RatInEig.lean:79). [R]
  - `LocalLanglandsHypothesis hL` (TPS/HypN.lean:31) demands `GoodRowCuspParam` at every row. [R]
  - *Reading:* its role is to attach local Galois parameters to local components, which is Galois-side bookkeeping. It produces no forms. [I]

**(c) "Large unramified exponents" and the level prime.**
- The property A is `GridA (max CF0 CF1)` (TPS/SiegelEisensteinSecondTermHypotheses.lean:57; AM/GKeyFin.lean:61). [R]
  - It says: at every large base, for every realisation with `HidaSetting`, any grid datum `G₀` can be replaced by one with the same key that is `Full` (:43). The key is a place v₀ of F, a place over it, and characters χ_H(1..m). [R]
  - `extensionWithAtProperty` (TPS/ExtensionWithAtProperty.lean:16) multiplies the slot by `PLift (A K B f T)`. Built points therefore carry A; A constrains them and creates nothing. [R]
  - The label is uninformative: nothing in A mentions exponents. [I]
- T(u) is fixed by `LevCh` (AM/DuStarPos.lean:38). [R]
  - T is prime and T ≡ 1 mod QS·q·d. [R]
  - T = ππ̄ with π ∈ K and π ≡ 1 mod QS·q·d·(g₀g₁)². [R]
  - T lies in the window `T* ≤ T ≤ (1+1/(fk))T*`, where `T* = (D*/du*)^{1/(fk)}·Γ^{−2/(fk)}`. [R]
- T has three roles. [I]
  - The level structure at T makes the stabilisers trivial, so the dimension is exactly `du*·(T^k−1)^f`.
  - Choosing T tunes that dimension to D*/Γ², the size of the target.
  - The (F_T)ˣ action defines the ramified part, which costs the loss `aP10` over T.
- Existence of T: `LevelPrime` (GT/LogCondLeThree.lean:81) gives a prime in `[Ts, (1+1/(fk))Ts]` represented by the norm form whenever `c·m·L ≤ log Ts`. [R] It is proved by `levelPrime_unconditional` (`…/GlobalInterpolation/NormPrimesAndLevelPrimeUnconditional.lean:48`) from `levelPrimeN shortNorm`, which was not read. [R] `window_lower` supplies `cs·m·L ≤ log T*`. [P]

**(d) MinkDiv.**
- `MinkDiv := ∀ n, MinkMult n (minkM n)` (`Formalism/SharpRestriction/DesignExistsOfChoices.lean:12`). [R]
  - `MinkMult n M` says every finite subgroup of GL_n(ℚ) has order dividing M (GSB/MainIn.lean:51). [R]
  - `minkM n = ∏_{p ≤ n+1} p^{Σ_i ⌊n/(p^i(p−1))⌋}` is Minkowski's number (LRC/DataMink.lean:6, `Formalism/PeriodIntegrals/Minkowski.lean:7`). [R]
- It is discharged by `minkowski_bound_rat` (`Formalism/PeriodIntegrals/OrbitalBoundsConclusion/MinkowskiQ.lean:6`). [P]
  - That proof conjugates the finite group into GL_N(ℤ) through the lattice spanned by orbits (`…/MinkowskiTorsionFree/Lattice.lean:124`). [P]
  - It then applies `card_dvd_minkowskiNumber`, which is built from a trace step and a power-sum step; neither step was read. [P]
- Use: in `designS` it gives `DGamDvdF` (CB/DesignS.lean:73): each `DGam`, the lcm of stabiliser orders, divides `minkM(2·f·N_m)`. Then `dGamSize_of_dvd` gives log DGam ≤ 12·f·N·log(fN) (DesignExistsOfChoices.lean:46). [P]
- DGam is the denominator allowed in the period-integrality rows. [I]
- In `classSel` the MemberE premise ignores MinkDiv: `(fun _ => hMem)` (TPS/HypothesesNonemptyOfUnramifiedExponents.lean:61). [R]

**Non-degeneracy.** None of the three items can be zero or empty on the used path. [P]
- **d = rank N_u > 0.** [P]
  - `HidaSetting` (`Formalism/RankGapBounds/MeanBoundSecondForm.lean:111`) requires `∀ u0 u, 0 < d u0 u`, and `TieLocal` (GSB/TieGlobal.lean:64) sets d = `rank (Nu u)`. [R]
  - `linkCore` supplies this from `LatF` ← `lat_at` ← `MuRank`. `muRank_min` (GSB/LinkMin.lean:665) shows rank = `A.du = duS·(1−1/(T−1))^f`. [P]
  - Here duS > 0 by `jnt_duS_pos_of_proviso` (GSB/JointsL.lean:1320), and T > 2. [P]
- **m ≥ x^{1/2−ε}.** [P]
  - `RestSize` (`Formalism/SizeWindowBrackets/SChain.lean:53`) is a conjunct of `ChainTied` (GSB/TieGlobal.lean:114). [R]
  - It is supplied from `Win_at` (GSB/QuadraticLogDerivCongr.lean:231), which `size_windows_of_thick_set` (:1816) derives from the family field `sizes : SizesAt`. [P]
  - `SizeM` (`Formalism/SharpRestriction/ElevenLe.lean:27`): `x^{−θ}√(xδ₁) ≤ m ≤ x^{θ}√(xδ₁)`. Alongside it, n ≈ x^{2+8ε} and k ≈ x^{9/2+10ε}. [R]
- **B_u ≠ 0.** This rests on an inference. [I]
  - `LinkS_at` (`Formalism/SharpRestriction/GlobalTheoremInputs.lean:145`) requires `‖KD u u − id‖²_HS ≤ e0·duS`, with `√e0 ≤ exp(−x^{ε/8})`. [R]
  - `KD u u` acts on a space isomorphic to `Mu0`, of dimension duS (`Formalism/SharpRestriction/CuspSpanNormBounds/RelevantZeroGramTerms.lean:509`). If it were 0, then duS ≤ e0·duS, which is impossible. [I]
  - Theorem F's input `InputSG` (`Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean:30`) has the same clause, `‖γ_i B_iᴴB_i − 1‖² ≤ e0·rank`. [R]
  - `BesselId` (GlobalTheoremInputs.lean:65) gives `Bu = a·besS(Uφ, VF)` with a ≠ 0. [R]
  - I did not read `frame_at_of`, so it is not confirmed that `KD` is the Gram operator of `Bk u`. [I]
- **Families and words are nonempty.**
  - `FamCore` requires `Nonempty (Ix x)` on an unbounded window set (`Formalism/SharpRestriction/FamCore.lean:71`). [R]
  - Every `D7` has a field `u₀ : Word`. [R]
  - `QOf` is guarded by `κ.Pos`, but `Link` carries `pos : κ.Pos` (GT/ValidForConstructedPointClassesEventuallyWorking.lean:222), so that guard is not vacuous. [R]
- What is true by construction.
  - The constants: `designS` sets `CTu := cT eps 9` and proves `CYL = 9`. [R]
  - `D7` by itself admits zero data, since `Mu0` and `unf` are arbitrary fields. Zero data is excluded only by the class constraints above. [R]

**Upward trace.** `hEx` is a field of `HypsAlt`. [R]
- `goal_of_shape_of_hyps` passes `h.hEx` as the third argument of `shape_closed_link_n_of_green` (TPS/ShapeOf.lean:16). [R]
- That theorem uses it once (TPS/TopShape.lean:50): `designExists_of_tuSize_aux4n_litThin (𝒜 ∧ G.cls la) cT (fun hM => hEx hM la G hla hH) …`. [R]
- That theorem in turn applies `hEx minkowski_bound_rat` inside `designExists_of_choices` (TPS/LinkEx.lean:15). [R]
- The resulting `DesignExists` is the first argument of `topDesWin` (CB/DesWin.lean:11), which picks a family `Fm` and proves `ChainTied` for it through `LinkGLOBAL`. [P]
- That gives `FamilyClassConnected (G.cls la)` (CB/DivinNOfHypV.lean:13), which is `TopG` (CB/ZeroFreeAllOfTopG.lean:12). [R]
- `zeroFreeAll_of_topG` (:26) instantiates G = `GChi ψ` with la = 3/2. [R]
- `link_ex` is the consumer only on the off-path `shapeWin`. [R]

## 1. The definitions

- **`ExS 𝒜 cT`** (CB/ExS.lean:10) [R]:
  ```lean
  ∀ la G, 1 < la → HostExW la G.req → DesignChoices (WithTw fun Fm => 𝒜 Fm ∧ G.cls la Fm) 3 cT
  ```
- **`ExD`** (CB/Supply.lean:38) is the same statement in the `DC.` namespace. [R] `hEx` is built from `ExD` by `working_classes_frozen.2` (TPS/NonemptyHypsOfAllRows.lean:59). [R]
- **`DesignChoices 𝒞 C0 cT`** (DesignExistsOfChoices.lean:22) [R]:
  ```lean
  ∃ ε0 > 0, ∀ eps ≤ ε0, ∀ K, ∃ Fm CH C5 Cb, 𝒞 Fm ∧ 0 ≤ CH ∧ Fm.Large K CH ∧ … ∧ ThickSetEventually Fm ∧ ChosenTT Fm ∧ ChosenBad Fm Cb ∧ ChosenQD Fm C5 ∧
  ChosenCode Fm C0 CH ∧ BoxesF Fm ∧ QDRowsF Fm ∧ DGamDvdF Fm ∧ cT eps Fm.CYL ≤ Fm.CTu ∧ TameDistinctF Fm ∧ Fm.CF = CH ∧ CodeUpF Fm C0 CH ∧ Fm.CYL ≤ 9
  ```
  - `Fm.Large K CH` (`…/ParamsHeightRankConstant.lean:138`) only makes the family's constant lists exceed transported thresholds. It bounds no rank. [R]
- **`DesignExists 𝒞 C0`** (:187) is `∃ ε0, ∀ eps ≤ ε0, ∀ K, ∃ Fm CH, 𝒞 Fm ∧ 0 ≤ CH ∧ Fm.Large K CH ∧ ChosenE Fm C0 CH ∧ TuSize Fm ∧ DGamSize Fm`. [R]
- **`MemberE 𝒮`** (AM/ThetaChr.lean:102) is `BaseCond KPx ∧ FirstG KPx (IsBuiltE 𝒮) ∧ ExportF KPx (IsBuiltE 𝒮) ∧ SecondG KPx (IsBuiltE 𝒮) (IsGoodE 𝒮)`. [R] Its parts (AM/NotBaseCondFalse.lean) are [R]:
  - `BaseCond.ex` (:15): eventually there is a base containing any prescribed finite sets of algebraic numbers.
  - `FirstG` (:53): `Step KPx (untwisted T) (HasCore Q)`, so for all large bases with untwisted T a core satisfying Q exists.
  - `ExportF` (:55): every Q-core satisfies `ExportAt`.
  - `SecondG` (:68): after enlarging to B′ and retwisting to T′, there is a core with `Q ∧ TwAllAt ∧ Q'`.
- **`ExBL KP Q Q' Lk`** (GT/EventuallyAllScaleContextsAndOfBoth.lean:71) is `∃ R, LargeBaseCondition KP Q R ∧ ExB (sAnd Q' R) Lk`. [R]
  - `ExB` (GT/ValidFor….lean:259) is `EvP fun _ K => ∀ β : BPt K, β.Is Q → ∀ c, ∃ b, Lk K β c b`: every point carries a bundle linked to it. [R]
  - The bundle `BundleCondition` (TPS/ColumnChoiceWithTies.lean:47) holds the indefinite record `R`, spectral ties `S`, row family `P`, square-integrable columns `C` and the bounded real realisation `B`. [R]
- **Class and selection.**
  - `𝒜 := cls (sAnd Q' R) Lk E = clsP (QOf …)`, and `clsP QO Fm := ∃ κ, Link κ Fm ∧ DQ.cls7 (QO κ) Fm` (:238). [R]
  - `QOf E κ D O := κ.Pos → ∀ c, ∃ b, Built Q Lk κ D O c b ∧ E κ D O c b` (:254). [R]
  - `Fc.Built κ D O c b := ∃ K (β : BPt K) b', κ.Of K ∧ β.Is Q ∧ Lk K β c b' ∧ ⟨D,O,b⟩ = ⟨β.D, β.O, b'⟩` (:250). [R]
  - `BPt` (:67) bundles stages, a core `c`, a layer `Y` and a `LedPart` p with `ChGood`, `RecOK` and `LedOK`. [R]
  - On the used path Q is `IsGoodE 𝒮 = positionOf (GoodE 𝒮)`, with `GoodE = BuiltE ∧ GoodO` and `BuiltE := ∃ b : Bl.Built 𝒮 K w Z c, EntC b.ker` (AM/ThetaChr.lean:85–91). [R]
- **A point and a family.**
  - `FamP eps` (`Formalism/SharpRestriction/ParConsts.lean:31`) extends `FamCore` (FamCore.lean:71). For each x it has an index type `Ix x`, a datum `D x i : D7` (LRC/RhoDetPrimeEqMuTildeMulChiPow.lean:76) and `L x i : SizeData₂`. [R]
  - It also has per-point parameters, `sizes : SizesAt`, and the lattice-defining fields `nuDef`, `nprimeDef`, `rrDef`, `h_eq` and `fills`. [R]
  - A point is `(D x i, objAt Fm x hx i)`. [R] In 𝒜 it equals `(β.D, β.O)` for a bundle point whose core has a `Bl.Built` record. [P]
- **`Bl.Built 𝒮 K w Z c`** (AM/NonzeroPlacesOverPrimes.lean:147) has the fields `pin`, `coh`, `g`, `col`, `what₂`, `rx`, `xi`, `lev`, `errX`, `n`, `nx`, `sx`, `ker0`, `ker_eq`, `ker`, `div`, `th`, `obj`, `ox`. [R]
  - `pin : ColPin` (AM/TiedColumnData.lean:78) holds `isTw` and `jets : ColIn.JetsIn` (the kernel jets lie in the field LL). It also holds `hX`, `above`, `half`, `d3b`, `selectedPlacesAgree`, `vals` and `roots`. [R]
  - `col : ColumnDataSplitPrimes` (:91) holds the tied forms `ColT` together with `isRec : IsRecG` and `om : OmegaCompatible`, which fixes the CM period Ω. [R]
  - `what₂ : RowsT` (NonzeroPlacesOverPrimes.lean:47) holds the indefinite rows `r`, `exAt`, the test-vector inner products `emt0` and `emt`, `etaF`, and **`rowInt`** (:61). [R]
  - `ker : KerT` (TiedColumnData.lean:111) holds the lift objects `O`, the kernel entries `E`, `served`, `iw` and `iw_pos`. [R]
  - `th : ThT` (:135) holds `AllTied`, the Weil-compatible equivariance `weq`, and `std : IsStdChar ψ (−1)`. [R]
  - `div : DivT` (:127) holds `Qp`, `chr`, `loc` and `geo`. [R]
- **`RowInt`** (GT/LowerTieTwAt.lean:80) has two fields, `ref` and `tw`. [R]
  - For each test vector F in `Mtilde μ` (for the untwisted μ0 and for each twist), every class value of F lies in that class's ∇-lattice (`RowVal`, :71). [R]
  - It is created inside the construction: `exists_rowsT` sets `rowInt := periodRowLatticesIntegral_provisionalRows …` (IW/ExistsRowsT.lean:62). [R]
  - This settles the hyps-record caveat. RowInt is established when the points are built, not assumed of them. [P]
- **Lattices.**
  - `lat i` and `ptLat` are fields of `MemberForms` (LRC/DataForms.lean:169, 203): `HLat LL` with `emb i` onto `Fi i` and `ptEmb` onto `ptC`, and `PtilIntegral` at :273. [R]
  - `NuLat u` lives in `SizeData₂`, tied to N_u by `nuDef` and `nprimeDef` (ParConsts.lean:70–71). [R]

## 2. Chains

- **Existence of families.** The chain runs `classSel` (CB/ClassSel.lean:14) → `recS` (CB/ObjCTrue.lean:30) → `memberTop_final_contextParameters` (IW/MemberTopFinalContextParameters.lean:14). [P] It continues:
  - `recAtG_of_two_passes` (IW/LayeredAutomorphicDataExistsOfTwoPasses.lean:23). [P] `BaseCond.ex` gives a base B, `FirstG` gives a built core at untwisted T, `SecondG` gives a good, retwisted core c′, and `lay_of_core` with `VolumeEqMass₂` gives a layer Y. [P]
  - `recExP_of_recAtG` (IW/ExistsLayeredDataOfGoodScaleContexts.lean:18) sets `du := duP`-valued naturals (`exists_du_nat`, AM/RecExGOfRecAtG.lean:13) and `Ds := DsP P`. [P] Here `duP = mass_k·idx^f·∏dimV` (AM/CmQuadraticFormEqAlternatingForm.lean:18), predicted numbers distinct from `du = finrank Mram`. [R]
  - `existsObjects_of_admissibleTwistDatum`, which uses `levelPrime`. [P]
  - `kitS` (CB/KitS.lean:15) builds a kit of points indexed by `Fin R.n` for each scale of the window set S. [P]
  - `designS` (CB/DesignS.lean:21): `exists_famP_of_kits`. [P]
- **`MemberE` and `ExBL`.** The chain runs `large_unramified_exponent_bundles_exist_alt` (TPS/MemberBundlesLargeUnramifiedExponents.lean:69) = `member_bundles_large_unramified_exponents_alt` (:34) → `member_exists_baseLattice_alt` (TPS/ExistsBaseLatticeOfPrime.lean:80) → `exists_baseLattice_of_prime_alt` (:57) → `exists_baseLattice_of_pair_alt` (:36) → `memberE_closing_alt_alt` (TPS/MemberEClosing.lean:17) → `memberE_of_steps2` (IW/ExistsMemberOfConstructionStepsSecondPass.lean:38). [P] Its inputs are:
  - `step_start` (:20) ← `step_pinned` (IW/StepPinned.lean:41) ← `evLg_canonical` (IW/EvLgCanonical.lean:97);
  - `exists_rowsT`;
  - `exists_constructedCore_of_all_construction_stages` (IW/…Statement.lean:12);
  - `ExportF` ← `automorphy_of_hypotheses_alt_alt`;
  - `BaseCond` ← `baseCond_KPx` (IW/ExistsPrePin.lean:30).
- **`ExBL`.** `compatibleSystem_weilBlock_ne_alt` (TPS/ExistsWeilBlockNeAtMember.lean:41) → `geometric_parameter_uniform_alt` (TPS/ExBLIsLinkedPrmRStatement.lean:18). It takes `MultiplicityCondition` from `member_multiplicatively_closed_alt` (TPS/MultiplicativeClosurePrimeMem.lean:47). [P]
- **The indefinite datum.** `datExS_evLg` (IW/ExistsFineAdelicDatumOfHyp.lean:81). [P]
- **Top.**
  - The record comes from `nonempty_hyps_definite_side_of_closed_bound` (TPS/SiegelEisensteinSecondTermHypotheses.lean:44) → `hypotheses_nonempty_of_unramified_exponents_alt` (TPS/HypothesesNonemptyOfUnramifiedExponents.lean:41) → `nonempty_hyps_of_allRows_alt` (TPS/NonemptyHypsOfAllRows.lean:19). That last step calls `classSel` (:51) and sets `hEx` (:59). [R]
  - The record is consumed by `goal_of_shape_of_hyps` (TPS/ShapeOf.lean:16) → `shape_closed_link_n_of_green` (TPS/TopShape.lean:33) → `designExists_of_tuSize_aux4n_litThin` (TPS/LinkEx.lean:15) → `topDesWin` (CB/DesWin.lean:11) → `zeroFreeAll_of_topG` (CB/ZeroFreeAllOfTopG.lean:26) → `every_character_of_green_v_win` (TPS/TopPlug.lean:16). [R]

## Not read

- The bodies of `has3_neo_of_localLanglands_alt`, `all_stages_at_member_of_specializations_alt`, `has4_of_has3_of_lv3Mv`, `CoreAsm.stepW_core`, `ambEx_of_rx`, `divEx_geoCl` and `exists_thetaData_trueRowsColumns_allCompatible`.
- `lay_of_core`, `volumes_eq_masses_of_unfold`, `window_lower` and `DuInt.duStarOf_nat`.
- `existsObjects_of_admissibleTwistDatum`, `hostWW`, `exists_famP_of_kits`, `working_classes_frozen` and `assemble`. That `D.mem = cols.mem` is inferred from field names.
- The bodies of `exportF_isBuiltE_alt_alt`, `exBL_isLinked_prmR_alt`, `twisted_multiplicity_one` and the three `compatibleSystem_*` theorems.
- `levelPrimeN shortNorm`, `minkowskiBound_of_steps`, `recTExists` and `llOf_alt`.
- `periodRowLatticesIntegral_provisionalRows`. I rely on the period-rows slice for it.
- `classNumber_all`, `rankFormula_of_classNumber` and the source of `RankTiesF`.
- `frame_at_of`. It is needed to confirm that `KD` is the Gram operator of `Bk u`.
- `evaluation_grid_of_join` and `test_vector_assembly_holds`.
