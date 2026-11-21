# The frame behind Theorem F, and the glued lattice behind `BoundsMu`

I read this on 2026-11-20 from the source text only; nothing was built. Paths are relative to `lean/src/`. Abbreviations:
- TD = `Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean`
- FST = `Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/`
- IR = `Formalism/LocalToGlobal/IndefiniteReal/`
- IF = `Formalism/LocalToGlobal/IndefiniteForms/`
- DV = `Formalism/LocalToGlobal/Divisibility/`
- GTI = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`

Tags: **[R]** means I read and transcribed it. **[P]** means I read the proof body and name its inputs. *[I]* means it is my inference.

## Direct answers

**(1) The frame.**
1. B_u takes a ramified level-T form φ of archimedean type u to a functional on the target lattice. Its value at x is the period of the m-fold iterated lift of φ, paired with any test vector F whose lowering ι(F) equals x. **[R]**
2. At the place embLL, B_u is the compression of a Poincaré-series map P_u to the subspace EE, up to unitary changes of basis and a nonzero scalar a(u). P_u maps all type-u forms of level T into a space HH of dimension Dall; B_u is its restriction to the ramified forms. **[R]**
3. `InputSG` constrains the maps P_u. Put K_uu' = (c0_u·c0_u')^(−1/2)·P_u*P_u', where c0_u = volN·volH/dim π_u. Then **[R]**:
   - for u ≠ u', ‖K_uu'‖²_HS ≤ (1+η0)·d_u·d_u'/D*;
   - ‖K_uu − 1‖²_HS ≤ e0·d_u;
   - Dall ≤ (1+η1)·D*.
4. This is a nearly tight frame, not a nearly orthonormal family. Each off-diagonal block has about the HS size it would have for independent random subspaces. Tightness comes from Σ_u d_u ≥ D*/sg, that is, from having many words. *[I]*
5. The proof is a relative trace formula for these Poincaré series ("Theorem S"). **[P]**
   - The identity orbit gives 1 on the diagonal and 0 off it.
   - Degenerate orbits vanish off the diagonal by Schur's lemma for distinct archimedean parameters. On the diagonal they are at most exp(−k·f·log k), which comes from Bessel multiplicity one in a large-gap range.
   - Generic orbits are bounded by a second-moment expansion over pairs of orbits, with inputs from Siegel–Weil.
   - Dall ≈ D* is proved by counting points.
   - The Rallis/`BForm` scalar identity is not used.
6. In numbers **[R]**:
   - sg = x^(−CH);
   - de = exp(−2x^(ε/8));
   - e = 2e0, with √e0 ≤ exp(−x^(ε/8));
   - η = 5x^(−CH) + 3exp(−x^(ε/8));
   - δ = delp ≤ exp(−x^(ε/(7J))).

   The tree proves (η + 4√e)·x^CH ≤ 6. With HH ≤ x^CH·b, Theorem F's error is therefore at most 6b, where b = exp(x^ε).

**(2) The glued lattice.**
1. R is a lattice in K^D, the coordinate space of a block of base-type forms: the forms orthogonal to the kernel of an m-step map Θ into EE. **[R]** R is glued prime by prime: at each w it is the Θ-image of the projected integral forms of local type μ(w), and μ(w) differs from the base type at finitely many primes. **[R]** These forms are D7's test vectors and Θ is D7's lowering map `iota`. *[I]*
2. There is one lattice M_j for each lift step j ∈ J, and |J| = m. M_j lies in an auxiliary space W_j that receives the single-step lift θ'_j. T_j is the level lattice of the forms of the j-th lift. **[R]**
3. The determinant identity is not a seesaw and not a Fock-space identity. It says that the scalars by which the lifts act multiply. **[R]**
   - On each Hecke piece p, ΘΘ* = κ·∏_j λ_j(p) and θ'_jθ'_j* = λ_j(p); these are `ThmBop` and `ThmAop` at v0.
   - The pieces of K^D and of each W_j have equal dimensions.
   - `SpecDet` then multiplies the determinants.
4. The terms m·ph(a) and Ω^a are not produced by `BoundsMu`; they enter through the height h_u. **[R]**
   - Each lift step has a kernel-size budget Σ_ρ[Σ_i ph(ν) − (Σν)·log Ω].
   - The step's eigenvalue log λ_j is subtracted from that budget.
   - −μ(M_j) contributes pq_j·w·log Ω.
   - −a·log T comes from the final period map.

   Most of each budget cancels against the eigenvalue and against M_j's covolume. What remains is ph(a) − a·log Ω per step, m times over. *[I]*
5. `passage` gives two inequalities, where la = log|G| for a finite group G. **[R]**
   - μ(R_cols^∨) ≤ μ(R_base^∨) + 3de·(μ(R_base^∨) + HH0 + 28·la) + 28·la.
   - μ_max(R_cols) ≤ HH0 + 14·la.

   The two lattices are images, under the idempotents of two level structures of G, of one G-stable lattice. `passage_from_levels` proves the inequalities from multiplicities that are nearly constant. **[P]**
6. `DIVinN` is the premise of two statements. **[R]**
   - `Onto` is the base side's ON clause: it bounds the index of θ_j(T_j) in M_j at the twisted primes, and the weighted sum E1 of those indices.
   - `Fun0` states μ_max(R_base) ≤ x^CH·b − mean log κ.

## 1. The frame

**What B_u is.**
- `BuRational` gives `Bu u (jN φ) (jEE x) = embLL (Bk u φ x)` (`Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:364`). **[R]**
- `BuDef` gives `perCol u μ0 φ F = Bu u φ (iota μ0 F)` for F ∈ V0 (`…/LocalRingCardinality/DataRows.lean:226`). **[R]**
- `iota μ` composes the maps down the tower `Mult μ m ≅ Amb μ → … → Mult μ 0 ≅ EE` (:92–99, :184). **[R]**
- `RRset μ = iota(proj_Qsp(Mtilde μ ∩ V0 μ))` (:199). **[R]**
- `perCol` is the period of the composite of the m kernel operators (field `perCol_base_eq_PtilCol`, :169). **[R]**

**`BesselId`** (GTI) **[R]**:

    BuRational ∧ ∃ V : EE ≃ₗᵢ EE, ∀ u, ∃ a ≠ 0, ∃ U, ∀ φ F, Bu u φ F = a * besS u (U φ) (V F)

Here `besS u φ F = ⟪sEE F, s.Pu u (ι φ)⟫` (RhoDetPrime…:353). **[R]** It is clause 4 of `LinkDIV_at`, supplied as ⟨hBR, adm13⟩ by `linkDIV_at_words` (DV/RecBridge.lean:327). **[R]**

**What P_u is.**
- `D.s` is an abstract `SData` (`…/CuspSpanNormBounds/DataS.lean:13`). **[R]**
- `ConcK.hI : SIso D.s (sOf hF)` (FST/ThmSOwn.lean:387) identifies it with `sOf`, in which `Pu u := puC hF u = PoincareSetting.Pu` (FST/ParametersTermRelations.lean:238). **[R]**
- That map is the L² class of `poinc Dt (Ph X u hK T)`, a sum over a transversal of G(F) modulo `Srat` (`…/HaarTransversals/PoincareInHH.lean:149–208`). **[R]** `Srat` is the group of rational points of the stabilizer of the flag eX and the vector zu (`HidaSetting.lean:179`). **[R]**
- *[I]* That stabilizer is a Bessel subgroup, P_u is the adjoint of a Bessel period, and HH consists of forms on U(2r_S + k + 1) that are discrete series at infinity.
- Words index archimedean parameters: `letter : Word → Fin (k−2) → Bool` is injective, and the parameter of u is shifted by Δ wherever its letter is set (DataS.lean). **[R]**

**From `BesselId` to the frame matrices.**
- `exists_rowBasis` builds an orthonormal basis of HH whose first Drows vectors are `sEE(V(oE k))`. **[P]** So κ indexes EE and κ₁ = `Fin (Dall − Drows)` indexes the rest of HH. Since `D_eq` gives Drows = (1−delp)·Dall, δ = delp. **[R]**
- `block_eq` (TD:1245) and `blockReal_at_of` (TD:1283) show that, on the κ rows, `PMat f u · Vr0` equals Y'⁻¹·(matrix of Bk u at v)·Y_u. **[P]** Here `PMat` is the matrix of P_u, and `Vr0` is the isometric embedding of the ramified forms (`vr_gram`).
- `matK_at_of` (TD:1097) sets `Ball = PMat·Vr` and γ_u = c0_u⁻¹. **[P]**
- `kp_eq` (TD:1069) gives KpG(Bf, γ) = opMat(KD). **[P]**
- `KD = Kmat = (c0 u·c0 u')^(−1/2) • (Pu u)*∘Pu u'` and `c0 = volN·volH/dimPi` (`…/CuspSpanNormBounds/RelevantZeroGramTerms.lean:335–341, 509`). **[R]**

**`InputSG`** (`Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean`) **[R]**:

    (∀ i ≠ j, hsSq (KpG B ga i j) ≤ (1+η0)·|ι i|·|ι j|/Dstar) ∧ (∀ i, hsSq (KdG B ga i − 1) ≤ e0·|ι i|) ∧ |α| ≤ (1+η1)·Dstar

**Turning `InputSG` into Theorem F's hypotheses is linear algebra.** The proofs are `compressTraceSquareBound` (:591) and `compressDiagDefectBound` (:450) in `…/ChainSlopeWindows/TraceConjTransposeMulSelf.lean`. **[P]**
- `cor_common` gives tr Q² ≤ R²/D*·((1+η0) + (1+√e0)²·sg) and tr Q ≥ (1−√e0)·R, using R ≥ D*/sg.
- Compressing by the isometries Vr lowers every ‖K_uu'‖².
- It lowers tr Q by at most (de + √(de·e0))·R (:414).
- `num_main` and `num_ram` then give η = 5sg + 3√de, and the diagonal defect becomes 2e0.

**LinkS: what supplies `InputSG`.**
- `LinkS_at` (GTI) **[R]**: if C0⁻¹ ≤ duS·Γ²/D* ≤ C0, then
  - ‖KD u u'‖² ≤ (1+η0)·duS u·duS u'/D*;
  - ‖KD u u − 1‖² ≤ e0·duS u;
  - Dall ≤ (1+η1)·D*.
  - `LinkS` requires η0, η1 and √e0 all to be at most exp(−x^(ε/8)).
- The supplier is `link_alt_alt_bis` → `theoremS_transport_link_zero` (FST/LinkSPos.lean:131) → `theoremS_link_concrete` (:108). The last needs four clauses (FST/ThmSOwn.lean:37–47) and a point count. **[P]**
- **ClKppOff.** `KppOffC_holds` ← `schurNFC` (`…/RankPointCounts/SchurNFCOf.lean:34`) ← `schur_lemma_unitary_distinct_params`. **[P]** The statement reads: an intertwiner Vpi u' → Vpi u on the stabilizer at infinity vanishes when the parameters of u and u' differ at every τ. **[R]**
- **ClKppDiag.** `kernel_diagonal_positive` (FST/RowsPos.lean:202) ← `TypeP`, which the hyps-record slice traced to `UniqGap ∧ BesselOfW`. **[P]**
- **ClOff.**
  - `hsNormSq_off` (ThmSOwn:335) reduces it to ‖K0‖² and to `TheoremSSelected` (:669). **[P]**
  - `TheoremSSelected` is supplied by `CarrierGap.offDiag` (`Development/AbelianVarietyTheory/Proofs/FlagMeasures/OffK0Closed.lean:673`). Its inputs are `swxs_of_siegelWeil`, `rowNGP_of_siegelWeil`, `RowsFinDim` and `uniqGap_holds`. **[P]**
  - The bound has the shape of `PairBound` (`Formalism/HermitianCurvature/StatementPB.lean`): a main term from scalar pairs (`RowMain`) plus small loop and nongeneric terms. **[R]**
  - The identity part vanishes for u ≠ u' (`idZero_tO`, FST/RootLatticeThresholds/NuQPinExistsHolds.lean:58). **[R]**
- **ClDiag.** `diagonal_positive_final` (RowsPos:242) ← `RowNGP`, `RowMainEqP` (Siegel–Weil). **[P]**
- **Point count.** `CountAllPointsClass` and `adm10` give |Dall − D*| ≤ exp(−c·r·f·log r)·D*. **[R]**
- **Values.** `linkS_concl` (`…/StandingHypothesesHoldFamily.lean:186`) gives η0 = b^(−6), e0 = 2C0/Γ + 2exp(−k·f·log k) (`diag_unproj`, :144), and η1 = exp(−c7·r·f·log r). Each is at most exp(−x^(ε/8)) (`eF_nonneg_and_le_exp_neg`). **[P]**

**LinkIRR: what bounds δ = delp.**
- `LinkIRR` (GTI) is `DelpNonneg ∧ delp ≤ exp(−x^(ez/7))`. **[R]**
- The supplier is `closed_linkIRR_of_join_count` (`…/ThirdPlaceSeries/LinkIrr.lean:22`) → `linkIRR_of_allRows` (`Formalism/LocalToGlobal/GlobalTheory/ConcNP.lean:647`). **[P]**
- The proof bounds Dall − Drows by the number of rows whose label at g₀ or at g₁ is bad. It controls that number with `CountAllRows` (counts in cylinder sets) and `admLq` (Green's parametrisation). **[P]**
- *[I]* EE consists of the rows of HH whose local types at g₀ and g₁ are both good (`LabelCountGoodInjective`).

**Where the numbers come from.**
- `frameF_of` (TD:606) sets sg = x^(−CH) and proves (5x^(−CH) + 3√de + 4√eB)·x^CH ≤ 6. **[P]**
- `matRealF_of` (TD:750) sets de := E² and eB := 2E², with E = exp(−x^(ε/8)) ≤ x^(−CH)/2. **[P]**
- The true ramified share is at most 2f/b. This uses du = duS·(1 − 1/(T−1))^f and T ≥ b^(m/2) (`ramShare_at_of`, TD:894). **[P]**
- `frame_at_of` (TD:538) returns η = 5sg + 3√de and e = 2e0. **[P]**
- Σ_u d_u ≥ D*/sg follows from `ChCode_at` (#Words ≥ C0·Γ²·x^CH) and `ChProviso_at` via `word_count_bound_holds`. **[P]**
- `matSF_of` (TD:862) takes η1 from LinkS. `matKF_of` (TD:1348) takes η0 and e0 from LinkS's first two clauses. **[P]**
- *[I]* The budget x^(−CH) is far larger than the true defects. It is matched to HH ≤ x^CH·b (`LinkDIV_at` clause 2 with `Lat_at`), so F's error is O(b), which is below B0 = f·m·b·x^ε.

## 2. The glued lattice

**The abstract data** (IF/IndefSide.lean). **[R]**
- `DefSide` gives, for each type t: a K0-rational positive Hermitian form `HV t`; a lattice `Mt t`; a surjection `Pq t`; and the quotient metric `XQ t`. For each j and t it gives `HT`, `XT`, `Tl j t` and the pieces `Zp`.
- `IndefData` gives the types μ(w), the metric `XE`, the maps `ι t` and `θ j t`, the lattices `M j` with metrics `XW j`, and the scalars κ_v and λ_j(t,p,v).
- `RR := glueLat (fun w => matLat (ι (μ w)) (abelian₂ (μ w)))`, with `abelian₂ t = matLat (Pq t) (Mt t)` (:281, :68).

**The concrete instance on the path.** **[R]**
- `DefFam.side` (DV/RowLat.lean:250) fills the side:
  - `HV` is the Hermitian form on the good part of the forms, and `Mt` their integral lattice;
  - `Pq` is the orthogonal projection onto the block Z;
  - `Tl` is the image of a lift block's level lattice.
- `CxData` (IR/PartsOrth.lean:55) supplies the maps:
  - `Θ t : FC t → EE`;
  - `θ' j t : FLC j t → W j`;
  - the bases `bW` and the lattices `M b j`.
- In `CxData`, `Z t` is the preimage of range Θ_t*.
- `data` sets D = dQ μ0, `ι := rowMat`, `θ := liftMat` and `XW := Gram(bW)`. It defines `XE := rowXE(frameOf gramE, κ, λ)`, where gramE is the Gram matrix of the Θ-images, divided by nP.
- `pkg_of_rowsK_alt` fixes `eJ : J ≃ Fin D.R.m`.

**The determinant identity.**
- `specDet_rect` (IF/IndefUse.lean) concludes `detRatio XQ XE ι v = s^D * ∏ j, detRatio (XT j) (XW j) (θ j) v` from three hypotheses. **[P]**
  - ι scales by s·∏_j λ_j on each piece.
  - θ_j scales by λ_j on each piece.
  - Corresponding pieces have equal rank.
- `IndefRows.detId` supplies these three hypotheses from `l1c` and `part_dim`. **[P]**
- The scaling property has two sources. **[P]**
  - At v0, `H4` gives ⟪Θx, Θy⟫ = nP·κ·∏_j λ_j·⟪x, y⟫_XQ on piece p (`scal_rowsR`, IR/CxCoreRG.lean:60), and `ThmA` does the same for the lifts.
  - At v ≠ v0, it holds because `rowXE` is defined to make it hold (`rowXE_part`, IR/CxLemmas.lean:280); for the lifts it comes from `GalD`.
- `CxCore` carries two fields (IR/CutTuples2.lean). **[R]**
  - `ThmBop` (:99): ΘΘ* = κ∏λ on `EEp p ⊓ EEl b`.
  - `ThmAop` (:128): θ'θ'* = λ on each piece of W_j.
- *[I]* This is the shape of `BForm`: an iterated inner-product formula.

**The DIV clause** (`divClausesR_of`, DV/ConstantGeTwentyEight.lean:184) runs in four steps. **[P]**
1. `P.base.boundsMu` gives μ(R_base^∨) ≤ mean log κ + Σ_j l3_j + 2Fo + LG + Σ_j(E1_j + E2_j) + E3.
2. `passage` moves the bound from base to cols.
3. `L3main` bounds Σ_j l3_j ≤ Σ_j Σ_ρ pq_j·w_jρ·logOm + El3.
4. `R.divIneq` closes `muCC − meanLog κ + R.hu − 2Fo ≤ R.rhs`.

The height clause comes from `height_chain_atR` (:123). It gives log‖B u‖_v² ≤ hP + Σ_j hK_j − log κ_v − min_p Σ_j log λ_j, using `ch.fact`: `Pt = PtL ∘ K_mm ∘ ⋯ ∘ K_1`. **[P]**

**Where m·ph(a) and Ω^a come from.** The record `RecNums` (DV/Inputs.lean:18) fixes the following numbers. **[R]**
- hu = hA + Σ_j(hB_j − hX_j), with:
  - hA = −Σ_t a_t·logT + …;
  - hB_j = Σ_ρ(Σ_i ph(ν_jρi) − (Σ_i ν_jρi)·logOm) + …;
  - hX_j = Σ_ρ logH_jρ − ….
- ph(u) = u·log u − u (`Formalism/LogFactorialIndices/StatementSize.lean:7`).
- `rhs = Σ_{t∈TT}(m·(ph a_t − a_t·logOm) − a_t·logT) + errors`.
- `weight_height_sum_le`: Σ_i ph(ν) − logH ≤ ph(a_ρ)·[ρ∈TT] + eE.
- `weight_sum_eq`: Σ_i ν = a_ρ·[ρ∈TT] + k·w + δ.
- |pq_j − k| ≤ m.

The kernel-size budget `HtNums.sz` is `liftedMapLogSize` (`Formalism/ThetaSupremumBounds/DivIneqExplicit6.lean:15`); its leading term is Σ_τ(Σ_i ph(ν) − Σν·logOmτ). **[R]** The statement `LiftStepDi6` in the same file derives such a budget from two hypotheses. **[R]**
- A theta kernel satisfies ‖Th(u)‖ ≤ S·exp(nsq(u)/2).
- The coordinates are scaled by λ with |λ|² = Ω⁻¹.

My reading of the mechanism. *[I]*
- A Cauchy estimate bounds the coefficient of a monomial of degree ν by about exp(Σ ph(ν)), which is about log ν! by Stirling.
- The scaling costs Ω^(−ν).
- For each step j: the step's eigenvalue absorbs everything except ph(a_t), and M_j's covolume cancels the k·w·logΩ part. The m steps together leave m·(ph(a_t) − a_t·logΩ).
- −a_t·logT comes from the final period map (`t1`, `t5`).

**`passage`** (IF/IndefSide.lean:339) **[R]**:

    0 ≤ N.de → N.de ≤ 1/3 → ∀ HH0, S.muMaxRR ≤ HH0 →
      S'.muMaxRR ≤ HH0 + 14·N.la ∧ S'.muCC ≤ S.muCC + 3·N.de·(S.muCC + HH0 + 28·N.la) + 28·N.la

- The supplier is `passage3_of` (IR/NearConstantMultiplicities.lean:50) → `passage_of_steps` (IR/CutPassage3SOfSteps.lean:49) → `passage_from_levels` (`Formalism/LocalToGlobal/GlobalTheory/DivPassageP.lean:163`). **[P]**
- `LevelAmb` (`…/DivPassage.lean:16`) holds the data. **[R]**
  - There is one lattice `Rg` and two idempotents, given by the operators e_{P,ψ} for (P0, ψ0) and (P1, ψ1) (`epM_eq`).
  - rk(base) = Σ_s rk R_s and rk(sharp) = Σ_s n_s·rk R_s.
  - (1−de)·n̄ ≤ n_s ≤ (1+de)·n̄.
  - log|G| ≤ la.
- The inputs are `NearConstantMultiplicities` for (P1, ψ1) and `M1` for (P0, ψ0). **[R]**
- `passage_sizes` takes de = 8fr/g. **[R]**
- `PassageAtBaseSharpLevels` names the two levels `P0 Pg r ψ` and `Psharp Pg r k ψ`. **[R]**
- *[I]* G is a product of GL_r over the residue fields at the special primes. M1 says the base model occurs with multiplicity one.

**DIVinN.**
- Statement (GTI) **[R]**: etaSum ≤ D0·C·x^ε·(B0 + Nc), where etaSum = Σ over twisted w of lwP·e_w·etaJ. `LinkN` bounds etaSum by Σ_l log l·Σ_e shaLen. **[R]**
- It is the premise of three statements. **[R]**
  - `Onto`/`OntoX`, which conclude `(p.S false).ON` (`Development/AbelianVarietyTheory/Definitions/Divisors/TupleReadBaseTupleEqFamily.lean:528`; `…/SingleIndexPlacesAreTwisted.lean:167`).
  - `Fun0`, which concludes `FUN` (:536).
  - `DivisionKernelConstantBounds.pkg`/`.hh` (`…/ThirdPlaceSeries/DIVRecBridgeSel.lean`).
- `ON` (IF/IndefSide.lean:318) has two parts. **[R]**
  - At each twisted w, Σ_j(Iw + Iw̄) ≤ (Σ_j(2·ramw·F0 + ramw·err0) + ramw·2/plc²)·D, where Iw = idx_w(M_j, θ_j T_j).
  - Σ_w lw·ramw·(err0 + J0) ≤ E1.
- `IndefSide.boundsMu` feeds both parts into `BoundsMu`. **[P]**
- `FUN` (IF/IndefSide.lean:331) states μ_max(R) ≤ hh − mean log κ with hh = x^CH·b; it is the HH0 that `passage` uses. **[R]**

## Chains

- `frameF_of` (TD:606) ← `frameRealF_of''` (TD:988) ← `matSF_of` (TD:862), `matRealF_of` (TD:750), `matKF_of` (TD:1348) ← `matK_at_of` (TD:1097) ← `blockReal_at_of` (TD:1283) ← `BesselId`.
- `frame_at_of` (TD:538) → `joint_a_ramified_holds` → `ramification_condition_holds` → `ramification_linear_case_holds` → `flat_lattice_theorem_holds` → `theoremF` (`…/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean`).
- `link_alt_alt_bis` (`…/ThirdPlaceSeries/LinkAltAltBis.lean:16`) → `theoremS_transport_link_zero` (FST/LinkSPos.lean:131) → `theoremS_link_concrete` (:108) → `theoremS_link_of_evaluation` (:97) → `linkS_of_standing_hypotheses` (`…/StandingHypothesesHoldFamily.lean:628`) → `linkS_concl` (:186).
- `closed_linkIRR_of_join_count` (LinkIrr.lean:22) → `linkIRR_of_join_ex` → `linkIRR_of_allRows` (ConcNP.lean:647).
- `divClausesR_of` (DV/ConstantGeTwentyEight.lean:184) ← `IndefSide.boundsMu`, which uses `specDet_rect` and `detId`, which in turn use `scal_rowsR` and `scal_liftsR`.
- `passage3_of` → `passage_from_levels`.

## Not read

- The inputs of Theorem S: `CarrierP`, `FormulaC` and the mass data in `theoremS_leaves_of_carrierG`; the `PairBound` instance; `rowMainEqP_of_siegelWeil`; `rowNGP_of_siegelWeil`; and the step from `UniqGap` to `TypeP`.
- `idCellOffC_holds_of_vol` and `KExpansionC`, which is the unfolding itself.
- The definitions of `HHX` and `Ph`. That HH is exactly a space of discrete-series forms cut out by an idempotent remains *[I]*.
- The numerics of `delp_of_allRows`.
- Where `ThmBop` and `ThmAop` are proved, and `links_of_prims`.
- What M_j is concretely, `Covol`, and `l3main_ofNum`.
- Who supplies `nKcb`, and whether `LiftStepDi6` is the instance used.
- The proofs of `Onto` and `Fun0` from DIVinN.
- `passageLat_of`, `levelCompare_statement`, and the supplier of `NearConstantMultiplicities`.
- `divIneqRecord`.
