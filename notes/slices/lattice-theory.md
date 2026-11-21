# The two lattice theorems: Theorem F and `BoundsMu`

Read 2026-11-20 from source text only; nothing was built. Paths are relative to `lean/src/`. Abbreviations: HNP = `Formalism/HarderNarasimhan/HarderNarasimhanProofs/`, QMD = `Formalism/QuotientMetricDivisors/`, GSB = `Formalism/SharpRestriction/GlobalSchurBounds/`, CSW = `Formalism/SizeWindowBrackets/ChainSlopeWindows/`. Tags: **[read]** transcribed from source; **[proved-by]** I read the proof body and name what does the work; *[inferred]* my interpretation.

## 0. Direct answers

1. `theoremF := frame_theorem_log_ideal` is `TheoremFSharp` plus one line: `theoremF_of_sharp` (HNP/TheoremFSharp.lean:390) subtracts `log|I| ≥ 0`. **[proved-by]** No step of the argument produces the log|I| term; it is pure slack. **[proved-by]** The path nevertheless uses the weaker form: `joint_a_ramified_holds` takes `.1` of a pair whose `.2` is the sharp form. **[read]**
2. The proof of F (HNP/TheoremFSharp.lean:168–386) runs as follows. **[proved-by]**
   - At every level τ ∈ [0, HH], cut each source at its Harder–Narasimhan step for slope s − τ + h_i.
   - A Markov bound shows these steps miss at most a share u/(u+τ) of the sources' total rank.
   - The μ_min slope inequality puts their images inside the target's HN step for slope s − τ.
   - A near-tight-frame lemma (`FrameLA1`) shows those images span all but a share w(τ) of the target.
   - Integrating over τ (layer cake) bounds the target's mean slope.
3. Origin of each error term **[proved-by]**:
   - 4u·log(1+HH/u) = ∫₀^HH 4u/(u+τ)dτ;
   - (η+4√e)·HH = ∫₀^HH (η+4√e)dτ;
   - (1−δ)⁻¹ comes from passing from the enlarged frame space ℂ^(κ⊔κ₁) to the target's κ coordinates;
   - log|I| comes from no step.
4. `DegSupermodZ` is used only to build the HN step. **[proved-by]** `dualPl` is not used in the proof of F at all. **[proved-by]** It enters F's application (μ_min(cc) = −μ_max(RR)) and the proof of `BoundsMu` (μ(R^∨) = lcv(R)/D). **[proved-by]**
5. `BoundsMu` bounds μ(R^∨) above by mean log κ − Σ_j μ(M_j) plus local error terms. **[read]** Its core, `StepBW`, is an exact covolume calculation. Its only inequality is a Cauchy–Schwarz step for a quotient metric (`LemmaRb`). **[proved-by]** The many error parameters are bookkeeping. **[proved-by]**
6. `BoundsMu` has one instantiation, `IndefSide.boundsMu`, and every caller, `divClausesR_of` included, goes through it. **[read]** That instantiation sets ρ ≡ 1 and discards the second conjunct. **[read]** It applies `BoundsMu` to the "base" side's lattice. A separate `passage` field then transfers the bound to the lattice whose dual is F's target. **[read]**

## 1. Theorem F

**Statement.** `TheoremF` (StatementFrameF.lean:26) and `TheoremFSharp` (:64) have identical hypotheses (third reading §10). **[read]** Their conclusions are

    s - log |I| - (1-δ)⁻¹ * (4u·log(1 + HH/u) + (η + 4√e)·HH) ≤ muDef b' X' cc        -- F
    s           - (1-δ)⁻¹ * (4u·log(1 + HH/u) + (η + 4√e)·HH) ≤ muDef b' X' cc        -- FSharp

**[read]** The definitions used:
- `muDef` (StatementPl.lean:64) is 2·slope of the ℤ-realisation − log 2 + log|d_K|/[K:ℚ]. **[read]**
- `htMap` (:60) is the mean over infinite places of log‖φ‖_v². **[read]**
- `hnStep ρ L θ` (Statement.lean:36) is the sup of the nonzero sublattices N ≤ L with θ ≤ μ_min(N). **[read]**
- `slopeList` (:39) lists the HN slopes. **[read]**

**Proof sketch** (`theoremFSharp_of`, HNP/TheoremFSharp.lean:168):

1. *HN filtration.* `hnStep_of` (HNP/HNStep.lean:18) proves three properties of hnStep(L, θ): it is saturated, it has μ_min ≥ θ, and it contains every sublattice with μ_min ≥ θ. **[proved-by]** The engine is supermodularity of g(N) = deg N − θ·rk N. **[proved-by]** That comes from `degree_supermodular_integral` (HNP/DegSupermodZ.lean:153): covol(A∩B)·covol(A+B) ≤ covol(A)·covol(B), proved through saturations and an orthogonal projection, which is a contraction. **[proved-by]** HNSlopes gives #{j : θ ≤ slope_j} = rk hnStep(L, θ) and Σ slope_j = deg L. **[read]** HNExtreme puts every slope in [μ_min, μ_max]. **[read]**
2. *Corank share (Markov).* Let x_ij be the normalised HN slopes of N_i minus h_i. **[proved-by]** Their rank-weighted mean is ≥ s, and each is ≤ s + u (by hypothesis and HNExtreme). **[proved-by]** `frameB_share` (HNP/FrameHermSharpB.lean:25) concludes #{x_ij < s − τ} ≤ (Σ m_i)·u/(u+τ). **[proved-by]** Combined with `frameB_count_lt`, this becomes `hcor`. **[proved-by]** It states that the steps Nt(τ,i) = hnStep(N_i, level s−τ+h_i) satisfy Σ_i(rk N_i − rk Nt) ≤ (u/(u+τ))·Σ_i rk N_i. **[proved-by]**
3. *Slope inequality.* The proof uses part 1 of `slope_inequality_mean`, `muMinDef A − htMap φ ≤ muMinDef (φ A)` (statement StatementPl.lean:148, proof HNP/SlopeIneqMean.lean:117). **[proved-by]** It does not use the μ_max/injective form. **[proved-by]**
   - The lemma's proof rescales the target metric at each place by c_v with mean log c_v = 0 (`Twist`). The operator norm then equals exp(htMap/2) at every place. **[proved-by]**
   - It then applies the Euclidean slope inequality, proved by comparing Gram determinants (`rank_range_eq_and_degree_le`, HNP/SlopeIneq.lean:85). **[proved-by]**
   - So each B_i(Nt) has μ_min ≥ s − τ. **[proved-by]** By maximality it lies in the target step St(τ) = hnStep(cc, level s−τ), and so does M(τ) := Σ_i B_i(Nt) (`hMle`). **[proved-by]**
4. *Robust spanning at v.* `thmF_place` (:35) works at the complex place v. **[proved-by]**
   - The span of Nt at v has complex dimension rk_K Nt. **[proved-by]**
   - `FrameLA1` applied to `Ball` bounds the orthocomplement of the images' span in ℂ^(κ⊔κ₁) by (η+4ε+4√e)·|κ⊔κ₁|. **[proved-by]**
   - Projecting to the κ rows loses at most |κ₁|. **[proved-by]**
   - `hplace` concludes |κ| − rk_K M(τ) ≤ w(τ)·|κ|, with w(τ) = (1−δ)⁻¹(η + 4u/(u+τ) + 4√e). **[proved-by]**
5. *Target count.* Since rk St(τ) ≥ rk M(τ), #{slopes of cc < s − τ} ≤ w(τ)·rk cc (`hcnt`). **[proved-by]** Every slope of cc is ≥ s − HH (`hlow`), because HH ≥ s − μ_min(cc). **[proved-by]**
6. *Layer cake* (`layer_cake_formula`, `Formalism/CorankShare/CorankShareProofs/LayerCakeFormula.lean:57`).
   - The lemma: if x_j ≥ a − HH and #{x_j < a − τ} ≤ w(τ)·D on [0, HH], then the mean of the x_j is ≥ a − ∫₀^HH min(1, w). **[read]**
   - Take a = s; the mean of the target's slopes is μ(cc). **[proved-by]**
   - `frameB_integral` computes ∫w = (1−δ)⁻¹(4u·log(1+HH/u) + (η+4√e)·HH). The proof drops the truncation min(1, ·). **[proved-by]**

**FrameLA1** (StatementFrameF.lean:11). **[read]**

    Σ_i ‖c_i·B_i*B_i − 1‖²_HS ≤ e·Σ_i dim V_i,  e ≤ 1/4,  tr Q² ≤ (1+η)(tr Q)²/dim H  (Q = Σ c_i B_iB_i*),
    Σ_i codim N_i ≤ ε·Σ_i dim V_i   ⟹   dim (Σ_i B_i N_i)^⊥ ≤ (η + 4ε + 4√e)·dim H

The proof (`frame_linear_algebra_first`, HNP/FrameLinearAlgebraFirst.lean:77) takes an orthonormal basis g_l of W = (ΣB_iN_i)^⊥ and bounds t_W = Σ_l⟨g_l, Q g_l⟩ from both sides. **[proved-by]**
- *From above.* B_i* g_l lies in N_i^⊥, so t_W ≤ εR + R√(εe), with R = Σ dim V_i. **[proved-by]**
- *From below.* Q is nearly scalar, ‖Q − (tr Q/dim H)·1‖²_HS ≤ η(tr Q)²/dim H, and tr Q ≥ R(1 − √e). **[proved-by]**

The conclusion is about dimensions only. *[inferred]*

**CorankShare** (`Formalism/CorankShare/StatementFR.lean:24`) is the one-family Markov bound. **[read]** As a Prop it is never proved or used; its content is proved inline as `frameB_share`. **[read]** The variants `FrameLA` (2η), `FrameLast`, `FrameHerm` and `FrameHermSharp` (constants 2η and u(1+4log)) have no consumer. **[read]**

**What is new compared with Bost.** *[inferred]*
- Three inputs are classical: the HN filtration of Hermitian 𝒪_K-lattices, the μ_min slope inequality and supermodularity.
- Bost's slope method bounds the degree of one filtered source from above, using μ_max of the targets plus heights.
- Here many sources map into one target, and the target's whole HN polygon is controlled level by level.
- The new steps are 2, 4 and 6: a Markov bound on the sources' low-slope rank, a robust-spanning lemma from a near-tight frame at one place, and integration over levels.

**Unusual hypotheses.**
- *The frame sits on a lift.* `Ball i` must equal Y'⁻¹·(matrix of B_i at v)·Y_i only on the κ rows. **[read]** Y_i and Y' are arbitrary invertible matrices, unrelated to the metrics X. **[read]** The κ₁ rows are free. **[read]** This is not a loophole, because the frame enters only dimension counts. *[inferred]*
- *Degeneracy.* Suppose the B_i vanish on the κ rows. With N_i = V_i and ε = 0, the projected span is 0, so the hypotheses force η + 4√e ≥ 1 − δ. *[inferred]* Then w ≥ 1, and the conclusion is no better than s − HH. *[inferred]*
- *When the theorem has content.* The bound μ(cc) ≥ μ_min(cc) ≥ s − HH already follows from the hypothesis HH ≥ s − μ_min(cc). **[proved-by]** So F says something only when its error term is below HH. **[proved-by]**
- *Heights.* The height bound is required only for nonzero B_i. **[read]**

**Call site and instantiation.** The chain is `frameF_of` (GSB/TopDensityNGeSixteen.lean:606) → `frame_at_of` (:538) → `joint_a_ramified_holds` (CSW/JointDModelAppliesUnitLattice.lean:254) = `(ramification_condition_holds …).1` (:215) → `flat_lattice_theorem_holds` (:187) → `theoremF`. **[read]** The abstract data are filled as follows. **[read]**
- Target and field: K = LL; cc = `RR.dualL` with the dual basis and dual frame.
- Sources and maps: I = `Word`; N_u = `Nu u`; B_u = `Bk u`; h_u = `div.h u`.
- s = `sFrame` is exactly the rank-weighted mean. u = `uFrame` = max_u(μ_max(N_u) − h_u) − s (`LocalRingCardinality/DataArith.lean:131,134`). Both choices are extremal.
- Frame constants: δ = `delp`; e = 2·e0; η = 5·sg + 3√de, with sg = x^(−CH).
- Frame data: κ₁, v, Y, Y', `Ball` and γ are existential in `FrameReal_at` (GSB/TopDensityNGeSixteen.lean:519), with `Ball u = Bf u · Vr u`.
  - Vr is an isometric embedding of the ramified subspace into the full space of dimension `duS u`.
  - `InputSG` on Bf: ‖K_uu'‖²_HS ≤ (1+η0)·d_u·d_u'/D*, ‖K_uu − 1‖²_HS ≤ e0·d_u, dim ≤ (1+η1)·D*; also Σ d_u ≥ D*/sg.
  - `CorBounds` and `CompressTraceSquareBound` (`Formalism/SizeWindowBrackets/TraceSquareAndDiagBounds.lean:64,109`) convert these into F's frame hypotheses.
- HH: any HH > 0 with HH ≥ s − μ_min(cc) (`Frame_at`, GSB/QuadraticLogDerivCongr.lean:188). The identity μ_min(cc) = −μ_max(RR) used there comes from `dualPl` (`lat_at`, :1323).

The log|Word| slack is carried into the record's `SlopeIneq` (`Formalism/RankGapBounds/MeanBoundSecondForm.lean:151`). **[read]**

## 2. `BoundsMu`

**Statement in words** (`Formalism/DivisorInequality/StatementObj.lean:17`). **[read]**
- *Field.* K is totally complex, K0 is a CM subfield, and v0 is an infinite place at which `star` is complex conjugation.
- *Lattice.* R ⊂ K^D is a lattice with metric `XE` at each infinite place.
- *Local types.* `μ : primes → Tup` is conjugation-invariant and equals μ0 outside a finite set. At every prime y, R_y = ι(μ(y))·`abelian₂`(μ(y)) (line 50). The `abelian₂ t` are lattices with metrics `XQ t`.
- *Base type.* `abelian₂ μ0` = P(Mt), carrying the quotient metric of a positive definite Hermitian H with entries in K0: (XQ⁻¹)ᴴXQ⁻¹ = (P·H⁻¹·Pᴴ)⁻¹ (`IsQuotMetric`, QMD/Statement.lean:63; line 46).
- *Auxiliary data.*
  - There are J auxiliary lattices M_j ⊂ K^D with metrics `XW j`.
  - For each type t there are local lattices `Tl j t` with Hermitian forms `HT j t`. For t = μ0 these are K0-rational, with metric `XT j μ0` at every place; for other t they are Hermitian at v0 only.
  - There are maps θ_j(t), and Gram elements `Gm t y` ∈ K. The v0-image of `Gm t y` is the Gram determinant of a local basis of `abelian₂ t` at y.
- *Determinant factorisation* (line 37). Here `detRatio XS XT φ v` = det Gram_XT(φe)/det Gram_XS(e) is the volume distortion of φ at v (QMD/Statement.lean:42).

      ∀ v,  detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v
      ∀ t,  detRatio (XQ t) XE (ι t) v0 = (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0

  Here ρ(t) is a unit at every prime, and ρ(μ0) = 1.
- *Local error bounds* on finite sets Tw ⊆ Sy:
  - outside Sy, all local terms vanish;
  - on Sy∖Tw, the index terms vanish;
  - on Sy, v_y(Gm) ≤ D·g_y, with Σ lw·g ≤ LG;
  - on Tw, Σ_j(idx_y + idx_ȳ) ≤ (Σ_j(2F + err) + 2/ell²)·D and jw ≤ J·D + η;
  - the weighted sums are bounded by E1, E2 and E3.
- *Conclusion* (lines 72–75), where lw y = log N(y)/[K:ℚ]:

      μ(R^∨) ≤ meanLog κ + Σ_j lcv(XW j, M j)/D + 2·Σ_j Σ_{y∈Tw} lw y·F y j + LG + Σ_j (E1 j + E2 j) + E3
      ∧  ∀ j, lcv(XW j, M j)/D = −μ(M j)

  The second conjunct holds by definition.

In words *[inferred]*: the slope of R's dual is at most the mean log of κ, minus the slopes of the J auxiliary lattices, plus local corrections at finitely many primes.

**Proof strategy** (`slope_bounds`, `Formalism/DivisorInequality/DivisorInequalityProofs/BaseLevelBoundsWithCovolumeHolds.lean:47`):

1. `untwisted_choice` extends the error data by zero off Tw. **[proved-by]** The proof then runs `divisor_bounds_chain_weak` (QMD/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean:518) → `second_step_refined_weak` (:506) → `weak_form_b` = `stepBW_of` (:324). **[proved-by]**
2. `stepBW_of` proves `StepBW` (QMD/RatHermLcvTwist.lean:60) **[read]**:

       lcv XE R ≤ D·meanLog κ + Σ_j lcv(XW j, M j)
                  + Σᶠ_w lw w·( v_w(G_{μ(w)}) + Σ_j (idx_w(M_j, θ_j T_j) + idx_w̄(M_j, θ_j T_j) + jw(HT_j, w, T_j)) )

   Here T_j = T_j(μ(w)) and θ_j = θ_j(μ(w)). The proof is a chain of equalities plus one inequality. **[proved-by]**
   - (a) `IdxLcv` and `ImageLcv` (QMD/ProdFormula.lean:62,54) give lcv(R) = lcv(XQ, Λ_μ0) + (2/[K:ℚ])·Σ_v log detRatio(ι μ0) + Σ_w lw·(idx_w + idx_w̄). **[proved-by]**
   - (b) The factorisation at every v turns Σ_v log detRatio(ι μ0) into D·Σ_v log κ_v + Σ_j Σ_v log detRatio(θ_j μ0) (`hlogsum`). **[proved-by]**
   - (c) For each j, `hθj` turns the θ_j term into lcv(XW_j, M_j) plus index and jw terms, using ImageLcv, IdxLcv and **RatHermLcv**. **[proved-by]** RatHermLcv (ProdFormula.lean:69) says lcv(XT, T) = −Σ_w lw·jw(H, w, T) for a K0-rational Hermitian lattice. **[read]** Here jw(H, w, T) = −v_w(Gram determinant of a local basis). **[read]**
   - (d) **LemmaRb** (QMD/Statement.lean:120, proved at QMD/HermitianTwistDivisors/ReductionLemmaSecond.lean:163) gives lcv(XQ μ0, P·Mt) ≤ Σ_w lw·v_w(G_μ0(w)). **[proved-by]** Its proof applies the product formula to det(P·H⁻¹·Pᴴ)⁻¹. **[proved-by]** It also applies the determinant Cauchy–Schwarz inequality `DetCS`, pairing each place with its conjugate-twisted place. **[proved-by]** This is the only inequality in `StepBW`. **[proved-by]**
   - (e) `local_idW` (:174) proves an equality at each prime w: idx_w(ι_μ0 Λ_μ0, R) + idx_w̄ = v_w(G_μ(w)) − v_w(G_μ0) + Σ_j(Δidx + Δidx̄ + Δjw). **[proved-by]** The proof writes both Gram determinants at v0 and inserts the v0 factorisations for μ0 and μ(w). **[proved-by]** Because v0 is injective, the resulting archimedean identity becomes an identity in K. Taking its w-adic valuation gives the equality, and this step needs ρ to be a unit. **[proved-by]**
3. `divisor_bounds_sum` (QMD/HermitianTwistDivisors/BoundsSum.lean:10) divides by D and inserts the error hypotheses. **[proved-by]** `dual_lattice_measure` (QMD/HermitianTwistDivisors/DualMu.lean:14) converts lcv(R)/D into μ(R^∨) via `dual_polygon_identity`. **[proved-by]**

**Where things enter.**
- *Product formula* (`ProdFormula`, QMD/ProdFormula.lean:11: (2/[K:ℚ])Σ_v log‖v(a)‖ = Σ_w lw·v_w(a)). It enters in steps (c) and (d), converting archimedean Gram determinants of K-rational forms into finite valuations. **[proved-by]**
- *Determinant factorisation.* It enters in steps (b) and (e). **[proved-by]** Together these say covol(R) ≈ κ^D·∏_j covol(M_j), up to local factors. *[inferred]*
- *Lattice of periods.* That role is played by R^∨, the functionals integral on R. *[inferred]*
  - On the path, R = `IndefData.RR` = `glueLat (w ↦ ι(μ w)·Pq(Mt))` (`Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean:281`). **[read]**
  - The lattices slice identifies its generators as images of integral test vectors, ι_μ(proj(M̃ ∩ V0)). *[inferred]*
  - Clause 1 of `DivClausesR` (`Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean:111`) puts the periods of the shifted forms into `dualLat RR`. **[read]**

**Unusual or degenerate.**
- ρt and ρr: `IndefSide.boundsMu` (`Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean:271`) sets both to the constant 1, so this generality is unused. **[read]**
- The parameters gy, LG, F, err, J, η, E1–E3, ell, Sy and Tw can always be chosen to hold, for instance by setting gy to the actual term. *[inferred]* The content is `StepBW`. *[inferred]*
- The second conjunct holds by definition (`log_covolume_slope_mu`), and the caller takes only `.1`. **[read]**
- K0-rationality is required only for type μ0; other types need data at v0 alone. **[read]** This matches step (e), which uses v0 only. **[proved-by]**
- `BaseLevelBoundsWithCovolume`, `BoundsMuOn` and `DivIneqObj` (StatementObj.lean:77,170,239) are never proved or used. **[read]**

**Call site and instantiation.** `divClausesR_of` (`Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean:184`) calls `P.base.boundsMu boundsMu specDet …` (:211), which is `IndefSide.boundsMu`. **[read]** The arguments are filled as follows. **[read]**
- Gm t y = `gramR (quotGram (Pq t) (HV t)) (eb t y)`; `abelian₂ t = matLat (Pq t) (Mt t)`.
- `elly = ellw`; Fy = ramw·F0; erry = ramw·err0; Jy = ramw·J0(μ y); d_j = D (`dW_eq`).
- The two factorisations come from `IndefRows.detId` (IndefUse.lean:196), via `SpecDet` applied to `RowLatticeBoundForBasis` (IndefSide.lean:304). On each piece p, ι(t) multiplies the metric by κ_v·∏_j λ_j(t,p,v), and θ_j(t) multiplies it by λ_j(t,p,v).

*[inferred]* This is the iterated inner-product identity: the composite of the lifts with its adjoint is κ times a product of eigenvalues (third reading §9, `BForm`).

The caller then finishes in three steps. **[read]**
- `L3` gives lcv(XW_j, M_j)/D ≤ l3_j.
- `L3main` gives Σ l3_j ≤ Σ_j Σ_ρ pq_j·w_jρ·logOm + El3. So −μ(M_j) carries the CM-period term. *[inferred]*
- `P.extra.passage` moves the bound from `P.base` to `P.cols`, at a cost of 3·de·(μ + HH0 + 28·la) + 28·la.

Clause 3 of DIV reads `muCC − meanLog κ + R.hu − 2·FoOfR ≤ R.rhs`, and `tH` sets R.hu − meanLog κ = h_u. **[read]** The clause is therefore μ(CC) + h_u − 2·Fo ≤ rhs. **[read]** The mean log κ of `BoundsMu` cancels against the κ inside the height h_u. *[inferred]*

## 3. Could they be stated more simply? *[inferred]*

Both could, without losing what the application uses.

**For F:**
- State the sharp form, μ(cc) ≥ s − ∫₀^HH min(1, w(τ))dτ.
- Take as the hypothesis the property the frame is used for, robust spanning: images of subspaces of codimension share ε span all but (η + 4ε + 4√e)·dim. Keep `FrameLA1` as a separate lemma about near-tight frames.
- Fold Y, Y' and κ₁ into the phrase "after a change of coordinates at v, inside a space of dimension ≤ dim/(1−δ)".

The application needs only small η, e and δ. It can afford the log|Word| slack.

**For `BoundsMu`:**
- The one-page form is `StepBW` read as an Arakelov-degree identity: deg R/D ≥ Σ_j μ(M_j) − mean log κ − (1/D)·Σ_w lw·(local discrepancies). The "≥" comes only from the quotient metric.
- Drop ρ, the second conjunct, and the scaffolding Sy/Tw/g/F/err/J/η/E/ell.
- Keep the two features the application does need: types varying at finitely many primes, and factorisation at v0 only for twisted types.

## Chains

- F: `theoremF` (HarderNarasimhan/ShiftInvariance.lean:61) = `frame_theorem_log_ideal` (HNP/TheoremFSharp.lean:400) ← `theoremF_of_sharp` (:390) ← `frame_theorem_sharp` (:388) ← `theoremFSharp_of` (:168).
  - `thmF_share` (:11) ← `frameB_share` (HNP/FrameHermSharpB.lean:25).
  - `thmF_place` (:35) ← `frame_linear_algebra_first` (HNP/FrameLinearAlgebraFirst.lean:77).
  - `slope_inequality_mean` (HNP/SlopeIneqMean.lean:249) ← `slope_inequality_general` (HNP/SlopeIneq.lean:507).
  - `frameB_hnStep` (FrameHermSharpB.lean:77) ← `hnStep_of` (HNP/HNStep.lean:18) ← `degree_supermodular_integral` (HNP/DegSupermodZ.lean:153).
  - `polygon_extreme_slopes` (HNP/HNExtreme.lean:114), `layer_cake_formula` (`Formalism/CorankShare/CorankShareProofs/LayerCakeFormula.lean:57`), `frameB_integral` (FrameHermSharpB.lean:126).
- F's application: `frameF_of` (GSB/TopDensityNGeSixteen.lean:606) → `frame_at_of` (:538) → `joint_a_ramified_holds` (CSW/JointDModelAppliesUnitLattice.lean:254) → `ramification_condition_holds` (:215) → `flat_lattice_theorem_holds` (:187).
- BoundsMu: `boundsMu` (`Formalism/DivisorInequality/BaseLevelBoundsWithCovolume.lean:7`) = `slope_bounds` (…Holds.lean:47) ← `divisor_bounds_chain_weak` (ConjugateWeightLatticeOfGeneral.lean:518) ← `stepBW_of` (:324).
  - `stepBW_of` uses `local_idW` (:174), `lemmaRb_of` (ReductionLemmaSecond.lean:163), `ratHermLcv_of` (QMD/HermitianTwistDivisors/RatHerm.lean:258), and `imageLcv_of`/`idxLcv_of` (QMD/HermitianTwistDivisors/ImageLcv.lean:140,194).
  - `slope_bounds` also uses `divisor_bounds_sum` (BoundsSum.lean:10) and `dual_lattice_measure` (DualMu.lean:14).
- BoundsMu's caller: `wordFacts_of_face` (`Formalism/LocalToGlobal/Divisibility/RecBridge.lean:204`) consumes `DivClausesR` ← `divClausesR_of` (ConstantGeTwentyEight.lean:184) ← `IndefSide.boundsMu` (IndefUse.lean:271).

## Not read

- The bodies of `MuChar`, `RatioMax`, `FinSup`, `SatR`, `SatBasic`, `HNSlopes`, `place_lattice_structure`, `PlaceDecomposition.finrank_span_complex`, `Twist`/`RescaleCovol`, and the saturation half of `slopeIneq_of`.
- `hnExtreme_mem_iff`, which goes through `Lemmata.GeneralBFactLeftForm`.
- The proofs of `CorBounds`, `CompressTraceSquareBound` and `CompressDiagDefectBound` (CSW/TraceConjTransposeMulSelf.lean:450,591).
- The suppliers of `InputSG`, of the bound on `delp`, and of HH.
- The helpers of `local_idW` (`key_alg`, `idx_change_img`, `gram_image`), and the proofs of `LcvBasis`, `IdxChange`, `DetCS` and `prod_formula'`.
- `specDet`, `latticeGlue` and `ramBasic`.
- The concrete `DefSide`/`IndefRows` construction, that is, what HT, Tl, θ, M, κ and λ are concretely.
- `P.extra.passage`, and the suppliers of the `DivInputsR` fields.
- The hops from `closed_linkDIVt_of_closed_bridge_kernel` to `wordFacts_of_face`, which I took from the lattices slice.
