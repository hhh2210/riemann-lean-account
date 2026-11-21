# Theorem S: the Gram operator of the Bessel–Poincaré series

Read 2026-11-20 from the source text only; nothing was built. Paths are relative to `lean/src/`.

Abbreviations:
- SLT = `Formalism/LocalToGlobal/SiegelLatticeTheory/`
- FST = SLT`FlagStabilizerTensors/`
- CSB = `Formalism/SharpRestriction/CuspSpanNormBounds/`
- PB = `Formalism/HermitianCurvature/StatementPB.lean`
- FM = `Development/AbelianVarietyTheory/Proofs/FlagMeasures/`
- GTI = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`
- TD = `Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean`

Tags: **[R]** read (definition or statement transcribed); **[P]** proved-by (proof body read, inputs named); *[I]* inferred.

## Direct answers

1. **The groups.** **[R]** + *[I]*
   - G = U(V), with dim V = n = k + 2rS + 1 and signature (k+rS, rS+1) at each real place.
   - H = U(W), with W = ⟨e, f, z_u⟩^⊥, is definite of rank k.
   - S = N⋊H is a Bessel subgroup, cut out by an isotropic flag e₁…e_rS and a vector z_u of norm −T(u).
2. **The Poincaré series.** P_u sends a form T on H of archimedean type π_u to Σ_{S(F)\G(F)} Ph_T(δg), and lands in HH: the forms of one discrete-series type σ at infinity with a character χ₂ at level K₂. **[R]**
   - Ph_T(n·h·x_u·κ, g∞) = ψ(n)·χ₂(κ)·T(W_u(g∞))(h).
   - W_u is the Bessel function of σ.
3. **Theorem S** (`Conclusion1`) is about K_uu′ = (c0_u·c0_u′)^(−1/2)·P_u*P_u′, with c0_u = volN·volH/dim π_u. **[R]**
   - Degenerate terms vanish for u ≠ u′.
   - The degenerate part of K_uu has HS² ≤ d_u·e^(−kf log k).
   - For u ≠ u′, ‖K_uu′‖²_HS ≤ (1+b⁻⁶)·d_u·d_u′/D*.
   - ‖K_uu − 1 − (degenerate part)‖² ≤ Γ·d_u²/D*.
   - A separate point count gives dim HH ≤ (1+e^(−c r f log r))·D*.
4. **The proof** is a relative trace formula. **[P]**
   - The Gram matrix unfolds into double-coset orbital integrals of W_u ⊗ W̄_u′.
   - Identity cosets give exactly 1 on the diagonal (Schur orthogonality on the compact H∞, with c0 as the constant) and 0 off it.
   - Degenerate cosets vanish off the diagonal by Schur's lemma for a U(k) inside their stabiliser, and decay like (C/k)^(j(k−1−j)f) on it.
   - The rest goes through a Cauchy–Schwarz expansion over pairs of cosets. Scalar pairs give exactly d_u·d_u′/D*; everything else is exponentially small.
5. **Siegel–Weil** (2a < n) is used only as a mass formula: frame stabilisers have the volume of [G]. The archimedean half of the main term is ∫‖orbital integral‖² ≤ 1/(formal degree), which rests on Bessel multiplicity one. **[R]** + *[I]*
6. **On the path** the frame's Gram blocks are exactly these K_uu′ (`kp_eq`), and every P_u is nearly isometric. **[P]**
   - LinkS is conditional on a window d_u ≈ D*/Γ², which the consumer supplies.
   - That the abstract datum `D.s` is the concrete Poincaré setting is a field of the selected record.
   - No degenerate instantiation was found.

## 1. The statement

**Data.** **[R]**
- `HidaSetting` (SLT`HaarTransversals/HidaSetting.lean:179`) has:
  - isotropic vectors eX, fY with ⟨e_a, f_b⟩ = δ_ab;
  - `zu_norm : hT (zu u) (zu u) = -T(u)` (:218);
  - `piU u = ⊗_v piLoc u v` with `piLoc_type : IsHCTypeU k (hcW u (pl v)).u`, the archimedean type of word u.
- `Ranks` (`Formalism/LocalRingCardinality/Params.lean`) sets r = k+m−1, rS = m/2−1 and `sigY0 = (k + rS, rS + 1)`. H∞ has finite Haar measure, and π_u is irreducible on it (`PiIrr`, SLT`ClosedLocalOrbits/GaugeLatticeShifts/IdBlocks.lean:664`).
- `Hinf`/`Hfin` fix the e's, f's and z_u (SLT`HaarTransversals/PoincareInHH.lean:62–64`). `Sinf` (HidaSetting.lean:57) requires (g−1)e_a ∈ span(e_{<a}) and (g−1)z ∈ span(e). `Srat = G(F) ⊓ closure{y | y.1 ∈ SinfU ∧ y.2 ∈ SfinU}` (PoincareInHH.lean:149).
- The character ψ is exp(2πi·tr Σ_a ⟨f_a, g·nxt(e,z)_a⟩) (`psiR`, `psiFin`).
- `IsWu` (HidaSetting.lean:151) has three clauses:
  - W(sx) = ψ(s)·π_u(s)·W(x) on S∞;
  - ∫ ph(y)·W(xy) = W(x), where ph = (∏ d_v)·conj⟨σ(g)w, w⟩ (`phInf`, SLT`HaarTransversals/ProjRows.lean:117`);
  - ∫|W|² dν = 1.

**The Poincaré series** (PoincareInHH.lean:155–208) **[R]**:

    def Ph … (T : Cu X u hK) (y : GA) := if hd : ∃ n h k, IsDec X u y.2 n h k then phVal … else 0
      -- IsDec: n ∈ NfinU u ∧ k ∈ K2 ∧ y = n * h * xu u * k ;  phVal = psiFinU u n * chi2 k * T (Wu u yinf) (1, h)
    def Pser … T x := poinc Dt (Ph X u hK T) x        -- Dt: right transversal of G(F) mod Srat
    abbrev HHX := RowsDef.HHB X.B X.Rph              -- InHH: Re (Rph (PuFun T)) = PuFun T

- `Cu X u hK = Cols … (piRep X u)` is normed by `sharp`, the values at class representatives (`CM cs = PiLp 2 (cs.Cl → Vpi u)`, SLT`ClosedLocalOrbits/TermOp.lean`). **[R]**
- These are algebraic modular forms on the definite H, the M_u of the lattice slice, and P_u is the adjoint of a Bessel period for (U(n), U(k)). *[I]*

**Theorem S** (`CSB/RelevantZeroGramTerms.lean:335–343`; `CSB/AdmissibleBoundsFromSource.lean:212`) **[R]**:

    def c0 u := s.volN u * s.volH u / dimPi u        -- dimPi u = ∏_τ dimPiU k (u_τ)
    def Kmat u u' := ((c0 u * c0 u') ^ (-1/2)) • (adjoint (Pu u)).comp (Pu u')
    def Conclusion1 :=
      (∀ u u', u ≠ u' → Kpp D u u' = 0) ∧ (∀ u, hsNormSq (Kpp D u u) ≤ du u * exp (-(k*f*log k))) ∧
      (∀ u u', u ≠ u' → hsNormSq (Kmat u u' - Kpp u u') ≤ (1 + b^(-6)) * du u * du u' / Dst) ∧
      (∀ u, hsNormSq (Kmat u u - Kpp u u - id) ≤ Gam * du u ^ 2 / Dst)

- `Kpp = KOf … {t | Gterm t = 0 ∧ ¬ isId t}` (`CSB/NonGenericAndKTwoTheorems.lean:52`). **[R]**
- `Gam = GamOf = exp(CGam·m⁵·f·L)` (`CSB/StandingHypothesesHoldFamily.lean:119`). **[R]**
- FST`ThmSOwn.lean:37–49` splits `Conclusion1` into ClKppOff, ClKppDiag, ClOff and ClDiag (`Iff.rfl`). **[R]**

**LinkS** (GTI:145) **[R]**:

    LinkS_at … := (∀ u, C0⁻¹ ≤ duS u * Gam^2 / Dstar ≤ C0) →
      (∀ u ≠ u', hsSq u u' ≤ (1+η0) duS u duS u' / Dstar) ∧ (∀ u, hsDiagFull u ≤ e0 duS u) ∧ Dall ≤ (1+η1) Dstar

- `linkS_concl` (CSB`StandingHypothesesHoldFamily.lean:186`) takes the off-diagonal clause from clauses 1 and 3. **[P]**
- `diag_unproj` (:144) takes the diagonal from clauses 2 and 4. The window turns Γd_u²/D* into (C0/Γ)·d_u, so e0 = 2C0/Γ + 2e^(−kf log k). **[P]**
- The dimension clause comes from a point count, `adm10`. **[P]**
- Off the window, `linkS_of_standing_hypotheses` (:628) returns (0, 0, 0) vacuously. **[P]**

## 2. The proof

**Step 1: unfolding.** `KExpansion` (SLT`ClosedLocalOrbits/TermOpStmt.lean:23`) **[R]**:

    ∃ K, HasSum (fun t : GTerm … => aTerm cs cs' FdN FdN' t) K ∧ ∀ T T', Kform … T T' = ⟪K (sharp T'), sharp T⟫
    -- Kform = (√(c0X u · c0X u'))⁻¹ · ⟪PuFun T, PuFun T'⟫   (PoincareInHH.lean:260)

- A `GTerm` (TermOp.lean:86) is a class-lattice pair (Λ, Λ′) with a rational γ modulo NLam(F)×NLam(F′): an integral double coset. **[R]**
- `blk` (:246) gives block (ρ, ρ′) as scl·volK2·χ₂(k)·OOt t when k = (h_ρ x_u)⁻¹γ_f(h_ρ′ x_u′) ∈ K₂, and 0 otherwise. Here OOt t = ∫_{Ω_t} rk1(W_u x, W_u′(γ∞⁻¹x)) (:25, :149). **[R]**
- `KExpansionC_holds` (SLT`ClosedVolumeStatements/UnipotentInLevelSubgroup.lean:63`) proves the expansion from slab covering (strong approximation), regrouping and a neat level. **[P]**
- `kmat_eq` (FST`RootLatticeThresholds/NormalizingConstantEq.lean:206`) identifies Kmat with K. **[P]**

**The partition** (PB:45–61). **[R]**
- identity cosets;
- degenerate: G = 0, not identity;
- non-generic: G ≠ 0, not generic;
- generic: G ≠ 0 and generic.

G is `Gflag = |D_{r+1}|² − T·T′·|D_r|²`, from leading minors of the Gram matrix of the two frames (CSB`BlockEnds.lean:53–63`). "Generic" is a lattice condition at the primes over g (CSB`IsPrimitiveSub.lean:265`). Identity cosets have G = 0 (`gval_eq_zero_of_inSF`). **[R]**

`hsNormSq_off` (ThmSOwn:335) and `hsNormSq_diag` (:345) reduce clauses 3 and 4 to ‖K0‖² and ‖K0 − 1‖². K0 is the sum of the identity, generic and non-generic parts. **[P]**

**Step 2: identity terms.** `oo_eq` (IdBlocks.lean:301) **[R]**:

    ∫ x in Ω, (innerSL ℂ (W x)).smulRight (W x) ∂μG = ((μN.real Ω * μH.real univ / finrank ℂ V : ℝ) : ℂ) • id

Its inputs are Weil's formula μ_G = (μ_N×μ_H)·ν, the covariance of W, irreducibility of π on H, and ∫|W|² dν = 1.

- **Diagonal.** **[P]**
  - `oot_eq` (:672) evaluates the identity coset.
  - `idDiagBlocks_of` (:761) uses scl = c0X⁻¹, where c0X = volK2·μN(FN)·μH(univ)/dim Vpi (PoincareInHH.lean:257), and `IdMeetPhase` (χ₂(k)·ψ̄ = 1). The coefficient is then exactly 1 (`hcoef`).
  - So c0 is the identity orbital integral.
- **Off the diagonal.** `oot_off_eq_zero` (:896) uses `cross_zero` and `IdOffIneq`: no H∞-intertwiner exists from π_u′∘Ad γ to π_u. **[P]**

**Step 3: degenerate terms, u ≠ u′.** `SchurNFC` (SLT`CokernelGLCounts/RankPointCounts/KappaOffDiagonal.lean:47`) **[R]**:

    (∀ τ, uS D u τ ≠ uS D u' τ) → Relevant … → Gval … = 0 →
    ∀ P, (∀ h ∈ pointwiseStabilizerInfinite X q, piU u h ∘ P = P ∘ piU u' (γ⁻¹ h γ)) → P = 0

- `GeomB` (`…/SchurCoreA.lean:72`): when G = 0, the stabiliser contains elements acting by M on π_u and by CMC* on π_u′, for every M ∈ ∏_v U(k). **[R]**
- `SchurCoreA` concludes P = 0 when the parameters differ at one place. **[R]**
- `kppOffC_of_steps0` (`…/FixedDecomposition.lean:755`) handles both cases. **[P]**
  - Irrelevant terms (ψ_F ≠ ψ_F′ on N_F ∩ N_F′) vanish by `LemmaV`.
  - Relevant terms are covariant, so Schur's lemma kills them; `words_differ` makes the parameters differ at every place.

**Step 4: degenerate terms, u = u′, and `UniqGap`.** `UniqGap` (`CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/AtFormAdmOneOfSteps.lean:15`), condensed **[R]**:

    1 ≤ k → GapAtLeast ε lam h → 120·n³ ≤ h → IsHCParam lam → IsDSHpk k r ε lam σ → … → IsHCTypeW k r z u π →
    ∀ B₁ B₂, IsBesselMapSm z (psiGen z c) σ π B₁ → IsBesselMapSm … B₂ → ∃ a b, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v smooth, a • B₁ v + b • B₂ v = 0

In words: for a discrete series of U(p,q) whose Harish-Chandra gaps are at least 120n³, Bessel maps to π_u form a space of dimension ≤ 1. **[R]**

**The chain** (`typeBound_of_gap`, FM`TypePOfLargeGapDiscreteSeriesBessel.lean:15`). **[P]**
- `uniqGap_holds := besselMapUniqGap` (proof not read) → `GapIn.Hyp`.
- `GapIn.Hyp` gives `TailP` (local Bessel tail bounds), which with `LocDatC` (from `BesselOfW`) gives `AmpP`.
- `PairsP` comes from Siegel mass ratios.
- `AmpP` and `PairsP` give `TypeP`.

**What `TypeAt` says** (SLT`CokernelGLCounts/RankPointCounts/DimFormC.lean:40`). **[R]**
- Over pairs of relevant degenerate terms of corank j′, j″, Σ‖vec‖·‖vec′‖ ≤ dim π·mass·(k2a·k2e)(j′)·(k2a·k2e)(j″).
- The corank is j = rS − dim(X_F ∩ X_{γF′}) ≥ 1.
- k2a carries the factor (C/k)^(j(k−1−j)f) (CSB`KappaEndpoints.lean:2965`).

**How clause 2 follows.** **[P]**
- `pairs_degree_bound` (FST`RowsPos.lean:95`) and `final_bound_closes` (KappaEndpoints:2593) give 2d·k2B ≤ d·e^(−kf log k) once k2C0·m⁶·L ≤ k log k. Here k2A j = e^(Cm⁶fL)·(C/k)^(j(k−1−j)f).
- `kppDiag_of_pairs` then gives clause 2.

**Mechanism.** *[I]*
- Uniqueness makes W_u a fixed projection of one discrete-series vector. `AmpKF0` (`Development/AbelianVarietyTheory/Definitions/SemilocalFrames/UniqGapOfUniq.lean`) writes the amplitude as (formal degree)⁻¹ times the orbital integral of a matrix coefficient.
- A degenerate integral is then a U(k)-type matrix coefficient of relative size (C/k)^(j(k−1−j)) per place.

**Step 5: the pair expansion for G ≠ 0.** **[R]**
- `vec t = wt(t)·hsEmb(ampN t)` (TermOp.lean:343). Rows record (Λ, Λ′) and the Levi class in ∏_v GL_k(F_q) at the primes over g₀ and g₁.
- `NormExpansionOn` (PB:86): ‖part S‖² = Re Σ_{i,j} GG(i,j)·⟨vecPart i, vecPart j⟩, with GG(i,j) = conj γ(j⁻¹i), γ the normalised Gelfand–Graev character (`GGMirabolic.lean:28`).
- `GGBound` (PB:89): Pg·Γ₁·I ⪰ GG, with Pg = ∏(1+3/q_v).
- `PairSplit` (PB:139) writes Γ₁·Σ‖vecPart‖² as Σ over pairs in a common row of Re⟨vec t, vec t′⟩.
  - Generic pairs are split by the corank s0: big (s0 ≥ 2), non-scalar (s0 = 1), scalar (s0 = 1).
  - Non-generic pairs are split into big and s0 = 1.

`PairBound` (PB:220) gives ‖K0‖² ≤ (1+b⁻⁶)·dd, with dd = d_u·d_u′/D*. **[R]**
- **Hypotheses.**
  - `IdZero`;
  - `RowBig` and `RowNotScalar` ≤ e^(−c k f log k)·dd;
  - `RowMain` ≤ (1+δ)·e1·dd, with δ ≤ b⁻⁷ and e1 ≤ exp(12f/2^(k−2r−2));
  - `RowNG` ≤ 2^(−(k−2r−5))·e^(Cn·m⁵·f·log b)·dd;
  - Pg = (1+3/g₁)^f·(1+3/g₂)^f.
- **Assembly.** (√(Pg(A+2ε)) + √(Pg(ε+ε′)))² ≤ 1+b⁻⁶ (PB:206).

**Off the diagonal**, `theoremS_closedP` (FST`TheoremSClosedP.lean:256`) gets its inputs from `pbApplied` (FST`TheoremS.lean:19`) via `theoremS_rec` (`SpectralTiesReal.lean:147`). **[P]**
- `IdZero` from `idZero_tO`.
- The loops from `LoopRowS`, a lattice-sum count, at e^(−kf log k/3).
- `RowNG` from `rowNGP_of_siegelWeil`.
- `RowMain` from `MainRow`.

**On the diagonal**, `diagonal_positive_final` (RowsPos.lean:242) uses `IdOne` (identity part = 1) and a crude `RowMain` with gamB = e^(CB·m⁵·f·log b). `DiagNumC` absorbs this into GamP. **[P]**

**Step 6: the main term and Siegel–Weil.** `MainRow` (PB:381) concludes `Γ₁·Sig ≤ (1+δ)·e1·(d·d′/D*)`. **[R]**

Its proof, `t_MainRow` (`Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean:1070`), runs in three steps. **[P]**
1. `RowsInput` makes sd·Kr − Σ_ρ c_ρ c̄_ρ positive semidefinite. A lattice estimate with recursion (`TC.TheoremAAfter`, `TC.RecursionWithDens`) then gives Σ_ρ‖Σ_p c_ρ(p)·Vt(p)‖² ≤ (1+δ)·e1·IntN.
2. This becomes c0·c0′·KV ≤ (1+δ)·e1·n0c·IntN.
3. `S3.MainTheorem` (`Formalism/HermitianCurvature/MemParahoricTimesPrincipalCongruenceIff.lean:675`) closes with the relations of `MassData` (:608–624): `InForm` (Sig = ρ0·KV), `InKernel`, `InTheoremA`, `InInfinity` (IntOO ≤ 1/deg) and `InVolumes` (volB·volG = volHa·volHa′). Here `Dstar = deg·volG/μKpp` and `c0 = volN·volH/dimπ`.

**Two more inputs.** **[R]**
- `InInfinityX` (SLT`ClosedLocalOrbits/RealObj.lean:172`): the integral over generic archimedean double cosets of ‖OOinf‖²_HS, with weight ∏ G_v^(k−1)·JacV, is at most 1/∏ d_v. It is supplied by `realObj_inInfinityX_jsz` from `UniqGap`.
- `FormulaC` (FST`TheoremSRecursion.lean:34`): the genus-averaged number of generic frames at relative position Z equals c·|N(scaled Gram)|^((k−1)/2)·∏_p (local density). It is proved by `formulaCT_holds` (not read).

**Siegel–Weil** (`Formalism/UnipotentAdelicQuotients/SiegelWeilUnitaryConvergent.lean:18`) **[R]**:

    ∀ n, 2 * n < M → ∀ T Hermitian, det T ≠ 0 → … Φ = Φ∞ ⊗ Φf (Φ∞ smooth, compact support) →
      ∃ ginf gv, (Gram-pushforward densities of Φ_v) ∧ Multipliable … ∧
      meanC μ 𝓕 (thetaS … Φ {X | gramE σ J X = T}) = ginf T * ∏' v, gv v T

- **Use.** `swxs_of_siegelWeil` → `volStabXS_of` → `VolStabAt` (SLT`CokernelGLCounts/Volumes.lean:55`): vol[Stab X0] = vol[G] in compatible measures. **[R]**
- **Consumers.** `InVolumes` (via `inVolumesAt_of_SWS`), `normalizing_constants_all`, `massDataVolAll_of`, `RowNGP`, `RowMainEqP` (via `genericFamilyStep_of_siegelWeil`), and the loop rows (`volumeRatio`). **[R]**
- **Proof.** The tree proves it (`siegelWeilUnitaryConvergent`, `CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/Imports.lean:10`); not read. **[R]**
- **Reading.** *[I]*
  - The [U(V)]-integral of Σ_{Gram X = T} Φ(g⁻¹X) is the product of local Siegel densities at T. That product is the T-th coefficient of the Siegel–Eisenstein series on U(a,a) at absolute convergence, though the tree states only the product.
  - Unfolding the left side gives vol[Stab] = vol[G].
  - So the main term is d_u·d_u′/D* = (dim π_u·vol H)·(dim π_u′·vol H′)/(deg·vol G).

**Where k, g, b and T enter.**
- **The decay is in k.** **[R]**
  - (C/k)^(j(k−1−j)f) for degenerate terms;
  - e^(−kf log k/3) for loops;
  - 2^(−(k−2r−5)) for non-generic terms;
  - e1 for the density.
- **Conditions** (`KTwoParameterConditions`). **[R]**
  - Cl·m⁶·L ≤ k log k;
  - (kb)⁸ ≤ g_i ≤ b^Cg;
  - parameter gaps > Cl·k·m³;
  - T(u) ≤ b^(CT·m).
- **T has no decay rate of its own.** It is the norm of z_u. It enters G, the congruence T(u) ≡ T(u′) mod gS² (`Stand`, `ChoicesC`), the height bounds, and d_u ∝ (T^k − 1)^f. **[R]** + *[I]*

## 3. Standard and new

All tagged *[I]*.

**Standard.**
- Unfolding a Gram matrix of Poincaré series into orbital integrals: the Petersson or Kuznetsov pattern, for Bessel periods; compare the relative trace formulae for Bessel periods on unitary groups.
- The identity term by Schur orthogonality and formal degree.
- Off-diagonal vanishing by Schur's lemma for distinct K-types.
- Decay of matrix coefficients in large rank.
- Archimedean Bessel multiplicity one, used here only in a large-gap range.
- Siegel–Weil in Weil's range, used as a mass formula.
- Gelfand–Graev bounds.
- Lattice counting with error (C/Th)^f.

**New-looking.** Uniformity over whole families.
- Across about Γ²·x^CH archimedean types, all off-diagonal Gram blocks are at most (1+b⁻⁶) times their size for random subspaces, and all diagonal blocks are within e^(−x^(ε/8))·d_u of the identity.
- k, f, n and the groups all grow together.
- The diagonal estimate (Γ·d_u²/D*) is deliberately crude. It is small only because the window forces d_u ≈ D*/Γ².

## 4. B_u and the Gram operator

**The Gram operator is K.** **[P]**
- `matKF_of` (TD:1348) calls `matK_at_of` (TD:1097) with `blockReal_at_of (BesselId)`.
- `kp_eq` (TD:1069): `KpG (fun u => (PMat f u).map ε) (fun u => (c0 D.s u)⁻¹) u u' = (opMat (KD u u')).map ε`.
  - `PMat` is the matrix of `D.s.Pu u` in an orthonormal basis of HH.
  - `KD = Kmat D.s` (RelevantZeroGramTerms:509).
- `hs_opMat` (TD:1025) matches the HS norms. So `InputSG`'s blocks are exactly Theorem S's K_uu′.

**`D.s` is the concrete setting.** **[R]**
- Theorem S is proved for `sOf hF` and transported along `hI : SIso D.s (sOf hF)`, which matches Pu, volN, volH and the terms isometrically (`isoNorm`, `packageTieConc`).
- `hI` is a field of the selected `STies` (`SpectralTiesReal.lean:245`), obtained from `SRest.hI` (`Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/SameDegreeZeroFormsSelf.lean:48`).
- `SPack.toNew` there sets `s := sOf P.fin`. *[I]* The identification is by construction; I did not read who builds `SRest`.

**Non-vanishing.** **[P]**
- The window gives d_u > 0 (`hdu` in `matKF_of`).
- `unfolding_constant_pos_of_diagonal` (TD:1334) uses ‖K_uu − 1‖² ≤ e0·d_u with e0 < 1. A zero P_u would give ‖−1‖² = d_u, so every P_u ≠ 0. *[I]* P_u is injective off a subspace of dimension ≤ 4e0·d_u.
- `BesselId` (GTI:65) writes B_u = a·⟨sEE F, P_u(ιφ)⟩ with a ≠ 0.
- `compressDiagDefectBound` (`Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean:450`) keeps the per-word bound ‖γB*B − 1‖² ≤ e0·d_u for PMat·Vr (all HH rows), so that map is non-zero.
- Nothing asserts that the EE-row block of each B_u is non-zero. Theorem F uses the extended maps, and `LinkDIV_at` bounds heights only under `Bk u ≠ 0 → …` (GTI:80). **[R]**

**Degenerate instantiations.** None found. Two conditionals are discharged, and one non-triviality holds. **[P]**
- `LinkS_at` assumes the window; `matKF_of` supplies it from `ChosenProviso`.
- `ThmSOwn` assumes `hyp`; `standing_hypotheses_hold_family` supplies it.
- `ChCode_at` forces many words.

## Chains

- `link_alt_alt_bis` (`…/ThirdPlaceSeries/LinkAltAltBis.lean:16`) → `theoremS_transport_link_zero` (FST`LinkSPos.lean:131`) → `theoremS_link_concrete` (:108) → `theoremS_link_of_evaluation` (:97) → `linkS_of_standing_hypotheses` (CSB`StandingHypothesesHoldFamily.lean:628`) → `linkS_concl` (:186), `diag_unproj` (:144).
- ClOff: `hypOwnS_off` (ThmSOwn:891) ← `hsNormSq_off` (:335) and `TheoremSSelected` (:669).
  - `TheoremSSelected` ← `CarrierGap.offDiag` (`Development/AbelianVarietyTheory/Proofs/FlagMeasures/OffK0Closed.lean:673`) ← `offDiagonalK0_of_rows` (FST`LinkSFinalP.lean:58`) and `theoremS_leaves_of_carrierG` (OffK0Closed:633).
  - `theoremS_leaves_of_carrierG` → `theoremS_closedP` → `pbApplied` → `t_PairBoundFromLocal` (GrowthOfBasic:1236), `t_MainRow` (:1070).
  - `offDiag` is called by `at_choice_alt` (`Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/AtChoice.lean:16`) with `swxs_of_siegelWeil` and `rowNGP_of_siegelWeil`.
- ClKppOff: `hypOwnE_kppOff` ← `KppOffC_holds` (SLT`ClosedVolumeStatements/FullExistsTiedHolds.lean:36`) ← `kppOffC_of_steps0` ← `schurNFC` (SchurNFCOf.lean:34).
- ClKppDiag: `hypOwnE_kppDiagP` (LinkSPos:21) ← `kernel_diagonal_positive` (RowsPos:202) ← `rowsPos_typeP` (FM`RowsPosTypeP.lean:9`) ← `typeBound_of_gap`.
- ClDiag: `hypOwnL_diagP` (LinkSPos:57) ← `diagonal_positive_final` (RowsPos:242) ← `RowNGP`, `RowMainEqP` (FM`RowMainEqPOfSiegelWeil.lean:10`) and `IdCellDiagC_holds` (UnipotentInLevelSubgroup:98) ← `idDiagBlocks_of`.

## Not read

- The proofs of `besselMapUniqGap`, `BesselOfW`, `tailP_of_gap` and `amplitudeBound_of_localData_of_tailBound`, which carry the (C/k) decay.
- `kExpansionC_holds_of`, the unfolding and its convergence (`OOLintSumC`).
- `TC.TheoremAAfter`; the proof of `S3.MainTheorem` and its mass identities; `formulaCT_holds`; `carrierP` and `CarrierFull`.
- `loopRows_of_rowsFinDim_alt` and `corankOneNonGenericRowBound_closed`.
- The proofs of Siegel–Weil and of `volStabFromSW_holds`.
- What `IsScalar` and `s0` mean beyond their definitions; `NormExpSat`.
- Who builds `SRest`; `ChosenProviso`; `CountAllPointsClass`; `IdOffLift`; `realObj_inInfinityX_jsz`.
