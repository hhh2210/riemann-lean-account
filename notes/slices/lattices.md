# The lattices and gains behind the count bound

Read 2026-11-20 from source text only (build unfinished). Paths are relative to `src/`. Abbreviations: `LRC/` = `Formalism/LocalRingCardinality/`, `GSB/` = `Formalism/SharpRestriction/GlobalSchurBounds/`, `SWB/` = `Formalism/SizeWindowBrackets/`, `Div/` = `Formalism/LocalToGlobal/Divisibility/`, `D7:n` = `LRC/RhoDetPrimeEqMuTildeMulChiPow.lean:n`. Tags: **[R]** read, **[P]** proved-by, **[I]** inferred.

## 0. The record on the path

- [R] `MeanBoundSecondForm` (`Formalism/RankGapBounds/MeanBoundSecondForm.lean:187`) is not used. A fixed-string search of all of `src/` finds only its definition and four module imports, and no proof.
- [R] `ChainTied` (`GSB/TieGlobal.lean:97`) demands `LChain.SizeData₂ Dd C Xpp` (`SWB/SChain.lean:17`) `:= HidaSetting ∧ DIV ∧ EComp5 ∧ HComp ∧ Count5 ∧ Slopes ∧ QuotientSlopeBoundsWith ∧ LossBounds ∧ SlopeIneq ∧ HHBound ∧ FParams`.
- [R] `DIV` and `SlopeIneq` are the definitions `MeanBoundSecondForm` uses. Three hypotheses differ (`SWB/QuotientSlopeBoundsWith.lean:19,27,34`). `SlopesN` has the loss `Lo5 = cSl1·IO + cSl1·nT·m(a/k+b')·log T + cSl1·Xpp + 1`. `Losses` holds for every u0, not on average. `Count` has `La` for `L` and no `logGam` term.
- [P] The eleven are consumed by `each_unit_bound_statement : PointwiseBoundVariant` (`SWB/ChainSlopeWindows/LevelOfCongruence.lean:175`), which gives `ASK u0 ≤ Main u0 + ErrX5at u0` for every u0. It is used in `ch_top` (`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean:54`).
- [R] The producer, each call read: `plugAll` (`Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean`) → `shapeWin` (`Development/AutomorphicArithmetic/CharacterBoxes/ShapeWin.lean:27`) → `link_gl` (`Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LinkGl.lean`) → `FamGLmin.link8`/`link7` (`GSB/LogXLowerFamilyOfTheorems.lean:60–74`) → `linkGLOBAL7_min` → `linkGLOBAL7_items` (`GSB/LinkMin.lean:723, 693`) → `linkCore` (`GSB/LossesSmallShares.lean:38`). `linkCore` builds `DIV`, `Count5`, `QuotientSlopeBoundsWith`, `LossBounds` and `SlopeIneq` from `LinkDIV`, `CountF`, `SlopesNF`, `LossFS` and `FrameF` respectively.
- [R] `shapeWin` passes `linkDIVt_closedK`, `link_g`, `link_alt` and others to `topDesWin`. [I] I did not read `topDesWin`, and assume it routes them to the inputs of `LinkGLOBAL`.

## 1. What the datum is

**Ring and metric.**
- [R] All three lattices have type `HLat LL`, with `LL = what₂.LL` (D7:114, 285). An `HLat K` (`LRC/DataArith.lean:61`) is a K-vector space V with K-basis `b`, an `𝓞 K`-submodule `L`, and a complex matrix `X v` for each infinite place v.
- [R] The norm at v is `normAt b X v x = ‖(X v)⁻¹·v(coords x)‖` (`Formalism/HermitianLattices/StatementMaj.lean:35`).
- [R] The slope is `muDef b X L = 2·slope(realize b X) L − log 2 + log|d_K|/[K:ℚ]` (`Formalism/HarderNarasimhan/StatementPl.lean:64`). Here `realize` embeds V in ⊕_{v,i} ℝ², and `slope = −log covol / rank_ℤ` (`Formalism/LatticeSlopes/Statement.lean:15–25`). `muMax` and `muMin` are the extreme slopes of sublattices and of quotients (`Formalism/HarderNarasimhan/Statement.lean:29–33`).
- [R] LL is a totally complex Galois number field, and its star is complex conjugation under `embLL` (D7:106–112). The host CM field E maps into it by `embE`, with `embLL ∘ embE = φ₀` (D7:120).
- [I] μ is the Arakelov degree per rank of a Hermitian 𝓞_LL-module, doubled and normalized by [LL:ℚ].

**M_u = `(fm u).lat 0`.**
- [R] `emb 0 : V →(embLL) (cls 0 → Y 0 → ℂ)` sends `b` to a basis of `Fi 0 = A.Mu0`. At the place `embLL`, `majAt … x x = Σ_c wt 0 c · ipV 0 c (emb x c) (emb x c)` (`LRC/DataForms.lean:165–176`), where `wt i c = 1/|stab i c|` (`LRC/DataKernels.lean:55`).
- [R] Each class `c ∈ cls i` carries an 𝓞_E-lattice in the Hermitian space `X i` (`clsLat`, D7:162). `X j` is definite of rank `N j = k + j(t+1)` (`LRC/DataSpaces.lean:86–87`).
- [I] So M_u is an integral structure on vector-valued algebraic forms on the definite unitary group of X_0, functions on genus classes, carrying the Petersson norm at one place.
- [R] T(u) = `(mem u).A.T` is prime. `A` provides f fields `Fv v` of size T, acting on forms by `rhoT v`. `Mram = Mu0 ⊓ ⨅ v, ker (Σ_{c∈(Fv v)ˣ} rhoT v c)` (`LRC/DataKernels.lean:107–149`).
- [I] Mram consists of the forms without invariants under any torus `(Fv v)ˣ`, the forms ramified at T.

**N_u = `div.Nu u`.**
- [R] `nuIn u : V_N →ₗ[LL] V_M` is injective with range `ramSub = (emb 0)⁻¹ Mram`, and it preserves `normAt` at all infinite places (D7:291–297; `LRC/DataForms.lean:239`). `eMu u` identifies `what₂.Mu u` isometrically with Mram (D7:165, 287).
- [R] On the path the family fixes the lattice through `nprimeDef` and `nuDef` (`Formalism/SharpRestriction/ParConsts.lean:70–71`).
  - `NprimeDef` (`LRC/DataDIVDefs.lean:22`) says `(div.Nu u).L = span{a•y | a ∈ Iu, y ∈ NuLat u}`, where `Iu = ∏_{w∈supp} 𝔓_w^(−⌊e_w·sg u w⌋)` (:17).
  - `NuDef` (:48) says that, away from T(u), `NuLat u ⊆ MramL u = (nuIn u)⁻¹(M_u.L)` locally (:12). Equality holds where p ∈ `drop` or p is neither inert nor signal. The local length of `MramL/NuLat` at w is `lenMN u w·e_w`.
- [I] So N_u is the ramified part of M_u, cut down at the served primes and then divided by 𝔓_w^{sg(u,w)}.

**Target.**
- [R] `jEE` sends a basis of `RR.V` to a basis of `EE`, and `normAt RR.b RR.X (mk embLL) x = ‖jEE x‖` (D7:185, 300). EE is a complex inner-product space with `Drows = (1 − delp)·Dall` (`LRC/DataRows.lean:62–71`).
- [R] `RRDef` (`LRC/DataDIVDefs.lean:26`, imposed via `rrDef`): x ∈ RR.L iff, at each w, some d ∉ 𝔓_w has `d•x ∈ span{y | jEE y ∈ RRset (muAt w)}`. Here `RRset μ = ι_μ(proj_{Qsp μ}(Mtilde μ ∩ V0 μ))` (`LRC/DataRows.lean:184–199`), with:
  - `Mtilde μ` an O-lattice in `Amb μ`;
  - `V0` the range of a self-adjoint idempotent;
  - `Qsp = V0 ⊓ (V0 ⊓ ker ι)ᗮ`;
  - ι running down a tower `Mult μ m → … → Mult μ 0 ≅ EE`.
- [R] CC is `cc = RR.dualL = {f | ∀x∈L, f x ∈ 𝓞_LL}`, with the dual basis and the frame `((X v)ᵀ)⁻¹` (`LRC/DataArith.lean:92–102,168`; `Formalism/HarderNarasimhan/QuotRealize.lean:15,28`). μ_CC = `RR.muDual` and μ_min,CC = `RR.muMinDual`.

**The map and the height.**
- [R] `Bk u : V_N →ₗ Dual(RR.V)` (`LRC/DataArith.lean:146`). `BuRational` (D7:364) says `Bu u (jN u φ) (jEE x) = embLL (Bk u φ x)`.
- [R] `perCol_base_eq_PtilCol` (D7:169) equates `perCol u μ0 φ F` with `PtilCol φ F = period (lowerMap (evz (col φ))) F`, where `col` is the m-fold composite of the kernel operators `K i` (`LRC/DataKernels.lean:67–70,192–195`).
- [I] So `Bk u` sends a ramified form to "the period of its m-fold iterated theta lift", viewed as a functional on the target.
- [R] `LinkDIV_at` (`Formalism/SharpRestriction/GlobalTheoremInputs.lean:77`) requires `Bk u ≠ 0 → htMap … (Bk u) ≤ h u`. Here `htMap = (1/#places)·Σ_v log ‖Bk u‖_v²`, with operator norms taken from the metric of N_u to the dual metric (`StatementPl.lean:60`).
- [R] `h_eq` (`ParConsts.lean:73`) gives `h u = SZbP u + Σ_j kernelPlaceMeanBound u j − Σ_j L6lo j − meanE log κ_R` (`LRC/KernelPlaceMeanBound.lean:25`), where `SZbP u = −Σ_t a_t·log T(u) + C(…)·La` (`LRC/DataDIVDefs.lean:83`).
- [R] `adm7` (`Formalism/SharpRestriction/Divisibility/LocalQuadraticParts.lean:271`) states `log ‖PtL‖_s² ≤ SZbP`, and bounds each kernel by `kernelPlaceMeanBound`.
- [I] So h(u) is the log-norm of the final period map plus those of the m kernels, less eigenvalue lower bounds. `height_chain_atR` (`Div/ConstantGeTwentyEight.lean:123`) has this shape.

**Remaining fields.**
- [R] `mem u` is a column chain, the columns at T, and a period map (D7:71). The prime T = T(u) satisfies:
  - `T ∈ levelPrimes`, and `T = ππ̄` with `π ≡ 1 mod QS·q·d·(g0g1)²` (D7:142–146);
  - `Tstar ≤ T ≤ (1+1/(fk))·Tstar`, where `Tstar = (Dstar/duStar)^{1/(fk)}·GamP^{−2/(fk)}` (D7:153; `LRC/DataKernels.lean:157–159`).
- [R] `host` (`LRC/DataHost.lean:39`) is the CM field E with q, d, the level primes, g0, g1, TT and T2. `what₂` (`LRC/DataRows.lean:36`) holds LL, its places (`plEq`, D7:134), and the spaces described above.
- [R] `SizeData₂` (`LRC/DataParams₂.lean:76`) holds reals `gain j w`, `F j w`, `E u j w`, `tau w` and `io w`, all zero off `supp`. From them:
  - `sz w y = 2·lw(w)·e_w·y`, where `lw = log N𝔓_w/[LL:ℚ]` (`LRC/DataArith.lean:39`; `DataParams₂:205`);
  - `sg u w = Σ_j (gainD + F − E)`;
  - `Ga = Σ_w sz w (Σ_j gainD j w − tau w)`, and `Fo` and `Ee` are formed alike (:215–222);
  - `gainD = 0` when p ∈ `drop`.
- [I] Summed over w | p, `sz` turns an exponent into a multiple of 2 log p.

## 2. The five hypotheses

**DIV.**
- [R] Family form, a clause of `LinkDIV_at`: `RR.muDual + h u − Fo ≤ MAIN u + C·|TT|·a·La + C·m·(B0+Nc)·x^{Cabs·ε}`, with `MAIN u = Σ_t (m(ph a_t − a_t·logOm) − a_t·log T(u))` (`DataParams₂:232`).
- [P] Proof chain: `linkDIVt_closedK` → `linkDIVt_of_rowsK` → `…_rowsT` → `linkDIVt_of_rowsF` (`Div/RecBridge.lean:656`) → `linkDIV_at_words` (:327). The inequality there is read off `WordFacts` (:128). `wordFacts_of_face` builds `WordFacts` from `DivClausesR` (`Div/ConstantGeTwentyEight.lean:111`), which `divClausesR_of` proves (:184).
- [R] Clause 3 of `DivClausesR` is `muCC − meanLog κ + R.hu − 2·FoOfR ≤ R.rhs`. The package supplies `R.hu − meanLog κ = h u` and `R.rhs ≤ MAIN u + …`.
- [P] `divClausesR_of` gets clause 3 from:
  - `P.base.boundsMu Formalism.DivisorInequality.boundsMu …`, where `boundsMu : BoundsMu := slope_bounds` (`Formalism/DivisorInequality/BaseLevelBoundsWithCovolume.lean:7`);
  - a perturbation `passage`;
  - `L3main : Σ_j l3 j ≤ Σ_jΣ_ρ pq_j·w_jρ·logOm + El3`.
- [R] `BoundsMu` (`Formalism/DivisorInequality/StatementObj.lean:17`), trimmed.
  - Hypotheses: R is locally `ι(μ_y)·abelian₂(μ_y)` at every prime y; `detRatio (XQ μ0) XE (ι μ0) v = κ_v^D·∏_j detRatio (XT j μ0) (XW j) (θ j μ0) v`; local indices are bounded on Tw ⊆ Sy.
  - Conclusion: `μ(R^∨) ≤ meanLog κ + Σ_j lcv(XW j)(M j)/D + 2Σ_jΣ_{y∈Tw} lw y·F_y j + LG + Σ_j(E1_j+E2_j) + E3`, where `lcv/D = −μ(M j)`.
- [I] A factorization of the metric determinant over the m lifts becomes a bound on the target's slope by the slopes of m lattices. This is where a determinant enters.
- [P] `LinkDIVt = LinkEta → DIVinN → LinkDIV` (`GlobalTheoremInputs.lean:94`). `divinN_of_hypV` (`Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:117`) proves `DIVinN` from `HypV` (the VWin bound), `LinkN` and `SmallLevelRankEq`.
- [R] `DIVinN_at` says `etaSum ≤ D0·C·x^ε·(B0+Nc)`, where `etaSum` sums `lw·e_w·etaJ` over twisted places.

**SlopesN.**
- [R] Family form, `SlopesN_at` (`GSB/QuadraticLogDerivCongr.lean:181`): `μmax(N_u) ≤ μmax(M_u) + Ga + Fo − Ee u + C·m·B0` and `μ(M_u) + Ga + Fo − Ee u − LoU ≤ μ(N_u)`.
- [P] `slopesNF_of` (`GSB/TopDensityNGeSixteen.lean:1544`) derives it from `placesF_min'` (`Formalism/LocalToGlobal/GlobalTheory/PlacesMin.lean:23`), which uses `nprimeDef`, `nuDef`, `LinkMu`, `LinkG` and `fills`. The inequalities are `slopesN_at_of` (:1529), from `HypLow`, `HypLow2` and `HypHigh` (`SWB/ClaimGaFree.lean:65–94`).
- [R] `HypLow` is the identity `muN = muMu + Sg sg' τ − BeSum len τ`, that is, μ(N_u) = muMu + Σ_w 2ℓ_w(sg'_w − τ_w) − Σ_w 2ℓ_w(len_w − du·τ_w)/du. Here:
  - `len = lenMN`, with `len_w ≤ dM(τ_w + io_w)` off T(u);
  - sg' ≤ sg is a rounding of sg, with total rounding loss at most Rd.
- [R] `HypLow2` ties muMu to M: `muMu = μ(M_u) − f·log(T−1)/(T−2)`.
- [I] So muMu plays the slope of the ramified part, and SlopesN is bookkeeping on N_u's definition. Dividing by 𝔓^{sg} adds 2Σℓ·sg, while the index of NuLat costs at most τ + io. It is not an inequality between different lattices.

**SlopeIneq.**
- [R] Family form, `Frame_at` (`GSB/QuadraticLogDerivCongr.lean:188`): `∃ η ≤ etaB, e ≤ eB, ∀ HH ≥ s − RR.muMinDual > 0: s − log|W| − (1−delp)⁻¹(4u·log(1+HH/u) + (η+4√e)·HH) ≤ RR.muDual`, where s is the rank-weighted mean of μ(N_u) − h(u).
- [P] Proof chain: `frameF_of` (`GSB/TopDensityNGeSixteen.lean:606`) with `frameRealF_of''` (:988) → `frame_at_of` (:538) → `joint_a_ramified_holds` (`SWB/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean:254`) → `flat_lattice_theorem_holds` → `theoremF : TheoremF` (`Formalism/HarderNarasimhan/ShiftInvariance.lean:61`).
- [R] `TheoremF` (`Formalism/HarderNarasimhan/StatementFrameF.lean:26`), trimmed.
  - Hypotheses: lattices N_i and a target cc, with maps satisfying `B_i(N_i) ⊆ cc` and `htMap B_i ≤ h_i`; s, u and HH as above. At one place, the normalized matrices satisfy `Σ_i ‖γ_i B_i*B_i − 1‖²_HS ≤ e·Σ rank` and `tr Q² ≤ (1+η)(tr Q)²/dim`, with `Q = Σ γ_i B_iB_i*`. The ambient dimension is at most dim W/(1−δ).
  - Conclusion: `s − log|I| − (1−δ)⁻¹(4u log(1+HH/u) + (η+4√e)HH) ≤ μ(cc)`.
- [R] The inputs come from three places:
  - `OneMapIntoCC` and the height bound, from `LinkDIV`;
  - `delp ≤ exp(−x^{ez/7})`, from `LinkIRR`;
  - near-orthogonality `InputSG` (`SWB/FrameTraceRatioFinEquiv.lean:30`), from `LinkS`, which `link_alt` produces. It says `‖K_{uu'}‖²_HS ≤ (1+η0)d_u d_{u'}/D*` and `‖K_{uu} − 1‖²_HS ≤ e0·d_u`.
- [R] `frame_at_of` returns `η = 5x^{−CH} + 3√de` and `e = 2e0`. Here de bounds the non-ramified share of the rank: `Σ(duS − du) ≤ de·Σ duS`.

**Losses.**
- [R] `Loss_at` (`GSB/QuadraticLogDerivCongr.lean:203`) says `IOsum ≤ C|TT|·m·b·x^{eL·ε}` and `Σ_t Σ_j ASK − Ga ≤ C|TT|·m·b·x^{eL·ε}`.
- [P] It is `lossF_of_7` (`GSB/LossesSmallShares.lean:308`) applied to `stLoss7 = losses_of_small_share_weight` (`Formalism/LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean:86`). That proof uses `ChosenTT`, `ChosenBadp`, `LinkG`, `loss_setting_family` (:41) and `joint_discriminant_eventually`.
- [I] The loss measures the orbit restrictions and penalties in the gain's definition (§3).

**Count.**
- [R] `Count_at` (`GSB/QuadraticLogDerivCongr.lean:167`): `Σ_j (1/f)Σ_τ log(w_jτ·v/π) + m·log(g0g1) − C(La + m²La/k) ≤ log T(u) ≤ C·m·L`, and `|log T(u) − log T(u')| ≤ C log k`.
- [P] `countF_fam` (`GSB/JointsL.lean:1152`) proves it via `count_at_of` (:20), from `TorusPairsWithVariant` and `VandermondeVariationBound` (`GSB/StandardLattice.lean:533`). Those come from `family_part_five_of_explicit_constants (division_level_prime_family Fm h2b h2v h3)` (`GSB/LinkMin.lean:425,734`).
- [R] `TorusPairsWithVariant` says: if `Xu·Γ^{−2/(fk)} ≤ T ≤ (1+1/(fk))·Xu·Γ^{−2/(fk)}`, then `|log(duStar·(T^k−1)^f/(Dstar·Γ^{−2}))| ≤ C` and `lowB − 2logΓ/(fk) ≤ log T`. The quantities (`GSB/GeneralLinearActions/GapAtLeast.lean:26–99`) are:
  - `log Xu = (1/(fk))·log(Dstar/duStar)`;
  - `Dstar = vol(Y0)·idxSig·∏_ρ dsig ρ`;
  - `duStar = mass_k·idxPi·∏_ρ dimV(weights)`, with `dimV = vand/facProd`.
- [I] So T(u) is chosen to make the number of level-T forms, duStar·(T^k − 1)^f, match the target dimension. Weyl's dimension formula then converts log(D*/du*)/(fk) into the weights.
- [R] h2b, h2v and h3 come from `siegel_mass_ratio_family`, from `volume_eq_mass_rank_two` (taking the inputs `MassRatioUnderVolume` and `GenusMassAt D 2`), and from `explicit_bound_family` (`GSB/TuSizeOfRealPlaceSecondLayer.lean:14–22`).

## 3. Where the gain comes from

- [R] `gain` is a free field of `SizeData₂` (`DataParams₂:93`). The family field `fills` (`ParConsts.lean:62`) imposes `ParametersFill` (`Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean:401`). Over a prime p that is inert or signal, it sets `gain j w = gainP X K a b p j`, `tau w = tauP`, `io w = ioP` and `wPart j t p e = fill (partner p t e)`.
- [R] `gainP` (:355) is 0 if p is inert with `hP = 0` or if p > X''. Otherwise it is `Σ_{t0∈VV} max(gU − Pr, max(g0,0)) + Σ_{t0∈reps∖VV} max(g0,0)`, where:
  - `g0 = Σ_{s∈tops t0} Σ_{e odd, not Excl} max(0, (a_s−2cG)/p^e − capU) − dl` (:247);
  - `gU = γ(p)·Σ_s(a_s−2cG) − Σ_{s not V} Σ_{e odd} min((a_s−2cG)/p^e, capU) − dl` (:254);
  - `γ(p) = p/(p²−1)` and `capU = fill(partner p s e) − kaJ j + cG`.
- [I] Since Σ_{e odd} p^{−e} = γ(p), both g0 and gU are the p-part of the ASK count, Σ_{e odd} max(0, a/p^e − partner weight), taken over Frobenius orbits and less the penalties dl and Pr.
- [R] `LinkG_at` (`GlobalTheoremInputs.lean:122`) gives two things:
  - for inert or signal w with p ≤ X'': `0 ≤ gain ≤ 4|TT|a/p`, and `Σ_jΣ_{t∈TTw}(vonMangoldtClassSum j t p − loG p) − m·flG p ≤ Σ_j gain j w − tau w`, where `vonMangoldtClassSum = Σ_{i odd} max(0, a_t/p^i − wPart)` (`DataParams₂:240`);
  - off T(u): `NuLat ⊆ 𝔓^{⌊e_w τ_w⌋}·MramL` locally, and `lenMN ≤ duS·(τ + io)`.
- [P] `LinkG` is proved by `GlobalTheory.Top.link_g` (`Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LinkG.lean:14`).
- [R] What makes the gain real is `adm2` (`Formalism/SharpRestriction/Divisibility/LocalQuadraticParts.lean:206`). For φ ∈ NuLat u and F ∈ `Mtilde(muAt w) ∩ V0(muAt w)`, it says `perCol u (muAt w) (jN φ) F = embLL y` with `y = 0 ∨ ⌊e_w·sg u w⌋ ≤ v_w(y)`.
- [R] `adm2` is a field of the DIV bridge `BridgeRowsK` (`Div/RecBridgeSel.lean:329`). It feeds `val2AllAtRF` (`Formalism/LocalToGlobal/GroupLattices/ServJointF.lean:84`), which supplies clause 1 of `DivClausesR`: the divided lattice still maps into the dual of RR.
- [P] One proof of `adm2` is `admissible_level_two` (`Formalism/LocalToGlobal/GroupLattices/AdmissibleAtGeneratorPlaces.lean:214`), using `period_geTU` and `gainLe_of_fills`. I did not check whether the path uses this proof.

## 4. Corrections to the second reading

- [R] The η of `SlopeIneq` is a frame defect (§2), not a cohomological index. Cohomology enters through `DIVinN`.
- [R] The gains are built into the definition of N_u and paid for by `adm2` (§3).
- [R] The record on the path is `LChain.SizeData₂` (§0).

## Not read

- `topDesWin`.
- The proofs of `slope_bounds`, `theoremF`, `loss_setting_family`, `places_at_of`, `link_alt` and `linkG_concrete5`.
- The inputs of `admissible_level_two`.
- The division package.
- `dl`, `Pr`, `Excl`, `FDef` and `EDef`.
- The sources of `Slopes`, `HComp`, `EComp5` and `HHBound`.
