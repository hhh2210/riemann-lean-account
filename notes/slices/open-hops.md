# Three open hops: the lift lattices, coverage of maximal ideals, inertia at S

Read 2026-11-20 from the source text only; nothing was built or edited. **read**

Paths are under `lean/src/`, with these abbreviations:
- AM = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/`
- IW = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/`
- IE = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`
- TPS = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- TC = `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/`
- HGC = `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/HeckeGaloisCriteria/`
- DV = `Formalism/LocalToGlobal/Divisibility/`
- COL = `Formalism/LocalToGlobal/Columns/`
- NFF = `Formalism/LocalToGlobal/NumberFieldFamilies/`
- LLC = `Formalism/SharpRestriction/LevelLetterCocycles/`
- PkAlt = AM/RowsRestWordColumnUnitBaseTupleAlt.lean

Tags: **read** = statement or definition transcribed; **proved-by** = proof body read, inputs named; *inferred* = my interpretation.

## Verdicts

| Hop | Verdict | What settles it |
|---|---|---|
| A | **SETTLED**, first option. `D.what₂.MtLat μ j` is the lattice of level-part algebraic modular forms on `UF E nV`, of weight `W.lamV j`, whose value at every point lies in the dual-Weyl 𝒪-lattice transported by that point's hermitian lattice. *inferred* | `MtLat μ j := (p.sL μ j).lat` (PkAlt:397); `latT : OLatTie σ s.lat j m.N` (PkAlt:64); `mL : ∀ a j, p.mL a j = mLU … a j` (AM/ReadPk.lean:80); `Nab d := nabAtr X.emb lam (L d)` with `mtVal j SG := roundPk X (W.lamV j) fun d => d.1.N` (COL/CoefCol.lean:63, :101). **read** |
| B | **SETTLED.** Coverage holds by definition, because the local indices are the maximal ideals. Only finiteness is proved, by commutative algebra over the DVR. No Galois representation is involved. *inferred* | `LocT B := Σ jw, {I : Ideal (heckeAlg0 B jw.1 jw.2) // I.IsMaximal ∧ 1 ≤ jw.1 ∧ jw.1 ≤ R.m ∧ muAt jw.2 ≠ mu0}` (NFF/NPartCNd.lean:135); `mx_all := mxC_all B0 (locsFin_of hs hd)` (IW/NonemptySpec.lean:174). **read** |
| C | **SETTLED.** Only what `AwayB` provides is consumed. The g-places of S are built to be tame, square-free and ℚ_g with g > 16a². The pde places and the places of Q fall either into that case or into the abelian (`Tor`) case. *inferred* | Consumed: `ine : Nc N A y → ∀ σ ∈ Ine, A.inePol x σ = A.inePol y σ` and `mono : Nc N A y → A.mono0 x` (TC/AutomorphicGaloisAdmissible.lean:26–27), via `RelU` (TC/TrivialLocalCondition.lean:16). Bridge: `star_guard : NcW y → (IsQpBig w y.lpDim ∧ TmW y ∧ Sqf y) ∨ Tor y` (TC/OfStar.lean:22). **read** |

## Hop A: what `MtLat` is

**Where it is set.**
- `D7.what₂ : Rows.Data R` (Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:87) has the field `MtLat : ∀ μ j, OLat O (embLL.comp OtoLL) (Mt μ j)` (Formalism/LocalRingCardinality/DataRows.lean:137). An `OLat` is a finite set `gen` that spans over ℂ; its carrier is the O-span (:7, :14). **read**
- `Stages.toD7 X := assemble …` (AM/AssembleLattice.lean:197) sets `what₂ := W.what₂` (:20). `RowsRest.what₂` copies `MtLat := W.MtLat` (AM/RowsRestWordColumnUnitBaseTuple.lean:162). On the path, W is `RowPk.W η hη := q.p.what₂ q.e q.W₀ q.n η hη` (AM/ReadPk.lean:92). **read**
- `Pk.what₂` (PkAlt:356) sets `MtLat μ j := (p.sL μ j).lat`, `MtL μ j := Fin (p.mL μ j).n → B.LL` and `jMt μ j := (p.tL μ j).j`. **read**
- No later stage changes it. **read**
  - `oL x L` reuses `P.q.W` and replaces only η and the N stage (IW/TwistDataAgreeAcrossCoefficientsLocalized.lean:50).
  - `DL_eq : DL x L = withLoc L` is `Eq.refl` (:55).
  - `setRaw` sets `what₂ := rowsEta D.what₂ η hη = { what₂ with etaJ := η, … }` (AM/NStageTrivialCharacterCoeffEqAlt.lean:11, :119).
  - `reL` keeps the W stage (slices/vacuity-flags.md).
- `exists_rowsT` (IW/ExistsRowsT.lean:28) builds a `RowsT`, the field `Bl.Built.what₂`. Despite the shared name it is not `D.what₂`, and it sets no `MtLat`. **read**

**The ties, and who proves them.**
- `Pk.tL : ∀ μ j, Tie1 σ (mL μ j) (sL μ j)` (PkAlt:230) contains `latT : OLatTie σ s.lat j m.N` (PkAlt:64). **read** Here `OLatTie σ M j N := (∀ v ∈ M.gen, v ∈ range j) ∧ ∀ x, x ∈ N ↔ ∃ c : W → 𝓞 K, j x = Σ_{v∈M.gen} σ (c v) • v` (DV/RowSideTie.lean:46). **read**
- `RowPk.mL` (AM/ReadPk.lean:80) pins `mL a j` to `mLU a j`. For 1 ≤ j ≤ m that is `lMat (famR X I hX Set.univ Xg tr).A P0 ψ0 ⟨j−1⟩ (tAll I a)` (:41), and its lattice slot is `lNab` (PkAlt:95). **read** Both ties are fields of the types, so every record on the path satisfies them. *inferred*
- Construction. **proved-by**
  - `rowPk_nonempty` (IW/NonemptyRowLiftFamilyOverColumnChoices.lean:19) fills `mL` by `rw [hpL]` (:48), and fills `PkT.hL` from `formsCoordinates_indexOfFamilyTuple_eq`.
  - `exists_pkT` chooses `sL tL` by `exists_complexification_of_definiteGroupForms'` on `mL μ j` (IW/ExistsRowLiftReadingDefiniteFormCoordinates.lean:26).
  - That theorem (IW/ExistsComplexificationOfDefiniteGroupForms.lean:163) sets `lat := M` (:172) from `exists_formsTie_oLatTie` (IW/ExistsFormsTieOLatTie.lean:209).
  - `exists_formsTie_oLatTie` also proves `(∀ y, IsIntegral ℤ (o y)) → M.carrier = j '' N`, with `gen = G.image j` for a finite ℤ-spanning set G of N.
- Its integrality hypothesis is the D7 field `O_int` (RhoDetPrimeEqMuTildeMulChiPow.lean:130). **read**
- `Read.latL` (AM/StableIffCarrierEq.lean:161) is `cast_lat (m.t.hL i t) (q.p.tL …)` (IW/ExistsReadingInMovedRowData.lean:215), that is, `latT` transported along `PkT.hL` (PkAlt:266). **read** The η identity takes `x.r.Y.latL` as an argument (TPS/EtaJLocalCompatibility.lean:33). **read**
- The local modules use the same generators. `latL B i := {x | jMt x ∈ MtLat.gen}`, and `MtSub` is the O-span of their projections (NFF/NPartCNd.lean:182, :185). **read**

**What `lNab` is.**
- `lNab := (A.fam.L i t).S.lvlNab … (A.fam.lvlA P ψ).ψ` (DV/RowSideTie.lean:88), with `lvlA P ψ = ⟨X, P, ψ⁻¹⟩` (DV/RowLat.lean:248). **read**
- `lvlNab = cutNab (lvlIdem P ψ) = cutLat (cutE …) nabLat` (DV/GoodPartHermitianSpec.lean:96, :125). **read** `nabLat := valLatF S.I S.Nab` (DV/ClassSum.lean:86) consists of the coordinates x with `I x c ∈ Nab c` for every class c (Formalism/QuotientMetricDivisors/ClassSumDualGeF.lean:15). **read**
- The class-sum datum. **read**
  - `L j τ := liftDat (A.MtCSD j τ) …` (DV/LiftLat.lean:102).
  - The family is `famR = famC = colIn3 …` (AM/IsAbsIrrCharCompIff.lean:62, :202; DV/HeckeCSDICommTrRep.lean:130), with `MtCSD j τ := Col.MtKCSD W Ch sel τ.1 (j.1+1) …` (DV/LiftLatInst.lean:83).
  - `MtKCSD j := (mtKGSD j).toCSD`, where `mtKGSD j := formGSD (mtVal W j …) (mtTyKK … j).inv` (COL/RowForms.lean:277, :304).
  - `formGSD` sets `Nab := C.Nab` (COL/ColForms.lean:72).
  - `toCSDOf` makes the classes the orbits and `Gam c` the stabiliser of a chosen representative, and sets `Nab c := S.Nab (s.rep c)` (COL/RhoEqOfSmulEq.lean:134, :145).
- `mtVal j` reads `d.1.N`, the unimodular hermitian lattice of the decorated point (COL/StdLatUnimodular.lean:68). **read** `nabAtr lam L := nabK lam (fun τ => dualFr (tauLat emb τ L))`; `nabK` moves `nabStd`, the τ-tensor product of the forms `nablaSq (𝓞 K) n (lam τ)`, to that lattice place by place (DV/CoefMod.lean:184, :196, :207, :326). **read**
- So `MtLat` is a value lattice in Gross's style: values in ∇ ℤ-forms, cut down to the (P0, ψ0⁻¹)-part. It is not the image of a theta lift. *inferred* The `T_j` and `cut_j` charged in `inEta_num` are built from this same `lvlNab` (`Tl`, slices/congruence-sha.md). **read**

## Hop B: who proves `mx_all`, and from what

**Existence on the path.**
- `lv3_of_third_alt_alt` (TPS/FinitenessOfHyp.lean:61) sets `hB := builtEx_of_published_inputs' l hP` (:70) and takes `⟨L, hL'⟩ := hB big` (:72) and `⟨Sp, ⟨Au⟩, ss⟩ := hL'` (:74). `oL x L` then replaces the bare record. **read**
- `AutomorphicSideExists … := ∀ big, ∃ L, BuiltAlt … big L`, and `BuiltAlt … L := ∃ Sp : NdSpec A.pl M C big L.X L.T, …` (TPS/ForcedByAutomorphicSemisimpleData.lean:12, :15). `NdSpec` has `mx_all` as a field (AM/RingSpecNormalisedCharacterEq.lean:275). **read**
- The chain of proofs. **proved-by**
  - `builtEx_of_published_inputs'` (TPS/FinitenessOfHyp.lean:35) is `locAll_exists_alt` (TPS/LocAllExists.lean:17).
  - That takes `Sp` from `ndSpec_exists_alt` (TPS/NdSpecExists.lean:21), which ends with `nonempty_spec (base M C hR X hS) C hs hd hML …` (:72).
  - `nonempty_spec` (IW/NonemptySpec.lean:115) sets `mx_all := mxC_all B0 (locsFin_of hs hd)` (:174).
- `mkX` sets `Loc := LocT B0` and `locs := locsC B0 (locsFin_of hs hd)` (IW/UnitsLiftSpec.lean:156, :166). **read** The η proof passes `mx_all := Sp.mx_all` to the η identity (TPS/NonGaloisEtaJMem.lean:68). **read**

**What it rests on.**
- `mxC_all … I hI := ⟨⟨(j, w), ⟨I, hI, h1, h2, hw⟩⟩, …, mxC_self …⟩` (NFF/NPartCNdTie.lean:69). **proved-by** Every maximal ideal is its own index, so coverage needs no argument. *inferred*
- What is proved is finiteness of each fibre (`LocsFin`), because `locsC` is its `toFinset` (NFF/NPartCNd.lean:149, :151). **read** `locsFin_of` (NFF/NPartCNdStd.lean:76) gets it from `NCov.finite_maximal` (Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverEta.lean:496). **proved-by**
- The algebra is `heckeAlg0 B j w := adjoin (Oc j w) {hK j w v k | GenAt0 …}` inside `End_{Frac Oc}(V j w)`. Oc is a complete DVR finite over ℤ_ℓ (NFF/NPartCNd.lean:27–35, :131). **read**
- How finiteness is proved. **proved-by**
  - `finite_maximal` applies to commuting operators on a finite-dimensional space, split, with eigenvalues in O.
  - Each maximal ideal is `cls ψ` for an O-point ψ with a non-zero eigenspace (`exists_pt_of_isMaximal`, CoverAlg.lean:334).
  - These ψ index independent subspaces, so there are finitely many (`exists_finset_pts`, :217).
- The hypotheses, read as statements only (TPS/NdSpecExists.lean:28, :38, :42–43). **read**
  - `hs` comes from `heckeStandardFacts_on_localisation_base` under `HeckeStdPlain`: split-place Hecke operators preserve the type space, commute, and have eigenvalues integral up to ℓ-prime denominators (Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverStd.lean:9).
  - `hd` comes from `finiteDimensional_localisation_space_all`, stated for every `LocBase0`.
  - Splitting comes from enlarging O until it contains every Hecke eigenvalue.
- `GlobalArtinReciprocity` and Chebotarev enter `ndSpec_exists_alt` only through the twist characters (`hGal`: ramified exactly at Q, trivial above ℓ). **read** They play no part in `mx_all`. *inferred*

## Hop C: inertia at the places of S

**What the bound needs.**
- `CutCoreUnit.main` (IE/GlobalCongruenceCountOfRootDifferenceUnit.lean:44) assumes `∀ v ∈ S i, (QuadAt v ∧ IsUnit (zeta i v − 1)) ∨ PolyAt π v` and `∀ v ∈ Q i, QuadAt v ∧ zeta i v ≠ 1`. **read**
- The two conditions are defined in `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GlobalCore.lean` (:56, :61). **read**
  - `QuadAt v`: `(r_x γ − 1)(r_x γ − χ₁ γ) = 0` for γ in inertia at v.
  - `PolyAt π v`: for some P over T, `P(r_x(gam0 v))·(r_x γ − χ₁ γ) = 0` and `P_π(ζ_v)` is a unit.
- The suppliers are `TheoremFiveAtS.main_alt_alt` (TPS/ImportsExtraExtra.lean:10) and `QuadAtQ.main_alt_alt` (TPS/ImportsExtraRest.lean:10), called at TPS/AdmissibleParameterEventually.lean:48–49. **proved-by** Both use only `galois_condition_five_of D i r hF.Conclusion2.1` and `TameDesign.main`. PolyAt is used over g₀ and g₁; QuadAt over pde (pde′ when ℓ = pde) and at Q. **proved-by**
- `galois_condition_five_of` discards the third conjunct of `ConclusionG5` (`obtain ⟨ha, hb, -⟩`, LLC/JointConditionsZpowers/GaloisConditionFiveExtraOf.lean:38). **read**

**Design of S.**
- `S i := (exceptional_places_finite D.host (lOf B0 i)).toFinset` (IW/UnitsLiftSpec.lean:196). Here `exceptionalPlaces l := {v | (v over g 0 ∨ v over g 1 ∨ v over (if l = pde then pde' else pde)) ∧ v not over l}` (NFF/NPartCNd.lean:17). **read**
- g₀, g₁, pde and pde′ are level primes, totally split in E (`g_split`, `pde_split`, Development/AbelianVarietyTheory/Definitions/Foundations/AuxiliaryFrameNormalizedSpaces.lean:23, :25). **read**
- `big_of_le_nV : n ≤ nV → 16 n² < g k` (Development/DiscreteGroups/GlobalIrreducibility/DzBigDef.lean:28) follows from `g k ≡ 1 mod QS·q·d`, `QS ≥ 16`, `n ≤ q` and `n ≤ d`. **proved-by** I found no such bound for pde. *inferred*
- `TameDesign.main` (IE/TameDescentConditionsEveryLocalisation.lean:137) shows χ₁ is trivial on wild inertia at every place of S ∪ Q. The twist characters force this (:81–131): on inertia they have order dividing 15 at the δ-places, are tame at the g-places, and are unramified elsewhere. **proved-by**
- `galois_condition_five_extra_of` (GaloisConditionFiveExtraOf.lean:116) adds four facts. **proved-by**
  - `gam0` is a tame generator.
  - χ_c = χ₁ on inertia.
  - ζ_v ≠ 1 at the places of Q.
  - ζ_v − 1 is a unit over pde, because χ₁(gam0) has order exactly 15 (:153) and Φ₁₅(1) = 1.

  None of this uses a Galois representation. *inferred*

**The compatibility clause consumed.**
- `ConclusionG5` (LLC/SumRepresentations.lean:243) is supplied by `prvG5_of_admissible_cutRec` (TPS/AdmissibleJOfRestricted.lean:28), installed at TPS/CFacts.lean:52. **proved-by** Its Galois–automorphic input at S ∪ Q is `hLGC := lgc_of_cut'_alt D hA.1.1 hC` (:31). **read** The residual conditions use `adm6` over g and `EigPd` over pde; `EigPd` is built from `hA.1.1`, `hLGC` and `RbEx` (:32), and I did not read its proof. **read** Local Galois cohomology enters as `HOneTwo` (:33). **read** Whatever `EigPd` uses comes from `hA.1.1` and `hLGC`, whose compatibility away from ℓ is `RelW`, so the verdict does not depend on it. *inferred*
- `lgc_of_cut'_alt` (TPS/LgcOfCut.lean:12) proves `LGCatN` (TC/TrivialLocalCondition.lean:27). **proved-by**
  - `LGCatN … w := ∀ x, ∃ P, ptV i P = some x ∧ RelU (wdOf (r x) w) (lpTw (locV i P w) ((1−nV)/2))`.
  - `RelU` is `RelW` plus `Nc` (:16).
  - The `RelW` comes from `isoRep` (TC/GoodRCongr.lean:288), that is, from `AutomorphicGaloisAdmissible`.
- The consumers read only `hP.ine` and `hP.mono` (TC/Bridge.lean:51, :162–163). **read** They are `SplitI_of_TY` (Q and pde, :147) and `exists_inertia_charpoly_factor_of_tame_type` (g-places, :130), reached through `galois_clause_of_sufficient_alt` (TPS/GaloisClauseOfSufficient.lean:94). **read**
- Their remaining inputs are `MonodromyInertiaType` (LLC/SumRepresentations.lean:311), which gives the shape of the automorphic local parameter; Chebotarev; and `TieGal` (:69). **read** `TieGal` lists properties of the local Weil–Deligne functor and none of its clauses relates an automorphic parameter to a Galois one. **read**
- `Nc y := Tm y ∧ mono0 y ∧ Sqf y` (TC/AutomorphicGaloisAdmissible.lean:21). **read** `Sqf`: any eigenvalue z of a tame generator with multiplicity ≥ `thr w (lpDim y)` satisfies z^(Nw−1) = 1 (:18). **read** `thr w n = 2` if w lies over a prime p that is totally split in E with n = 1 ∨ 16n² < p; otherwise `thr w n = 1` (TC/Transported.lean:11). **read**

**Nc is proved at S.**
- Over pde and pde′, and at Q: `nonCritical_localParam_of_full_dim` (TC/NonCriticalLocalParamOfFullDim.lean:12) takes mono0 and the inertia polynomial (X−1)^r (X−χ₁ σ)^t from `MonodromyInertiaType`, and tameness of χ₁ from TameDesign. Every inertia eigenvalue is then 1 or χ₁(γ), and χ₁(γ)^(Nw−1) = 1. **proved-by** So `Sqf` holds at either threshold. *inferred*
- Over g_k: `CutRec` (HGC/RhoBar.lean:12) is `cutRec_cut hc := hc.nice …` (HGC/Tie0CutOfTie0.lean:164). **proved-by**
  - `nice` comes from `nc_of_type` (TPS/ExistsGood.lean:47; HGC/ExistsUnitOneAddGenerator.lean:143), which calls `nc_of_label` (TC/CardRootsBar.lean:92), which calls `nc_of_roots`.
  - `nc_of_roots` rewrites with `thr_split (g_prime k) hw (g_split k) (big_of_le_nV D k hle)` (:82).
  - The type labels are square-free of degree r and have no root at χ_J^{±1} (`tuple_labels`, HGC/ExistsUnitOneAddGenerator.lean:126). So only the χ₁ eigenvalue repeats, and it is a (g_k−1)-th root of unity.

**From Nc to AwayB.**
- `AwayB x y` (TC/WeightsConjBis.lean:26) has three fields. **read**
  - `dim`.
  - `tor : Tor y → y.mono0 → x = y` (:29).
  - `tame0 : IsQpBig w y.lpDim → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g, deg g = 0 → x.charPol g = y.charPol g` (:31).

  `IsQpBig w n` means E_w ≅ ℚ_g continuously with n = 1 ∨ 16n² < g (:15). **read**
- `star_guard` (TC/OfStar.lean:22) sends `NcW y` to the big case when `thr = 2`, and otherwise to `tor_of_ncW` (TC/PowEqOneOfRoots.lean:51). **proved-by** In the second case every eigenvalue of the tame generator is an (Nw−1)-th root of unity, so the generator commutes with Frobenius and every commutator acts trivially (`Tor`). **proved-by**
- `aw_of_away` turns `AwayB` into `Aw` via `away_nice` (OfStar.lean:37, :43). `isGalU_of_props_alt` builds every `away` field this way (TPS/SOfStar.lean:33). `nc_iff : Nc ↔ NcW` and `relW_of_aw` then carry `Aw` to `RelW` (TC/InePolOfUnr.lean:34, :47). **proved-by**
- Hence the g-places of S sit exactly in the tame, square-free, ℚ_g, g > 16a² case. The pde places and Q use `tame0` when big and `tor` otherwise. *inferred* This chain consumes no local–global compatibility beyond `AwayB`. *inferred*

## Not read

- `goodR_fold` and `halfTwist`: how the `RelW` of each constituent gives the `RelW` of the isobaric sum, including that `Nc` of a sum gives `Nc` of each summand (`sqf_sum` read as a statement only).
- `rep_conj`, `exists_isCompl_finrank_inertia_of_charpoly`, `weil_deligne_clause_of_split` and `mult_of_rhobar`.
- The proof of `MonodromyInertiaType` on the path.
- `admDZ`, `exists_tuple`, `goodTuple`, `inertiaCharpoly_eigenvalues`, and the published `DepthZeroInertia`.
- `eigPd_holds_alt`, `hOneTwo_of_localFiniteness_tateDuality_eulerChar` and `adm6`.
- The bodies of `heckeStandardFacts_on_localisation_base`, `finiteDimensional_localisation_space_all`, `exists_padicFiniteExt_containing_all_hecke_eigenvalues`, `heckeStdPlain` and `exists_pt_of_isMaximal`.
- Who fills `NData.g_split` on the localised record.
- `exists_lat` before its final lines, and `formsCoordinates_indexOfFamilyTuple_eq`.
- Whether a stage after Has4 rebuilds the W stage (carried over from slices/vacuity-flags.md).
