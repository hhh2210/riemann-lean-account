# The junction: congruence ideals, Sha lengths, and the lift lattices

Read 2026-11-20 from the source text only; nothing built. Continues `slices/main-term.md` §4 and `slices/vandiver.md`. Paths are under `lean/src/`:

- GTI = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`
- DN = `Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean`
- QH = `Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean`
- IE = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`
- TPS = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- HGC = `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/HeckeGaloisCriteria/`
- TP = `Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean`
- DV = `Formalism/LocalToGlobal/Divisibility/`
- BS = `Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/BaseSizes.lean`

Tags: **read** (transcribed), **proved-by** (proof body read, inputs named), *inferred*.

## Direct answers

1. η_j is the normalised log-index of cut_j in T_j at the twisted places. Here T_j is the orthogonal projection of the lift-level-j lattice onto a Hecke-stable subspace Z of its theta-lift block, and cut_j is the lattice's intersection with Z. So T_j/cut_j is the congruence module of that part. **read**
2. `LinkN` is proved by a Ribet-type bound on the Hecke algebra T of each localised lift lattice. Take an eigensystem π whose parameter contains the Speh block (μ, t), and let I be the congruence ideal between π and the eigensystems without that block. Then v_ℓ(I) ≤ len Sel(ρ_πχ₁⁻¹) + Σ_{0<e<t} shaLen(E, ℓ, e) + v_ℓ(h_E) + t·Σ_Q v(ζ_q − 1). **proved-by**
3. The mechanism is a determinant (Fitting-ideal) lemma in the algebra spanned over T by Galois images. It bounds the congruence ideal by the lengths of modules of cocycles valued in ρ_πχ₁⁻¹ ⊗ K/O and in K/O(−e). The e = 0 cocycles are unramified everywhere, so Artin reciprocity bounds them by v_ℓ(h_E). The e ≥ 1 cocycles are unramified outside ℓ and coboundaries above ℓ, so their ℤ_ℓ-coordinates lie in Sha(E, ℓ, e). **proved-by**
4. Local triviality above ℓ is a hypothesis of the cocycle bound. It is supplied by a crystalline analysis valid for large ℓ (`UseLoc.main`). **read**
5. e runs over 1..t−1 because the Galois side of the Speh block is χ₁, χ₁ε⁻¹, …, χ₁ε^{−(t−1)}. The length t = `Ranks.t` is the rank step of every lift, and the lift index j only moves the centre of the weight segment. **read**
6. Galois representations are needed, for every eigensystem whether lifted or not, so the argument is not abelian. They come from `AutomorphicGaloisAdmissible`, which rests on the literature fields `CuspUAlt` and `CarUAlt`. **read**
7. `HypV` is used, but only in the form "Sha sum ≤ b": the square root is thrown away. The per-lift slot is D0·C·x^ε(B0 + Nc) with B0 = f·m·b·x^ε, and √b fills at most a fraction e^{−x^ε/2}/(f·m·x^{2ε}) of it. **proved-by**
8. Three arguments are passed and never used: `GoodR` and "π ∈ Z" in the core bound, and the `LinkEta` premise of `LinkDIVt` on the used route. **read**

## 1. The statements (step 1)

**η.** The definitions (GTI:36; `Formalism/LocalRingCardinality/DataArith.lean:39`):
```lean
def etaSum (L : SizeData₂ D) (j) := ∑ w ∈ L.supp.filter (fun w => muAt w ≠ mu0), lwP w * ramIdx w * etaJ j w
def lw (w) := Real.log (Ideal.absNorm w.asIdeal) / finrank ℚ K
```
**read**

`etaJ` is fixed by two ties. **read**
- `D7.etaJ_tie : etaJ j w = ∑ i ∈ nd.locs j w, nd.etaLoc i` ties it to Hecke modules (`Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:283`).
- `NumTie.etaJ` ties it to the lattices: `etaJ (i+1) w = A.fam.etaJ … w` at a twisted w, and 0 elsewhere (DV/RowSideTie.lean:244). Here `A.fam.etaJ = lenUW w Tl cutZ`, a length divided by e_w (DV/LiftLat.lean:118,147).

Hence η_j = [LL:ℚ]⁻¹ Σ_{w twisted} log N(w)·len_w(T_j/cut_j). **proved-by** This follows by unfolding `lenUW = lenW/eW` (`Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean:94`). The factor `lwP·ramIdx` only undoes the normalisation by e_w. *inferred*

**T_j and cut_j** (DV/RowLat.lean:142–157):
```lean
def Tl   := matLat (Pq ℓ Z * vPr ℓ * S.lvlE r P ψ) (S.lvlNab r P ψ)  -- Pq = orthPr (HV) onto Z0
def cutZ := cutLat (fE ℓ Z) S.nabLat                              -- {z | fE z ∈ nabLat}
def HZ   := zEᴴ * HV * zE                                           -- the Hermitian form on Z
```
**read**
- Z = `Zs.Zl j t` is a chosen subspace with `Zs.InBlock`. `inBlock_lifts` (DV/RowLatLemmas.lean:654) puts it inside the block part `ZH := Col.blockSum B.n B.q B.t B.bl B.op` (RowLat:85), the forms whose Hecke polynomial contains the length-t block factor. **read**
- So T_j = π_Z(L) and cut_j = L ∩ Z, and T_j/cut_j is the standard congruence module. *inferred*
- `BoundsIVAt` (DV/LiftLat.lean:208) states `jT ≤ etaW + dZ·(JexpW + vw DG + vw s)`, where `jT = jw HZ w Tl` is the discriminant index of HZ on T_j. **read** So the discriminant at w is bounded by the congruence module plus level terms.

**The links** (GTI:40–62; `Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:10`; `…/CharacterBoxes/ExistsPageN.lean:12`):
```lean
vvTerm D l := if l.Prime then (∑ e ∈ Ico 1 D.R.t, shaLen l e) * log l else 0
LinkN_at L j C := Summable (vvTerm D) → etaSum L j ≤ dZ0 j * (C*(f*m*b*L^2 + log x^2 * Nc) + ∑' l, vvTerm D l)
LinkN Fm := ∃ C x0, ∀ x ≥ x0, ∀ i, ShaFinOdd (D x i) → ∀ j ∈ lifts, LinkN_at (L x i) j C
SmallLevelRankEq Fm := … ∀ j ∈ lifts, dZ0 j = what₂.D0
DIVinN_at L j C := etaSum L j ≤ D0 * (C * x^eps * (B0 + Nc))
HypV Fm := ∃ x0, ∀ x ≥ x0, ∀ i, VVle (D x i).host.E (D x i).R.t (√b)
VVle E t B := ∀ Ω ld, (∀ p e, 0<e → e<t → shaLen (ld p) e ≠ ⊤) ∧ ∀ S, ∑ l ∈ S, log l * ∑ e ∈ Ico 1 t, shaLen (ld l) e ≤ B
```
**read**
- `Sha D e` is `Sha1 (qzTw D e)`. These are the classes in H¹(G_S, ℚ_ℓ/ℤ_ℓ(−e)) over E that are trivial at every place above ℓ; S is the set of those places. `shaLen` is the ℤ_ℓ-length (`Formalism/GaloisCohomology/Statement.lean:54–78`). **read**
- `InEta` (DV/LiftLat.lean:251) is `∑ w ∈ Tw, lw w * etaJW j w ≤ bd j * dZ`, with `bd = divSize = C·x^ε·(B0+Nc)` (DV/TwistedPlaceEtaSumLeExtended.lean:315). **read**

## 2. Who proves `LinkN`, and the congruence statement (step 2)

**2a. The objects** (`NData`, DN:55). **read** Each local index i carries:
- a prime ℓ_i, a lift index j_i, a twist μ_i, and a place w_i of LL over ℓ_i with μ(w_i) ≠ μ0;
- a DVR O_i finite over ℤ_ℓ, and a finite set X_i;
- a local subalgebra T_i ⊆ O_i^{X_i}, generated by the Hecke operators hT(v, k) at split v ∉ S_i ∪ Q_i with v ∤ ℓ and k ≤ nV (`T_gen`, DN:148);
- a free O_i-module Mt_i on which T_i acts faithfully (`act_inj`, DN:113);
- characters χ_c = χ₁·ε^{−(c−1)} of G_E for 1 ≤ c ≤ t, where E is the host CM field (`chi_def`, DN:126).

`prMt`/`prMt_lat` carry the lift lattice `MtL μ_i j_i` onto Mt_i along `embK i : LL → Frac O_i`. **read** So Mt_i is that lattice completed at w_i. *inferred*

T_i is a Hecke algebra in spectral form: O-valued functions on eigensystems. It is neither an endomorphism algebra of forms nor a group ring. *inferred*

Z_i (`ZN`, DN:1292) is the set of eigensystems that have an automorphic point whose isobaric parameter contains the part ⟨1, μ_i·η⁻¹, t⟩, the Speh block. **read** These are the theta lifts. *inferred*
```lean
ccIdeal T Z := ker (T → ∏_{y ∉ Z} O);  ccAt T Z π := (ccIdeal T Z).map (eval π)          -- DN:25,29
vcc i π := lenUnit l (O ⧸ ccAt (T i) (Z i) π)                                          -- DN:224
etaLoc i := lenUnit l (MtUp ⧸ MtLow);  MtUp = V_Zgood ∩ (L + V_Zgoodᶜ),  MtLow = L ∩ V_Zgood  -- DN:212–219
```
**read** vcc(π) measures how deeply π is congruent to the eigensystems outside Z, normalised so that v(ℓ) = 1. *inferred*

**2b. From η to congruence ideals.**
- `adm1` (TP:133) states `etaLoc i ≤ ∑_{π∈Zgood} mult π · (vcc π + v_ℓ|G|)`. **read** `EtaPassage.main` (IE/ImportsTerMore.lean:11) proves it from an endomorphism α commuting with T that acts by |G| on the Zgood eigenspaces and by 0 on those of Z∖Zgood. **proved-by**
- `etaAt_le` (`Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean:57`) uses Σ mult ≤ dZ0 (`adm2`, `adm3`) and Σ_{w|ℓ} lwP·e_w ≤ log ℓ (TP:276). It gives etaAt(j, ℓ) ≤ log ℓ·dZ0_j·U(ℓ). **proved-by**
- `etaSum_le` (same file :558) gives etaSum ≤ dZ0(6 + nuBudget + log h_E + log|G| + Σ log ℓ·lamG(ℓ)) + dZ0·Σ'vvTerm. **proved-by** The Sha term VV(ℓ) = Σ_{1≤e<t} shaLen passes straight into Σ'vvTerm.
- `stmtU_holds` (`…/LevelLetterCocycles/ExportBoundOfAdmissible.lean:1141`, using `etaSum_le` at :1032) produces the shape of `LinkN_at`. **proved-by**
- `linkN_of_gd` (HGC/LinkNOfGd.lean:38) moves the bound from the "cut" data back to the original at an extra cost of dZ0·log|G|, through `etaJ_le` (HGC/IsHeckeGaloisIff.lean:73). **proved-by**
- `KillAt` (`…/JointConditionsZpowers/CommutingEndomorphismCondition.lean:45`) bounds the ρ-Selmer term by an invariant `nuL` plus 1/ℓ², and bounds t·Σ_Q by 1/ℓ². **read** It is supplied by `chosenTwist_annihilates_selmerGroups`, through the choice of twist. **read**

**2c. The core statement.** `CongBound_at` (BS:87):
```lean
∀ i, lStar < l i → (∀ k, l i ≠ g k) → l i ∉ Exc L → WeightTie D i → HG nd naut i →
∀ r, GoodR nd i r → ∀ π ∈ nd.Z i, ∀ ρ, IsRankRPart D i (r π) ρ →
  vCC D i π ≤ sPi D i π ρ + shaSum D i + vClass D i + epsQ D i
-- shaSum = ∑ e ∈ Ioo 0 t, shaLen (ldat l) e;  vClass = v_l(h_E);  epsQ = t·∑_{P∈Q} v(ζ_P − 1)
```
**read**
- `IsRankRPart` (BS:57) says r_π ⊗ K ≅ ρ ⊕ ⊕_{c=1}^t χ_c. **read**
- `sPi` (BS:71) is the length of a Bloch–Kato Selmer group of ρ ⊗ χ₁⁻¹ with values in (K/O)^r (`selPi`, QH:380). **read**
- It is proved in `NLinkE.main_alt_alt` (TPS/AdmissibleParameterEventually.lean:30) by `congruenceBound_extended_of_rationalBound ∘ globalCongruenceCount_of_rootDifference_unit`. **proved-by**
- The second of these is `CutCoreUnit.main` (IE/GlobalCongruenceCountOfRootDifferenceUnit.lean:44). Its conclusion is `vcc i π ≤ sPi + ∑_{0<e<t} shaLen l e + v_l(h_E) + t·∑_{q∈Q} lenUnit(O ⧸ (ζ_q−1))`. **read**
- Medium primes use the same shape with extra local terms (`StarAD`, `CommutingEndomorphismCondition.lean:132`). **read** That proof was not read.

**2d. How the bound is proved.**

*(i) The congruence ideal is bounded by cocycles* (`CutDetOrd.main`, IE/LengthHeckeValueIdealLeDeterminantBound.lean:59). **proved-by**
- A is the O-algebra spanned over T′ = T[rr₁..rr_t] by the maps x′ ↦ r_{p(x′)}(γ). T′ is free of rank t! over T (`IsOrthogonalIdempotentDecomposition`, `Formalism/SharpRestriction/LevelLetterCocycles/IdempotentChoiceDepthZero.lean:18`). **read**
- The cocycle generators are `yg γ = χ₁(γ)⁻¹·r(γ)·Eel − Eel` (QH:551). Eel projects onto the χ₁-line, up to a scalar del. **read**
- At π′, A acts block-diagonally through surjections ψρ : A → M_r(O) and ψχ_c : A → O. **read**
- At each x ∉ Z, `NoChiOff` says χ₁⁻¹r_x has no invariant vector, so some yg(γ)(x) is non-zero (`exists_ne_zero`, :37). **proved-by**
- So for any relation tuple θ ∈ Rel, the generic determinant vanishes at every point over X∖Z. **proved-by**
- That determinant lies in T′ by `CharpolyCoeffsInSubalgebra` (QH:431). Its value at π′ therefore lies in the congruence ideal (`value_mem_ccOff`, :15), and there it factors into block determinants. **proved-by**
- The determinant lemma (IE/DeterminantLemmaDiscreteValuationRingQuotientLenStatement.lean:6) then applies. If every coefficient of ∏_j det(Σ_k X_k ψ_j(θ_k)) lies in I, then len(O/I) ≤ Σ_j len{w : Σ_q ψ_j(θ_q)w_q = 0 for all θ ∈ Rel}. **read** Its proof was not read.
- `length_sol_le` (IE/LengthHeckeQuotientLeCocycleSpanDeterminant.lean:77) turns each solution module into cocycles γ ↦ φ(yg γ), using Baer's criterion for K/O. These are `cocRho` and `cocChi c` (`Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GlobalCore.lean:39,41`). **read**
- Conclusion: len(O/ccOff) ≤ len(cocRho) + Σ_{c<t} len(cocChi c). **read**

In words: the χ₁-line of r_x is not Galois-stable, but it becomes stable modulo the congruence. The amount by which it fails to be stable is a cocycle in Hom(χ₁, the other constituents). *inferred*

*(ii) Each piece* (body of `CutCoreUnit.main`). **proved-by**
- The ρ-part is bounded by the Selmer length s. Above ℓ its local cocycles lie in H¹_f, away from ℓ they are unramified (`LocalGlobalSelmer.main`), and its coboundary module has length 0. **proved-by**
- For each c the ramification at Q is peeled off first, at a cost of Σ_Q len(O/(ζ_q−1)) (`Cut.Peel.main`). **proved-by**
- At S the classes are unramified by `QuadAt` or `PolyAt`, and elsewhere by `UnrOut`. **proved-by**
- c = 0 is the trivial character χ₁χ₁⁻¹, and its class is unramified above ℓ too (`Z1urD`). `UnramHom.length_le_classNumber` with Artin reciprocity gives length ≤ len(O/ℓ)·v_ℓ(h_E). **proved-by**
- c ≥ 1 is `ShaBound.main` (IE/LengthCyclotomicBlockCocyclesLeSha.lean:372): `len_O C ≤ lenCob C + len(O/ℓ)·shaLen(ldat ℓ, c)`. **read**
- Its proof picks a ℤ_ℓ-basis of O, so that K/O ≅ (ℚ_ℓ/ℤ_ℓ)^{[O:ℤ_ℓ]} with G_E acting by cyc^{−c}. **proved-by**
  - Each coordinate cocycle lies in Z¹. It vanishes on inertia off ℓ, so it is inflated from G_S. On each decomposition group above ℓ it is a coboundary (`LocTriv`, :206; `cob_of_bridge`, :333).
  - So it defines an element of Sha (`mk_mem_Sha`, :273), and the kernel consists of coboundaries.
- The coboundary modules have length 0 because del = ∏_{c≥2}(χ₁(g₀) − χ_c(g₀)) is a unit. Here g₀ lies in inertia above ℓ and cyc(g₀) mod ℓ has order ℓ − 1. **read** That is why this route needs ℓ large. *inferred*

*(iii) Why the classes are locally trivial above ℓ.* `UseLoc.main` (IE/AdmissibleOfLargeResidueChar.lean:24). **read**
- Hypotheses: ℓ ≥ 5; ℓ is not one of the host's small primes and is neither q nor d; position conditions on the Hodge–Tate weights mod ℓ.
- Conclusions: the local cut cocycles of χ_c for 2 ≤ c ≤ t are coboundaries (`BD`); those of χ₁ are unramified; those of ρ lie in H¹_f.

The Bloch–Kato input is `blochKatoTop_of_localTateDuality_eulerChar`. **read** The mechanism: lattices in a crystalline r_x give crystalline extension classes, and H¹_f(ℚ_ℓ(−e)) = 0 for e ≥ 1. *inferred* `TBAt` (QH:171) states this property as a definition, `0 < e → divisibleCocycles ⊓ HfD ≤ BD`. **read**

**2e. The twists.**
- `chiRatO c = χ_c·χ₁⁻¹ = ε^{−(c−1)}` (QH:283; `chiRatO_apply`). So piece c carries H¹(G_E, K/O(−(c−1))), with e = c − 1 ∈ [1, t−1]. **read**
- The t comes from the Speh part ⟨1, μ·η⁻¹, t⟩ (`muPart`, DN:1255). **read**
- In `WeightTie` (BS:42–52), `param` prescribes the archimedean weights that the infinity type `infWt` must match: −e_j(HC) + (t+1)/2 − c for c = 1..t. **read** So j enters only through the centre of the segment.
- `Ranks` (`Formalism/LocalRingCardinality/Params.lean:6–34`) gives nV = r + t and `rankY j = r + j·t`, with t odd and t ≥ k + m + 4. **read** So t is the rank one lift adds, and it exceeds the dimension r of ρ. *inferred*

## 3. Galois representations (step 3)

- They are needed. `CongBound_at` quantifies over families r with `GoodR` (DN:1232). Such a family is continuous and semisimple, and its Frobenius characteristic polynomials equal the Hecke polynomials. **read**
- `NoChiOff` concerns r_x at the eigensystems that are not lifts, so r is needed at every x. **read**
- `CharpolyCoeffsInSubalgebra` requires the characteristic-polynomial coefficients of the whole family to lie in T′. **read**
- `CutDetOrd.main` and both its lemmas discard their `GoodR` argument (`intro … S _ hS _`). **read** The Hecke–Galois content enters through that clause of S, which `exists_globalStep_objects_of_cyclotomic_generator_inertia … hr …` builds from `GoodR`. **read** Its proof was not read.
- Where r comes from:
  - `exists_canonical_hubData_with_bounds` takes `Conclusion1.1 = provisionFortyOne` (`TPS/CuspidalGaloisUnramified.lean:19`), which asserts an r with `GoodR` at every eigensystem. **read**
  - That comes from `heckeGaloisFamilyProperties_of_admissible` with `adm2_alt = AutomorphicGaloisAdmissible` (`…/TypeConditions/AutomorphicGaloisAdmissible.lean:133`). **read** It asserts Galois representations with local–global compatibility for regular algebraic, conjugate-self-dual cuspidal π on GL_a over E. **read**
  - That in turn is produced by `galClose_alt` (TPS/SClose.lean:21) from the fields `gal : CuspUAlt` and `car : CarUAlt` of `ThetaLocalInputsAlt` (TPS/WeightsConj.lean:50). **proved-by**
  - Whether those fields are filled by the theta-lift theorem (`Row0b`) on this path was not traced. *inferred* (from `slices/galois-from-theta.md`)
- The abelian ingredients are the class-group step (Artin reciprocity) and the Sha groups of cyclotomic twists. The ρ-part and `NoChiOff` are not abelian. *inferred*

## 4. Use, not presence (step 4)

- `divinN_of_hypV` (`DivinNOfHypV.lean:117`). **proved-by**
  - `vvRecord` (:17) extracts three facts from `HypV`: `ShaFinOdd`, which discharges the premise of `LinkN`; `Summable`, the premise of `LinkN_at`; and Σ'vvTerm ≤ √b.
  - The third is weakened by `Real.sqrt_le_self_iff` to Σ'vvTerm ≤ b.
  - In `divinN_at` (:76), `linarith` closes the goal using hb : Σ' ≤ b together with b ≤ B0 and B0 ≤ x^ε(B0+Nc). So the bound is used, but only in this weaker form.
- `topDesWin` (`…/CharacterBoxes/DesWin.lean:31`) feeds `divinN_of_hypV … aN aZ` into `LinkDIVt`. **read**
- On both routes, `wire4F` and `wire4F_alt` destructure `DIVinN` and pass `hCe x hx3 i` to `inpAt_of`. That calls `inEta3_num` (`Formalism/LocalToGlobal/InpAtOf.lean:46`). `inEta_num` (DV/SumLeEtaSumNum.lean:60) then unfolds the bound into `InEta`. **read**
- `linkDIVt_of_rowsF` (DV/RecBridge.lean:656) begins `intro _ hN`, so it discards `LinkEta`. **read**
- `LinkEta` is the statement that the localised modules cover the rank of the lift lattice. Without it, nothing on this route forces `nd.Loc` to be non-empty, and toy records with `Loc = ∅` and `etaJ = 0` (`ndToy`) exist in the tree. *inferred*
- This is not a loophole. Through `etaJ_tie` and `NumTie.etaJ`, a non-zero T_j/cut_j forces non-empty local data at that place. *inferred* Who proves the two ties for the D7 used on the path was not read.
- **Numbers.** **proved-by** (`Scale` at `Formalism/LocalRingCardinality/DataParams₂.lean:27–31`; `DataArith.lean:200–204`)
  - b = exp(x^ε), a = x·b, B0 = f·m·b·x^ε, Nc = |T2|·k·b·x^{2ε}/n².
  - The per-lift slot is D0·C·x^ε(B0+Nc) = D0·C·(f·m·b·x^{2ε} + |T2|·k·b·x^{3ε}/n²).
  - The Sha term is at most D0·√b, so its share of the slot is at most e^{−x^ε/2}/(f·m·x^{2ε}).
  - The true Sha sum is about exp(x^{4ε/5}) (`slices/vandiver.md` §1), smaller still.
- Downstream, the slot reaches the divisor clause as C·m·(B0+Nc)·x^{Cabs·ε} (`LinkDIV_at` clause 7 in GTI; `DivisionPackageFace.rhs` in DV/RecBridge.lean). **read**
- The slot is sized for the other terms: local lengths at small and medium primes, nuBudget, log h_E and log|G|. Each is linear in b. *inferred*

## Chains

- `nRest` ← `final_alt_alt` (TPS/CFinal.lean:19) ← `final_of_alt` (TPS/LinkNFam.lean:75) ← `linkedAt_linkN_of_boundAtTwoThree` (:64) ← `linkN_of_boundAtTwoThree_slot` (:54) ← `linkN_of_twGood_galoisPreconditions` (:37) ← `linkN_of_gd` (HGC/LinkNOfGd.lean:38) ← `LinkFam.main` (IE/LinkNAlongFamilyOfLocalBounds.lean:10) ← `linkN_of` (`…/LevelLetterCocycles/ThetaScalarFamilyOfEigenvalue.lean:45`) ∘ `stmtF_holds` (ExportBoundOfAdmissible.lean:1160) ← `etaSum_le` (MemPrimesOverOfMem.lean:558) ← `etaAt_le` (:57) ← `adm1` (TP:133; `EtaPassage.main`, IE/ImportsTerMore.lean:11) and `Bd`/`StarE` (`Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean:17,21`).
- `Concl` (same file :124) ← `NLinkClose.main_alt_alt` (TPS/ImportsFurtherTail.lean:22) ← `localBoundZeroAtLargePrimes_of_congruenceBound` ← `CongBound_at` (BS:87) ← `NLinkE.main_alt_alt` (TPS/AdmissibleParameterEventually.lean:30) ← `CutCoreUnit.main` (IE/GlobalCongruenceCountOfRootDifferenceUnit.lean:44) ← `CutDetOrd.main` (IE/LengthHeckeValueIdealLeDeterminantBound.lean:59) + `ShaBound.main` (IE/LengthCyclotomicBlockCocyclesLeSha.lean:372) + `UseLoc.main` (IE/AdmissibleOfLargeResidueChar.lean:24).
- `HypV` → `divinN_of_hypV` (`…/CharacterBoxes/DivinNOfHypV.lean:117`) → `topDesWin` (`…/CharacterBoxes/DesWin.lean:11`) → `linkDIVt_of_rowsF` (DV/RecBridge.lean:656) → `wire4F` (`Formalism/LocalToGlobal/Wire4F.lean:15`) / `wire4F_alt` (TPS/Wire4F.lean:26) → `inpAt_of` (`Formalism/LocalToGlobal/InpAtOf.lean:14`) → `inEta_num` (DV/SumLeEtaSumNum.lean:60) → `InEta` (DV/LiftLat.lean:251) → `BoundsIVAt` (:208).

## Not read

- The proofs of the determinant lemma (`DetGen.length_quot_le_sum_length`), `BlockDetPoly.main`, `det_generic_eq_zero`, `det_generic_blocks` and `exists_homs`.
- `localCocycles_aboveEll_inCut_unitDelta`, `finiteQuotientCocycleSpans_le_continuousCocycles`, `length_cutCoboundaryModule_le_unitDelta`, `length_global_cocycles_le_sum_places_over`, `length_cocycles_le_coboundaries_add_selmer`, `LocalGlobalSelmer.main`, `Cut.Peel.main`, the inertia lemmas at S, and `UnramHom.length_le_classNumber`.
- The lemmas under `UseLoc.main`, and the position hypotheses on the Hodge–Tate weights.
- `exists_globalStep_objects_of_cyclotomic_generator_inertia`, which builds S including the characteristic-polynomial clause, and `noChiOff_and_unrOut_of_large_good_place`.
- The branches for medium primes, small primes, 2 and 3, q and d, and the generator primes (`StarAD`, `StarF`, `StarG`, `StarH`), and `TruncatedSeriesCountingIdentities.second_statement`.
- `chosenTwist_annihilates_selmerGroups`, `sum_nuL_le`, and the bound on the bracket inside `stmtU_holds`.
- `exists_good_alt` (the cut) and `exists_canonical_hubData_with_bounds`.
- Who proves `etaJ_tie` and `NumTie` for the D7 used on the path, and whether its `nd.Loc` is non-empty.
- On this route, the suppliers of `CuspUAlt`/`CarUAlt` and of `NLink.Hypotheses₂` (Fontaine B_cris, local Bloch–Kato, local Tate duality, the Euler characteristic, Bhatt–Scholze).
- `biv`/`lift_index_bound_extended`. The downstream use of `InEta` is taken from `slices/main-term.md`.
