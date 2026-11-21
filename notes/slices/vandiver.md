# How `VWin` is proved: the counts, the windows, the automorphic inputs

Read 2026-11-20 from source; build unfinished. **[read]** = definition/statement transcribed; **[proved-by]** = theorem of that type located; **[inferred]** = my reading. Paths under `src/`: `AV/` = `Development/AutomorphicArithmetic/AutomorphicVarieties/`, `DT/` = `AV/ModularityArgument/ThresholdArguments/DenseThresholdCases/`. Other relative paths without a top-level prefix (`HeightAndVanishing/`, `LayeredIsomorphisms/`, …) are under `AV/`. Lean is trimmed to its mathematical content.

**Short version [inferred].** For l = 2 and odd l in a finite set Bchi, Iwasawa theory in cyclotomic towers bounds all but ≤ R exceptional twists, which LemmaK (a crude K-theory bound) handles once the window keeps them small. For other odd l, the minus part is bounded by Bernoulli numbers and the plus part (Vandiver's side), cut into character pieces, mostly by congruences with automorphic forms on U(3) and GSp4 (§5). The largest term is exp(x^{4ε/5}); sqrt(exp(x^ε)) is slack.

## 1. The arithmetic that yields `VWin`

[read] `vwinAt_of_joint (hJ : JointWin Ct) (hc : ThmBc Ct) : VWinAt ψ Ct` (`AV/CMFieldExponentialBounds/AdmissibleOfPageN.lean:41`), with Ct = 401, t(x) = ⌊x^{401}⌋ (`:43,131-133`), applies to each field E

    vvle_of_parts (h2 : BoundedHeightTwoPlaceCondition E t B₂) (hm : VVminusLe E t Bm) (hp : VVplusLe E t Bp) : VVle E t (B₂ * log 2 + Bm + Bp)

(`AV/LengthEqAddEigen.lean:127-128`).
- [read] `BoundedHeightTwoPlaceCondition E t B := VVat 2 E t B`: Σ_{1≤e<t} shaLen(E,2,e) ≤ B (`:107-111`).
- [read] `ShaPlus D e := Sha D e ⊓ (cAct D e).eigenspace ((-1)^e)`, `ShaMinus` with (−1)^{e+1}, cAct = complex conjugation of the CM field (`:64-72`); [proved-by] `shaLen_eq_add (hl : l ≠ 2) : shaLen D e = plusLen D e + minusLen D e` (`:88`). `VVplusLe`/`VVminusLe` bound Σ_{l odd} log l Σ_e of these (`:113-125`).

[read] The inputs (`AdmissibleOfPageN.lean:110-129`): B₂ = exp(x^{4ε/5}) (`BaAt`, `AV/PrimeSetBoundDataOfPrimitiveChar.lean:32-33`); Bm = `minusBound` = 3n t² log(tN) + C Σ_{l∣o, l odd} l n² t² log(tlN)² (`AV/StmtFields.lean:69-71`), ≤ K·exp(8x^{ε/4}) as log(condF(E)·t) ≤ 2x^{ε/4} (`CMFieldExponentialBounds/minusle.lean:6-8`, `LogConductorMulHeightLeOfPageN.lean:6-8`); Bp = (condF(E)·t)^C + C·exp(x^{4ε/5}) (`HVAt`, `PrimeSetBound…:75-77`). Then

    error_terms_le_sqrt_exp_rpow : ∀ eps K C, 0 < eps → ∃ x0, ∀ x ≥ x0, ∀ u ≥ 1, log u ≤ 2 x^(eps/4) →
      exp(x^(4eps/5)) log 2 + K exp(8 x^(eps/4)) + (u^C + C exp(x^(4eps/5))) ≤ sqrt(exp(x^eps))

(`ErrorTermsLeSqrtExpRpow.lean:6-9`). [inferred] exp(x^{4ε/5}) dominates and comes from the towers of §3; since log(qd) ≤ x^{ε/4}, anything polynomial in the conductor is exp(O(x^{ε/4})).

## 2. The combining theorem and the counts

[read] `DT/HVCore.lean:18-22`:

    theorem of_four_alt (hN : LiteratureRankNHypothesis) (hK : ∃ CK, LemmaK CK) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV) : VWin :=
      ⟨B, hB⟩ := Win.thmBab_of_lemmaK … FW.ferreroWashington hK
      vwin_of_counts … hL (hB 401 _) (Odd.thmBcFree_of (ML.iv … hN.coh.uo)) h1 h2 h3 h5 (countZ X.propZ)

[read] `vwin_of_counts` takes `ThmBab K 401`, `ThmBcFree`, CountI, II, III, V, Z (`AV/HeightAndVanishing/JointWinOfCounts.lean:30-33`) through `point (sumIn h2 h5 (countVs …) countIV) (sumOut h1 hZ h2 h3)` (`:16-18`). [proved-by] `countIV : CountIV` (`CountIV.lean:39`), `countVs : … → LemmaK CK → CountVs` (`CountVs.lean:86`), `countZ : PropZ → CountZ` (`CountZ.lean:5`); `PropZ`: the trivial-character piece vanishes for l ≥ 5, e ≥ 2 even, l−1 ∣ 2e (`Counts.lean:49-51`).

**Characters [read].** For E abelian of level N with group (ℤ/N)^×/H, odd l, e ≠ 0:

    plusLen D e * eO l O ≤ ∑ χ ∈ T, (V l e (dirG χ) + loss * eO l O)      when ↑T = evenSet O H e = {χ | H ≤ ker χ ∧ χ(−1) = (−1)^e}

and minusLen likewise with parity (−1)^{e+1} (`AV/CharacterLevelBounds/ReductionToDirichletCharAnyLevelOfLe.lean:48-54`). `V l e ψ` is the O-length of the classes in H¹(G_ℚ, (Frac O/O)(ψ⁻¹χ_cyc^{−e})) vanishing on decomposition groups above l and on all inertia groups (`AV/CharacterLevelBounds/ShaFamMono.lean:17-34`, `GaloisLibrary/SelmerTransport/ConjStableShaFam.lean:94-96,167-168`); `Vlen` uses level l·N, `Vn = Vlen/length(O/l)` (`HeightAndVanishing/DirichletPrimeToLPartMulLPowerPart.lean:116-120`). [inferred] E's plus part is a sum of ψ-parts over ℚ with even coefficient character: Vandiver's side.

**Hosts and cases [read].** A `Host` is a primitive χ, ex ≥ 2, primes q1 ≡ 3 mod 8, d ≡ 7 mod 16 (`…LPowerPart.lean:148-154`), N = lcm(2^{ex+2}, cond χ)·q1·d (`:164`); `X c e` = characters mod N trivial on H with ψ(−1) = (−1)^e (`:179-192`); `Big t`: 2t+1 < q1, d, and q1, d exceed cond χ, ord χ, pK, hStar, pOne (`:185-186`). `Bchi χ` = {3} ∪ odd primes dividing ord χ·cond χ·pK·hStar·pOne; pK is the least prime ≡ 3 mod 4, ≥ 7, prime to cond χ; hStar the class number of ℚ(√−pK) (`AV/StmtFields.lean:50,59-67`). [proved-by] `cases` (`HeightAndVanishing/Cases.lean:8-12`) puts every (odd l, 0 < e < t, ψ) in one of (`…LPowerPart.lean:208-219`):

| case | condition |
|---|---|
| I | l ∉ Bchi, l−1 ∤ 2e |
| Z | l ∉ Bchi, l−1 ∣ 2e, ψ = 1 |
| II | e ≥ 2, ord(chiP l ψ) even, (l ∈ Bchi or l−1 ∣ 2e) |
| III | l ∉ Bchi, l−1 ∣ 2e, ord ψ odd, ψ ≠ 1 |
| IV | l ∈ Bchi, e ≥ 2, ord(chiP l ψ) odd |
| V | l ∈ Bchi, e = 1 |

**The counts [read]** (`HeightAndVanishing/Counts.lean:53-73`, `LayerLe.lean:16-20`):

    CountI := ∀ χ, ∃ C r₁ r₂ (primes), ∀ host h of χ with r₁, r₂ < q1, d, ∀ t, h.Big t → ∀ 0 < e < t, ∀ finite Ls ⊆ Case I primes,
                ∑ l ∈ Ls, log l * ∑ ψ ∈ h.X (c l) e, Vn ψ ≤ (N * t)^C
    CountShape P := ∀ χ, ∃ C, ∀ h t, h.Big t → ∀ l ≠ 2, 0 < e < t, ψ ∈ h.X c e, P → Vlen ψ ≠ ⊤ ∧ Vn ψ * log l ≤ (l * N * e)^C
    CountII := CountShape CaseII;  CountIII := CountShape CaseIII;  CountV := CountShape (CaseV ∧ R1 l ψ ≤ 2^(c2 ψ))
    CountIV := … l ∈ Bchi, LayerLe χ l j t B → ord(chiP l ψ) odd → ∑_{e<t} Vn ψ ≤ B + (N t)^C

In words: Case I is bounded summed over all l; II, III, V, Z per (l, e, ψ); IV by the bound B on the l-cyclotomic layers. [read] `SumOut` (l ∉ Bchi) gives (Nt)^C, `SumIn` (each l ∈ Bchi) (Nt)^C + C·B, and `PointHV` gives `VVplusLe E t ((N t)^C + C * B)` (`LayerLe.lean:27-44`). [inferred] II, III, Z need l ≤ 2e+1 or l ∈ Bchi; only Case I has unboundedly many l, hence CountI is a sum.

## 3. Windows, LemmaK, exceptional twists

[read] `AV/GeneratorCountTuples/LemmaK.lean:11-17`:

    kBound C e n D := exp((2 e n)^C * log(2 D))
    LemmaK CK := ∀ l, ∀ L totally complex containing μ_l (μ_4 if l = 2), ∀ e ≥ 1,
      H²(G_S, ℤ_l(e+1)) finite ∧ log #H² ≤ kBound CK e [L:ℚ] |disc L|

[proved-by] `lemmaK_litN_alt` (`DT/KFinal.lean:11`), from `lemmaK (hB : BOdd) …` (`AV/ModularityArgument/ClassCounting/LemmaKOfLitN.lean:28-31`); `BOdd` bounds the ℤ-rank of a span built from degree-(k+1) homology classes of GL_n(O_L) by the number of complex places (`LemmaKOfSteps.lean:11-15`). [inferred] A Borel-type rank bound on K-theory, turned into H² and then Sha via `VFormula` (`Formalism/GaloisCohomology/Statement.lean:138-141`).

[read] `ThmBab K Ct` (`PrimeSetBound…:35-49`): for X ≥ X0 and q, d with log(qd) ≤ X^{ε/(4J)} there is Y, X^{1/J} ≤ Y ≤ X^{1/2}, with, for x ∈ [Y, Y²], every E's 2-part ≤ exp(x^{4ε/5}) and, for l ∈ Bchi, the layer of degree l^{j₀} of the l-cyclotomic tower over ℚ(μ_{l·cond χ}) satisfying Σ_{e<t} shaLen ≤ exp(x^{4ε/5}). [proved-by] `thmBab_of_lemmaK (…) (hFW : FerreroWashington) (hK : ∃ CK, LemmaK CK) : ∃ K, ∀ Ct ≥ 1, ThmBab K Ct` (`AV/LayeredIsomorphisms/ThmBabOfLemmaK.lean:9-12`). [read] `FerreroWashington`: abelian K ∋ μ_l (μ_4) has r with #(Cl(K(μ_{l^n}))/l) ≤ l^r for all n (`AV/PublishedTheorems/FerreroWashington.lean:7-11`); [proved-by] `UpperTheory.V.FW.ferreroWashington` (`AV/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:104`).

[read] Mechanism (`LayeredIsomorphisms/SecondBound.lean:19-50`): `ABound l R L₀` gives a finite K/ℚ_l and s_1…s_{R'} ∈ K, R' ≤ R, with `shaInv L₁ l e ≤ R'(max(m, j₀) + c + B)` on the degree-l^m layer whenever all |s_i − e| ≥ l^{−B}; `exc` (`Exc.lean:7-9`) turns this into a set `Exc` of ≤ R twists (`FirstBound`) off which Sha grows like R(m + log_l Z); `Good η Ct Exc x := ∀ e ∈ Exc, e ≤ x^Ct → e ≤ x^η`. `window` (`Window.lean:7-9`) finds Y ∈ [X^{1/J}, X^{1/2}], J = 2^{R+2}(Ct/η)^R, with Good on all of [Y, Y²]. In `point` (`LayeredIsomorphisms/ImportsAlt.lean:9-28`), for e ∈ Exc, Good gives e ≤ x^{ε/(2CK)} and LemmaK (`klen`) bounds the base layer's H²:

    shaInv L₁ l e ≤ R(m + j₀ + c + log_l Z) + 2 exp((2n₀)^CK c₀ x^(3ε/4))

and `final` gives x^{Ct}·(C(1+log x) + 2exp(C x^{3ε/4})) ≤ exp(x^{4ε/5}) (`Final.lean:6`). [inferred] The s_i are zeros of an Iwasawa power series in the twist variable; LemmaK's exponential bound is affordable only for twists ≤ x^{ε/(2CK)}, which the windows guarantee. Summed over x^{401} twists this is the exp(x^{4ε/5}) of §1.

## 4. The minus part

[read] `PsiBound` (`AV/OddResidueBounds/ZeroMemUnrHom.lean:97-103`): for CM abelian E, odd l ∤ [E:ℚ], e ≥ 1, ψ with χ_ψ(−1) = (−1)^{e+1}: `psiLen e ψ ≤ v_O(a)`, a = N·primorial(e+2)·B_{e+1,χ_ψ}, where B_{k,χ} = Σ_{a≤f} χ(a) f^{k−1} B_k(a/f) for χ primitive of conductor f (`:79`; `GaloisLibrary/BernoulliNumbers/MapGenBChar.lean:9-29`). [proved-by] `ML.iv : PoitouTateDuality → UnramifiedOrthogonality → PsiBound` (`AV/PrimitiveFrobeniusFixed/Iv.lean:4-6`); `thmBcFree_of (h : PsiBound) : ThmBcFree` (`OddResidueBounds/ThmBcOfPsiBound.lean:295`). [inferred] The classical main-conjecture side.

## 5. Where automorphic forms enter

**Case I: U(3) [read].** `count_i_of_printed_bound_k_kato_automorphy := U3.countI (U3.corGK (propGK_of_numberU3U_of_oneCharU (numberU3U_of_prints …) (oneCharU_of_katoTwoW_rig_admI_automorphy … hKa … h3)))` (`DT/LinkedUnlE.lean:49-54`); `U3.countI` uses K = ℚ(√−pK) and primes r₁ < r₂ (`AV/UnitaryThreeGroups/CountI.lean:22-30`). The carrying statements (`DT/NumberU3US.lean:27-62`):

    OneCharU_s: K CM, GD K l e ψ, σ ∈ G_K, t = Ψσ + 1 + (Ψσ)⁻¹ with Ψ = χ_cyc^e ψ,
      (∀ ρ : G_K → GL₃(Q̄_l), Adm3U_s ρ ∨ Adm2A ρ → tr ρ(σ) ≠ t) →
      Vlen ψ ≠ ⊤ ∧ ∃ X (pairwise non-isomorphic such ρ), Vn ψ ≤ 2 ∑ ρ ∈ X, v_l(tr ρ(σ) − t)
    NumberU3U_s: K imaginary quadratic → ∃ c A, ∀ e N, p ∤ N (p ≥ 7), w ∣ p → ∃ NN : ℤ, NN ≠ 0 ∧
      log|NN| ≤ c·#Orb·(N(e+1))^A·log p ∧ ∀ l ≠ 2, p: (tr ρ(Frob_w⁻¹) ≠ eis3 …) ∧ |NN|_l ≤ ∏_ρ |tr ρ(Frob_w⁻¹) − eis3 …|_l

`Adm3U_s`: irreducible, attached to a conjugate-self-dual cuspidal automorphic representation (`IsAutCsdA`), level N, weights (e, 0, −e), plus `Unl` (`:27-29`, `DT/AfStmt.lean:29-32`). `PropGK`: one NN ≠ 0, log|NN| ≤ c₅φ([(ℤ/N)^×:H])(N(e+1))^A log p, with Σ_ψ Vn ≤ 2v_l(NN) for every l ≠ p; `CorGK` sums log l over l using two primes p, p' (`AV/UnitaryThreeGroups/KatoUse.lean:36-52`). [inferred] Ribet's method read upward: one integer serves every l, so the sum over l costs log|NN|; its size comes from counting automorphic forms (`BorelInjC`), and purity forbids tr ρ = t.

**The lifting inside OneCharU [read].** `model_upper` (`AV/UnitaryThreeGroups/ModelUpper.lean:103-111`): S.R the universal ring of 3-dimensional lifts of r0 η Ψ (ker η = G_K) with local conditions, M a graded presentation; if the weight-zero subalgebra is finite over O, `PtHyp` holds, and trDiff ≠ 0 at every point neither upper nor lower triangular, then `nrm M.len ≤ 2 ∑ f ∈ T, vl(trDiff σ f)` with T covering those points, trDiff = tr ρ_f(σ) − tr r0(σ) (`ConjStable.lean:101-103`), `M.len` the length of the weight −1 cotangent part (`:89-90`); `vlen_le : Vlen ψ ≤ M.len` (`VlenLe.lean:52-54`). Automorphy of the points is `AutomorphyUnramifiedCoefficientsAlt` (finiteness `FinA`; type-I points automorphic `AutBAlt`; type-II 2-dimensional pieces modular `LemWAlt`; `DT/AutomorphyUnramifiedCoefficients.lean:16-26`); [proved-by] `automorphyUnramified_of_litN_of_gdEnd` from `GdEndAlt` (`DT/CohInp.lean:18`; `DT/AutEnd3AltAlt.lean:20-40`: ordinary points with irreducible image are conjugate-self-dual automorphic over K). [read] No Hecke algebra appears in these statements; the automorphic side is a finite set of points. [inferred] This is the R = T step: R finite, its points automorphic, the Selmer piece bounded by the congruences.

**Kato [read].** `KatoTwoW` (`…/KatoQuadraticCharacters/SphericalDecomposition/KatoTwoW.lean:10-14`): for 2-dimensional W satisfying `Used` (det θ, ordinary of weights (e, −e), residually θΨ + Ψ⁻¹, …; `KatoTwoOfUseN.lean:11-41`) with W⊗χ_cyc^{−e} attached to a weight-(2e+1) newform, the Bloch–Kato Selmer groups of W and W⊗θ vanish (cocycles unramified away from l and in H¹_f above l are coboundaries, `AV/AutomorphicForms/BlochKatoSelmerVanishes.lean:144`). The proof runs through `twoS` (`SphAtTw.lean:16-19`) and `VanishOrdL` from `ZetaUr` (`Development/AbelianVarietyTheory/Statements/CuspidalUnitaryTwists/ZetaUr.lean:18-20`: for W attached to an l-ordinary newform, a statement `ES W A`, not read); `KatoN` (`AV/LiteratureResults/KatoEulerSystems/KatoNOfKato.lean:27-35`) was not seen on this path. KatoTwoW feeds `ptHyp_of_autB_of_lemW_of_isBase` (`DT/FPtHypU.lean:15`), giving `PtHyp`, whose field `rigid` says points have no non-trivial first-order deformations (`AV/UnitaryThreeGroups/Rigid0.lean:16-20`, `GRepresents.lean:134-135`). [inferred] `ES` is an Euler system; odd weight has no central point, so no L-value hypothesis appears.

**Cases II, III: GSp4 [read].** `countII_and_countIII_of_printsH_of_sp4In := sp4Main_alt hS … (numberSp4_n_alt …) (rigSp4_alt …) (X.corX X.lemmaX X.residual_bernoulli_nonvanishing) …` (`DT/AdjointLiftingOfCohomology.lean:33-39`). `SymplecticFourImageDense`: the deformation data are `Fin0`, `NoEnd`, and every irreducible point (`AllIrr`, `AV/SymplecticGSp4/DecompSigmaOrd.lean:180`) is a 4-dimensional automorphic representation of G_ℚ (`DT/IsAut4.lean:14-17`). `NumberSp4Alt` is the integer statement for weights (e+1, e, 1, 0) and trace `eis4 p e z₁ z₂ z₃` (`DT/AfStmt.lean:34-43`). `LemmaX`: B_{1,φξ} is an l-adic unit for odd φξ, ξ primitive of conductor 2^n ≥ f·4^{v₂(l^d−1)}; `CorX`: then unramified residual cocycles for φξ^{±1} are coboundaries (`AV/LevelCohomology/UnramifiedCocycleIsCoboundaryOfBernoulliUnit.lean:14-26,50-54`). [inferred] Washington-type non-vanishing in the 2-power tower supplies residual vanishing; one use of the 2^e in E.

**Case V: U(3) over ℚ(i) [read].** `countV_of_finiteness_duality_euler_host : ThmS6_s → … → CountV`, K the Gaussian field (`DT/CountVOf.lean:33-36`). `ThmS6Core_s`: for imaginary quadratic K and host data, some g₁ makes the weight-zero part of every universal 3-dimensional ring finite over O and every type-I point automorphic over K (`DT/ThmS6CoreS.lean:27-36`). [proved-by] `unitary_lift_of_reduced_core : ThmS6Core_s → ThmS6_s` (`DT/UnitaryLiftTheoremOfReducedForm.lean:26-27`); `ThmS6Core_s` is a component of `ends0_alt` (`DT/DnEndsTop.lean:15-16`).

**RowT and OpenImageCondition [read].** `OpenImageCondition` has one field, `galoisRepOfPolarizedPairLit : RowT` (`DT/TemperedProductOfSquareIntegrable.lean:207-208`); `RowT := Row0b (fun h rc => IsRecT h rc)` (`AV/ModularityArgument/AutomorphyLifting/WeakOfAtt.lean:47`). The `*_of_open` theorems read return in-tree proofs without the field (e.g. `elliptic_main_theorem_cm_of_open O := ellipticMainTheoremCM_holds`, `:209-210`). RowT is the field `gal` (`DT/TopMainZj.lean:47`), feeds `katoTwoW_of_printsH` via `rowOf' …litN.aut.gal` (`DT/KatoTwoWOfPublishedH.lean:48-49`) and the GL₂ construction of §6. [inferred] Nothing about open images: it is the Galois-representation theorem for CM fields.

## 6. `HypothesesH'` and "patching"

[read] `HypothesesH'` extends `Hypotheses'` = {litN, ClozelCohC, ClozelConjC, BorelInjC, GaloisRepExistsTotallyRealGL2, StrongMultOneReal, GelfandKazhdanReal, AdmissibleReal, QuadBC0, NewformRep} by {DescWeak, CycC, Desc2, DefQuatExists, CuspSemisimpleReal} (`DT/AutomorphicFormHyp.lean:12-22`, `DT/AfDesc.lean:17-22`); none names a Hecke algebra or Selmer group. `BorelInjC`: cohomological cuspidal π with U-fixed vectors number at most a cohomology dimension (`AV/PublishedTheorems/GelfandKazhdanReal.lean:39-43`). `DescWeak`: regular algebraic conjugate-self-dual cuspidal π on GL_n (2 ≤ n ≤ 4) over CM E descends to a unitary group (`AV/ModularityArgument/CuspidalDescent/DescWeak.lean:10-19`); [proved-by] `UpperTheory.V.Z.Tf.SR.descWeak` (`AV/ModularityArgument/TraceFormula/SplitRigidity/HasOfSplit.lean:29`, via `runTh`).

[read] `published_hypotheses_from_patching_alt` sets `galR := galois_rep_exists_totally_real_rank_two_of_base_change hN quadBC2 admissibleReal` (`DT/PublishedHypothesesFromPatching.lean:98-103`), whose proof takes infinitely many CM quadratic K/F where π base-changes, gets r_K from RowT, and applies `galois_rep_patching_infinite_family` (`DT/SVPatch.lean:103-133`): a continuous semisimple ρ of G_F with ρ|G_K ≅ r_K for cofinitely many K (`PositivityTheory/…/GaloisRepPatchingInfiniteFamily.lean:12`). [inferred] "Patching" glues Galois representations of Hilbert modular forms (Taylor, Blasius–Rogawski); the Taylor–Wiles-type content lies in `ThmS6Core_s`, `AutomorphyUnramifiedCoefficientsAlt` and `model_upper`.

## 7. Every l and e?

- [read] `VVle E t B` bounds Σ_{l∈S} log l Σ_{1≤e<t} shaLen for every finite S (`Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:12-17`); terms are non-negative, so at an admissible x each Sha(E, l, e), e < x^{401}, is finite and bounded. Nothing is averaged over l or e.
- [read] Scales are restricted: `VWinAt` asserts the bound only for x ∈ [Y, Y²], Y ∈ [X^{1/J}, X^{1/2}] given for each X ≥ X0 and each (q, d) in `WinPair` (`ExistsPageN.lean:44-47`); Y comes from `ThmBab` via `jointWin_of` (`PrimeSetBound…:145-152`).
- [read] Exceptional twists are not discarded: the ≤ R twists of `Exc` (l = 2 and each l ∈ Bchi) stay, bounded by LemmaK because the window makes them ≤ x^{ε/(2CK)} (§3).
- [inferred] Pointwise in (l, e), windowed in x, for fields tied to auxiliary primes with log q ≈ Y^{ε/5}.

## Not read

Proofs of `NumberU3U_s`, `NumberSp4Alt`, `GdEndAlt`, `ThmS6Core_s`, `SymplecticFourImageDense`, `ZetaUr`, `PropZ`, `ML.iv`, `lemmaK_of_steps`, `FixedIn`, `TwoIn`, `sp4Main_alt`, `countIV`, `countVs`; definitions `Dat`, `Frame`, `Unl`, `TypeI/II`, `Adm2A`, `eis3`, `eis4`; ten fields of `HypothesesH'`.
