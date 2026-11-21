# Hosts: how the auxiliary field is chosen and how its auxiliary characters are bounded

Read 2026-11-20 from source text (build unfinished). Paths are relative to `src/` in the archive. A tag governs every sentence up to the next tag: **[read]** transcribed from a definition or statement; **[proved-by]** a theorem of that type was found; **[inferred]** my interpretation.

**[inferred]** In brief: a host is the abelian CM field cut out of ℚ(ζ_{QS·q·d}) by ψ, by ±1 mod 2^{e+2} and by the quadratic characters of q and d. Its auxiliary characters ξ·(·/q)^i·(·/d)^j, (i,j) ≠ (0,0), have conductors at least q ≈ exp(x^{ε/(5J)}). They are bounded at x for most q, then most d, by a mean square over prime moduli together with a zero-density count. Behrend's construction supplies the thick set in the 2-power tower.

## 1. What a host is

**[read]** `Frame` (`Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean:15`) is an abelian group A of order `ord` together with two pieces of structure:
- a surjection h from A onto (ℤ/2^{e+2})ˣ/⟨−1⟩, a cyclic group of order 2^e;
- a subgroup A0 = ⟨a0⟩ on which h is injective.

Put n0 = ord a0 and o = ord/n0. The Galois group is `GG := G0 × φ.MA` with G0 = ℤˣ × ℤˣ (:89).

**[read]** `HostRaw`/`HostAx` (`.../TotientGaloisClasses/ConjEMemHostFIff.lean:12, 174`) carry:
- primes q and d with `HostHyp q d` (`Formalism/FrobeniusOrbits/Statement.lean:13`): q ≡ 3 (8), d ≡ 7 (16) and (−d/q) = 1;
- an integer QS with 2^{e+2} | QS and QS prime to qd, all of whose odd prime factors split in K = ℚ(√−d);
- a Galois field E ⊂ ℚ(ζ_{QS·q·d}) with Gal(E/ℚ) ≅ GG;
- an Artin map `art` onto GG with `art (-1) = φ.cc`;
- an element `sqd` with `sqd ^ 2 = -d`.

`HostDer` (:87) adds the following requirements:
- E is a CM field of degree 4·ord.
- The two G0-coordinates of art(u) are (u/q) and (u/d).
- The CM type is `{ψ | ψ sqd = Complex.I * √d}` (:66), with stabilizer Psi = {g : g.1.2 = 1}.
- The different of E/K is 𝔟·𝔟̄ with 𝔟 + 𝔟̄ = 1, and Tr_{E/K}(xȳ) is unimodular on 𝔟⁻¹.

**[read]** For a given ψ, `KerChi ψ H` (`Development/AutomorphicArithmetic/CharacterBoxes/TwistForm.lean:9`) pins the field down: `art a = 1 ↔ (a ≡ ±1 [MOD 2^(e+2)]) ∧ ψ a = 1 ∧ (a/q) = 1 ∧ (a/d) = 1`. **[proved-by]** `isChiField` (`CharacterBoxes/IsChiField.lean:5`) shows this E is the field `IsChiField ψ e q d` that VWin bounds (`CharacterBoxes/ExistsPageN.lean:19`). **[read]** `fieldChi` (`CharacterBoxes/FieldChi.lean:20`) builds such a host for every e ≥ e0, with ord = c·2^e and o = order of ψ. **[inferred]** So E = ℚ(√−q, √−d)·ℚ(ζ_{2^{e+2}})⁺·ℚ(ψ). Its Galois group is (ℤ/2)² × A, with the tower as A0, and the CM type Φ is induced from K.

**[read]** `Host R` (`Formalism/LocalRingCardinality/DataHost.lean:39`) adds level primes {g0, g1, pde, pde′, q0}, the tops `TT : Finset R.A`, the thick set `T2 : Finset ℕ`, a translate `u0`, and `NoRel T2 Lw` (:107). The top places are ((1,1), t) for t ∈ TT. The thick places are ((−1,1), s·a0 + u0) for s ∈ T2 (:129, :133).

## 2. The existence statement

**[read]** `HostExW la P` (`Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:120`):
```
∀ eps, 0 < eps → eps < 1/52 → ∃ CT2 C8 C5 c6 Cb x0, 1 ≤ C8 ∧ 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧
  ∃ S : Scales la, ∀ s, s.eps = eps → x0 ≤ s.x → S.Mem s →
    ∃ R H q0, RankVal s R ∧ H.CT2 = CT2 ∧ HostGood s C8 C5 c6 Cb H q0 ∧ P C5 s R H q0
```
For each small ε there is a set of scales, containing a whole interval [Y, Y^la] beyond every point (`.../PrimeDiscriminants/Scales.lean:9`). Every scale x in it carries ranks and a good host. `RankVal` (`.../GlobalTwisting/PairRowIffQdRows.lean:28`) asks for n = ord ∈ [x^{2+8ε}, 2x^{2+8ε}], m ≈ √(xδ1) with δ1 = x^{−ε/8}, and k ≈ x^{9/2+10ε}.

**[read]** `HostGood` (`ThinScalesIffHostBound.lean:101`) is the conjunction of:
- `HostVal` (`PairRowIffQdRows.lean:78`): some Y ∈ [x^{1/J}, x] with `PairRow` (the windows of §5, in Kronecker form); |TT| ∈ [δ1n/2, 2δ1n]; |T2| ≥ x^{−ε}n; Lw ≈ 4050 log x;
- `HostArith`;
- the Behrend lower bound on |T2|, and 4Lw|T2| ≤ n0;
- `QDq x ε C5 q d`;
- `BoxW`;
- |Re L′/L(1, (·/d))| ≤ x^ε;
- `ThinOK`;
- `BadOK`;
- congruences on the level primes.

**[read]** For ψ the requirement is `GChi ψ` (`CharacterBoxes/Supply.lean:42`), namely `EAtH (Level.cyc ψ) H TT x ε 4 ∧ VVle H.E t (√b)`. `EAtH` (`.../ExplicitFormulaErrorOfHostConditions.lean:144`) requires:
- o is the order of ψ, and the kept characters lie in Xp;
- the `psK` clause;
- `Shares TT (x^{−1+ε})`;
- `BoundedCharsPointwise` at x;
- |L′/L(1,χ)| ≤ 4 log x for every bounded χ.

**[proved-by]** `supplyChi : ∀ ψ, VWinAt ψ 401 → HostExW (3/2) (GChi ψ).req` (`CharacterBoxes/SupplyChi.lean:8`), proved as `supplyOfAdm` (`CharacterBoxes/HostOfField.lean:17`). That is `supplyOfAdmOf hostOfField` fed with `admissibleClassesTwistedChar` (`CoprimeRanks/AdmChi.lean:13`). The latter gives ranks with `RankVal` and `admitted R H0`: every choice of level data extends H0 to a `Host` (`CharacterBoxes/Imports.lean:9`). **[read]** `hostOfField` (`HostOfField.lean:8`) takes `PairWin s Y`, `PairGood M ε Y x q d`, `FieldRows` and `admitted`. It returns a host H ⊇ H0 satisfying `HostGood s C8 4 c6 Cb H q0` and `Shares H.TT (x^{−1+ε})`. `supplyOfAdmOf` (`ShortNorms/supplyOfAdmOf.lean:13`) combines it with `fieldChi`, `winPairs` (which calls `QH.pairEx`) and `boundedTw`.

## 3. Condition (a): the auxiliary characters at x

**Which characters. [read]** `Bounded S = {θ | (θ ∈ Xp ∧ ¬Kept S θ) ∨ θ ∈ Xm}` (`.../TotientGaloisClasses/Analytic.lean:136`). Xp and Xm are the characters trivial on A0 with θ(iod) = +1 and −1 respectively. By `TwistForm` (`TwistForm.lean:14`), each such θ is a ↦ ξ(a)(a/q)^i(a/d)^j with ξ ∈ ⟨ψ⟩ and θ(iod) = (−1)^j. The proof of `boundedTw` (`CharacterBoxes/BoundedTw.lean:45`) shows that every bounded θ has (i,j) ≠ (0,0), and it bounds each one by `PairGood.bounds` at y = x. **[inferred]** Conversely, every pair (i,j) ≠ (0,0) gives a bounded θ: j = 1 puts θ in Xm, and when j = 0 the factor (·/q) keeps θ from being kept. That makes 3·o characters. For ψ = 1 they are the three in `QDq` (`Formalism/SharpRestriction/InertJacobiLevels/AsmIface.lean:166`), (−q/·), (−d/·) and (qd/·). These are `ValuesAtX`'s `psC, chC, chpsC` (`Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean:67`).

**The statement. [read]** `PairGood M ε Y X q d` (`CharacterBoxes/PairGood.lean:18`):
```
pair : WinPair ε Y q d ;  coprime : gcd(M, q*d) = 1
bounds : ∀ ξ mod M, (i,j) ≠ (0,0), χ primitive inducing ξ·(·/q)^i·(·/d)^j, ∀ y ∈ [Y, X],
  ‖gChi χ y‖ ≤ y^(1/2 + ε/2) ∧ ‖L'/L(1,χ)‖ ≤ 4 log y
boxes : ∀ real ρ, ρ.N ∣ 8M, (i,j) ≠ (0,0): that twist has no zero with Re s > 1 − 1/400, |Im s| ≤ height M ε Y j
```
`PairEx` (:28) says: for all M ≥ 1, ε < 1/52 and A ≥ 1 there is Y1 such that every Y ≥ Y1 has q, d with `PairGood M ε Y (Y^A) q d`. **[proved-by]** `QH.pairEx` (`MeanSquareBounds/pairEx.lean:112`).

**Most q, then most d. [read]** `pair_share` (`MeanSquareBounds/PairShare.lean:26`) uses z = Y^{ε/5} and two families:
- the q-family: primes q ∈ (e^{z/2}, e^z] with q ≡ 3 (8) (`PrimeSetTwoBounds.lean:41`);
- the d-family: primes d ∈ (e^{z′/2}, e^{z′}] with d ≡ 7 (16) and q·∏_{3≤p≤z} p | d+1 (:45).

It shows that a share at least 1 − η of the q-family is `GoodQ`. For each such q, a share at least 1 − η of its d-family is `GoodD` (:48, :51). Being good puts every primitive twist in `Box` (:35), which means:
- conductor ≤ Q, and no zero in the box;
- |L′/L(1)| ≤ C log Y;
- |G_χ(y)| ≤ y^{1/2+τ} on [Y, X].

**[proved-by]** `pair_exists` (`PairExists.lean:9`) takes η = 1/2 and picks any good q, then any good d. One pair is extracted by counting.

**The family estimate. [proved-by]** `stage` (`StagePow.lean:41`) works with the primes `PPset m0 a0 U`: q ≤ U, q ≡ a0 (m0), q > √U, where log U ∈ [Y^{ε/6}, Y^{ε/5}log²Y]. It shows that at most η·|PPset| of them have some twist outside `Box`. **[read]** The proof splits these bad q into two classes.
- **B1, a zero in the box.** `ZeroDensityBox` (`Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountSt.lean:7`):
  ```
  ∃ C, ∀ Q ≥ 3, any set of primitive characters of conductor ≤ Q, each with a zero s,
     Re s > 1 − 1/400, |Im s| ≤ Q, has at most C·Q^(1/4) elements
  ```
  **[proved-by]** `zero_density_box` (`.../CountZAll.lean:13`). **[read]** This is set against |PPset| ≥ U^{9/10}, from `count_a` (`.../MSqCount.lean:346`).
- **B2, a large finite sum.** Write G_χ(y) = −S − y·tail, with S(Z,y,q,κ) = Σ_{n≤Z} Λ(n)·min(1,y/n)·κ(n)·(n/q) and Z = Y^{400K} (`PrimeSetTwoBounds.lean:13`).
  - `meanSqK` (`meanSqK.lean:51`) proves Σ_{q∈PPset} |S|² ≤ C·y·log y·|PPset| for all y ∈ [Y, Y^K] and |κ| ≤ 1.
  - `bad_share` (`BadShare.lean:251`) turns this into |B2| ≤ η′|PPset|. **[inferred]** This is in effect Markov's inequality; I did not read the proof. **[read]**
  - The off-diagonal terms are handled by `twistK` (`twistK.lean:148`). It says that, except for one modulus nstar, every odd squarefree s with 1 < s ≤ Y^A and s prime to m0 has |Σ_{q∈PPset} (q/s)| ≤ Y^{−B}|PPset|.
  - `twistK` uses `ZFRDirichlet`, `ExcBound`, `page_across` (Landau–Page) and `PNTAPRelW` (`.../MeanSquareHypWIff.lean:38`). `PNTAPRelW` is the prime number theorem mod M with relative error. Its main term is corrected by at most one real χ1 with a zero β1 > 1 − 1/(8 log M), and it holds for log X ≥ C0·log M·log log M. **[proved-by]** `pnt_progressions_relative_weak_holds` (`.../PNTFinal.lean:22`).

  **[read]** For q outside B1 ∪ B2, `box_of_S` (`BoxOfS.lean:28`) applies: with no zero in the box, the tail is ≤ Y^ε and |L′/L(1)| ≤ C log Y.

**Order of choices. [read]** `winPairs` (`CharacterBoxes/WinPairs.lean:5`) proceeds in three steps:
1. It chooses (q, d) from `PairEx` at Y = X^{1/J}.
2. `VWinAt` (`ExistsPageN.lean:44`) holds for every pair satisfying `WinPair`. It yields W with W² ≤ X and the cohomology bound for all x ∈ [W, W²].
3. One pair therefore serves the whole window [kW, (kW)^{3/2}].

**Why this is not circular. [inferred, from these statements]** The bounded characters are twists by (·/q), (·/d) and (·/qd), whose conductors exceed every power of x. Their bound at x uses neither G, nor ψ, nor zeros near Re s = 1/2. It uses two inputs:
- orthogonality of quadratic characters to prime moduli q > Z² on sums of length Y^{O(1)}, which needs only the prime number theorem in progressions to moduli ≤ Y^{O(1)}, up to exp(Y^{ε/5}), with one exceptional modulus dropped;
- a zero-density count near Re s = 1 − 1/400.

An auxiliary character's own half-plane is proved when it is itself the ψ of `supplyChi`. `zeroFreeAll_of_topG` treats each ψ separately, with no induction over characters.

**The weighted-family statements. [read]** `WeightThm`, `WeightCor` and `WeightedSieveImpliesRH` (`Formalism/JacobiWeightFamilies/Statement.lean:38, 49, 57`), `ChebyshevWeightedAverageOverJacobiFamily` (`Formalism/WideWeightTheorem/Statement.lean:57`), and `EstimateImpliesRHDirichlet`/`Weighted` (`Formalism/ThickAverageLoss/Statement.lean:129, 158`) bound L(1, χ_d)-weighted means of G_{χ_d}. The average runs over squarefree d ∈ [D, 2D] with d ≡ r (8M) and prime factors > z. `WeightPrimeCor` (`Formalism/TwistFamilyExistence/Statement.lean:72`) extracts one prime d from moment bounds. No file other than its own mentions any of these names. No proof was located, and they are not on the path.

## 4. Condition (b): huge scales

**[read]** `ThinOK s c H` (`ThinScalesIffHostBound.lean:61`) is equivalent to `ChebyshevCharacterBound` (`Analytic.lean:145`): every primitive χ coming from GG satisfies ‖gChi χ y‖ ≤ y·exp(−c·x^{ε/8}) for all y ≥ exp(x^{ε/3})/3. **[proved-by]** `thinH` (`MeanSquareBounds/GaussSumFunctionEq.lean:55`) proves `ThinH` (`PairGood.lean:36`) under log(QS·q·d) ≤ 2x^{ε/5}log²x and `RealBox`. **[read]** Its route goes through `thin` (`Thin.lean:10`) and `psi_thin` (`PsiThin.lean:385`). `psi_thin` states: for primitive χ with log N ≤ λ and no real zero in (1 − c0, 1),

|ψ0(χ,u)| ≤ C·u·(log u + λ)²·exp(−c·log u/(λ + √log u)).

It comes from an explicit formula and `ZFRDirichlet` (`Formalism/LandauZeroFreeBounds/Statement.lean:15`):
```
∃ c > 0, ∀ χ mod q, ∀ s, Re s ≥ 1 − c/log(q(|Im s|+2)) → L(χ,s) = 0 (nontrivial) →
  χ² = 1 ∧ χ ≠ 1 ∧ Im s = 0 ∧ L'(χ,s) ≠ 0 ∧ it is the only such zero mod q
```
**[proved-by]** `zFRDirichlet` (`LandauZeroFreeBounds/NoZeroComplex.lean:32`). **[inferred]** The bound follows because log y ≥ x^{ε/3}/2 is far larger than λ ≈ x^{ε/5}log²x.

**Siegel zeros. [read]** Real characters with q | N or d | N are covered by the boxes, via `realBox` (`CharacterBoxes/RealBox.lean:99`). The others have bounded conductor and are handled by `small_zeros` (`SmallZeros.lean:32`). Siegel's `ExcBound` (`LogDerivRegionChiOf.lean:50`, proved by `excBound`) enters through `count_a` and `twistK`; I did not check for other uses. `Level.cyc` sets `psK := none` (`ExplicitFormulaErrorOfHostConditions.lean:112`), so no exceptional character of weight 1 occurs on this path.

**[read]** `HostConditions`, `LogDerivativeBound`, `PreHost` and `HType` (`Analytic.lean:149, 163`) form a parallel packaging. `PreRows.eAtH` (`CoprimeRanks/OfPInjective.lean:130`) converts it to `EAtH`; I did not trace its users. `GzPNT` (`Formalism/ZeroFreeRegion/Statement.lean:16`, proved by `gzPNT`) and `DLVP` (`ThickAverageLoss/Statement.lean:15`) both state |G(y)| ≤ K·y·exp(−c√log y). Neither occurs on the route above.

## 5. Condition (c): sizes

**[read]** `WinPair ε Y q d` (`ExistsPageN.lean:27`) asks for:
- q prime, q ≡ 3 (8), log q ∈ (Y^{ε/5}/2, Y^{ε/5}];
- d prime, d ≡ 7 (16), log d ∈ (Y^{ε/5}log²Y/2, Y^{ε/5}log²Y];
- `q ∣ d + 1`, and p | d+1 for every odd prime p ≤ Y^{ε/5}.

`WinDatum` (`TwistForm.lean:19`) adds x^{2+8ε} ≤ c·2^e ≤ 2x^{2+8ε}. **[proved-by]** `qdRows_kron_odd` and `qdRows_kron_two` (`CharacterBoxes/PairRows.lean`) give (−d/p) = 1 for p = 2, for p = q and for every odd p ≤ Y^{ε/5}. **[inferred]** These primes split in K, as `QS_split` and the factorisation of the different require.

## 6. Condition (d): shares, the thick set, Behrend

**[read]** The shares (`ExplicitFormulaErrorOfHostConditions.lean:135, 139`):
```
lam γ = (if γ ∈ A0 then 4 else 3) / (3o + 1)
Shares TT δ : ∀ γ, | #{t ∈ TT : t − γ ∈ A0} − lam γ · |TT| | ≤ δ·|TT|
```
`tops_sum` (`PrimitiveCosets/TopsSum.lean:75`): under `Shares TT δ`, every non-trivial θ trivial on A0 satisfies |Σ_{t∈TT} θ(t) − |TT|/(3o+1)| ≤ o·δ·|TT|. **[inferred]** Averaging over TT gives each non-trivial character of the level the weight 1/(3o+1), which is `Level.wt` in `Gm` (:36, :38). **[read]** `topsChoiceH` (`ThickFrames/topsChoiceH.lean:30`) supplies TT with |TT| ≈ δ1n, `BadOK` and `Shares TT (x^{−1+ε})`.

**[read]** `NoRel T L` (`Formalism/FrobeniusOrbits/HostThickExists.lean:13`): for distinct s1, s2, s3 ∈ T and i ≠ j with 0 < |i|, |j| ≤ L, `j(s₂ − s₁) ≠ i(s₃ − s₁)`. `HostThickExists` (:30):
```
∃ C > 0, ∀ n, L ≥ 2, ∃ T, (∀ s ∈ T, 4Ls < n) ∧ NoRel T L ∧ n·exp(−C·√(log n · log L))/L ≤ |T|
```
**[proved-by]** `hostThickExists` (`FrobeniusOrbitsProofs/ThickExists.lean:181`). Its lemma `noRel_image` (:85) shows that Mathlib's `Behrend.sphere S d k`, read in base 4Ld via `Behrend.map`, satisfies `NoRel`. This is Behrend's sphere construction. **[read]** `thickFrame2` (`ThickFrames/ThickFrame2Large.lean:29`) applies it with n0 ≈ x^{2+8ε} and Lw ≤ C log x. It gets |T2| ≥ x^{−ε}·ord and 4Lw|T2| ≤ n0.

**[read]** `hostThickOrbit` (`.../TotientGaloisClasses/FrameFacts.lean:821`) says what `NoRel` buys:
- if ord x > 4L, any L consecutive terms of t + i·x meet T2 + u0 at most twice;
- otherwise the whole orbit meets it at most once.

It is consumed by `GlobalTheory.HTW.LongWindow.main` (`.../SatakeParameters/AtMostTwoThickInWindowLongOrbit.lean:27, 30`). It is also consumed by `no_three_consecutive_thick_places` (`.../NoThreeConsecutiveThickPlaces.lean:222`), whose namespace is `UnusedSlot33` (:7). **[inferred]** Frobenius powers translate A0, so each prime's powers reach thick places (weight ≈ b, scale x) at most twice per Lw-window. Behrend's density x^{−o(1)} meets δ ≥ x^{−ε}.

**[read]** `Formalism/BehrendSets/Statement.lean` states a parallel version:
- `BehrendFree` (:48): no nonconstant solutions of αx1 + βx2 + γx3 = 0 with α + β + γ = 0 and |·| ≤ K;
- `BehrendBound` (:54): such sets of size ≥ N·exp(−C√(log N·log(K+1))) in [0, N);
- `WindowTwo` (:67), `OrbitOne` (:72) and `TranslateMean` (:78).

Outside the module, only `trivStab` (a p-group lemma unrelated to Behrend) and an import of `TranslateMean` are referenced. The route uses `FrobeniusOrbits.hostThickExists`.

## 7. On the path?

**[read]** The chain is `every_character_of_green_v_win` → `zero_free_all_of_green_v_win` (`.../ThirdPlaceSeries/TopPlug.lean:12–17`) → `zeroFreeAll_of_topG (la := 3/2) … (fun ψ => supplyChi ψ (hV ψ))`. Inside `zeroFreeAll_of_topG` (`CharacterBoxes/ZeroFreeAllOfTopG.lean:26`), `hS ψ` feeds `TopG`. `eFamC_of_cls` turns `EAtH` into `EFamC` (`.../TotientGaloisClasses/TopDefs.lean:15`).

By reference, the path includes `supplyChi`, `HostGood`, `EAtH`, `Shares`, `pairEx`/`stage`, `ZeroDensityBox`, `PNTAPRelW`, `ZFRDirichlet`, `ExcBound`, `thinH` and `hostThickExists`. The weighted-family statements and the Behrend statements of `Formalism.BehrendSets` are not referenced from it. Four cases are undetermined:
- `trivStab`;
- `PreRows.eAtH`;
- `PrimePairOfBoxAndMeanSquareHypotheses`, proved at `GL3MeanSquares/HookFormulaTorsion/NumericalZeroDensityBound.lean:413`, whose consumers I did not trace;
- `GzPNT`.

**[read]** This confirms the count of three. `GrowthInequalityExplicit` (`GrowthBoundGivesRiemannHypothesis.lean:87`) has `Gz x - 3 * x ^ (1/2 + ε) - moveCost x Cd CL`. `SmallCosts` (:96) bounds `moveCost` by x^{1/2+ε}, which yields the `4 * x ^ (1/2 + ε)` of `GrowthInequalityForm` (:99) quoted in the second reading.

## Not read

Proofs of `meanSq_abs`, `bad_share`, `tailK`, `kappaC`, `count_a`, `stage2` (`CharOf.lean:61`), the zero-density assembly and `topsChoiceH`. Also `levelData`, `exists_host`, `FieldRows` and `CyclotomicNorms.BB`, and how the thick-window lemmas reach `ChainTied`. For `DirichletDensity`, `LFunctionBounds`, `AdmissibleDesigns`, `CMTypeGalois` and `TameInertiaTowers`, only the statement names were seen.
