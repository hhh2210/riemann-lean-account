# The spine of the released proof: a first reading

Read 2026-11-20 from the source text of Alpöge's Lean archive, top down from `riemannHypothesis`, while the build was still running. This is what the files say, in the order the proof term calls them. Names are the author's; where a definition was read, its content is given, and where only a name was read, it is marked *name only*. Nothing here is verified until the build is.

Paths are relative to `src/` in the archive. ## The chain

**1. RH from non-vanishing.** `riemannHypothesis` is `rh_of_every allChi` (`Formalism/GammaFactorNonvanishing/CritLine.lean`). `EveryCharacter` says: for every modulus N, every Dirichlet character χ mod N and every s with Re s > 1/2 (excluding the pole), `L(χ, s) ≠ 0`. Taking N = 1 gives ζ, and the functional equation finishes. About thirty lines on Mathlib.

**2. All characters from primitive data.** `EveryCharacter` is `imprimitive` applied to `ZeroFreeAll`: every `PChar` ψ has `L(ψ.χ, s) ≠ 0` for Re s > 1/2 (`Development/AutomorphicArithmetic/CharacterBoxes/`, `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean`).

**3. The analytic step.** `zeroFreeAll_of_topG` gets `ZeroFreeAll` from a statement `TopG` about families of arithmetic data indexed by a scale x → ∞, through `zeroFreeOn_of_tiedWin_cyc`. The statements under `Formalism/` show the shape of this step: a one-sided power bound on

    G(x) = Σ_{n ≤ x} Λ(n)(x/n − 1) − x log x + (1 + γ)x

and its twists by characters implies the zero-free half-plane, by a Landau-type argument on sums with non-negative weights `Λ(n)(1 + Re χ(n))`. *How `TopG` yields the bound was not read.*

**4. Three inputs.** `every_character_of_green_v_win` (`.../ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean`) takes:

- **`Green`**, supplied from a field of the literature bundle (`greenRegularCharacters`). *Name only.*
- **`VWin`**, a bound on Galois cohomology in a tower of abelian fields. Read in full, below.
- **A non-empty set of hypotheses on "the definite side"**, built by `nonempty_hyps_definite_side_of_closed_bound` from: the literature bundles, `ThetaIntegralsAgree`, `LocalMatching`, a covolume bound `CovolumeBoundOfX`, a local Langlands correspondence, and a step named `boundAtTwoThree_linked_of_recT`. The note's item 14 says the argument "would stop at 2/3 a priori"; this is presumably where.

**5. `VWin`, the cohomological bound** (`CharacterBoxes/ExistsPageN.lean`). For a character ψ, small ε, a level e with 2^e between x^(2+8ε) and 2x^(2+8ε), and two auxiliary primes q ≡ 3 mod 8 and d ≡ 7 mod 16 in prescribed windows with q dividing d + 1: let E be the subfield of a cyclotomic field cut out by ψ, by ±1 modulo 2^(e+2), and by the quadratic characters of q and d. Then

    Σ_ℓ log ℓ · Σ_{1 ≤ j < x^401} shaLen(E, ℓ, j)  ≤  sqrt(exp(x^ε)),

where `shaLen` is, by its name and its arguments, the length of a Tate–Shafarevich-type Galois cohomology group of E at ℓ in the j-th twist (its definition was not read).

All those groups are finite, and their total logarithmic size is far below any trivial bound. This is the note's item 17, "a significant weakening of Vandiver", and the tower in e is its "Iwasawa tower".

**6. `VWin` from Galois representations.** `vwin_of_row` derives `VWin` from `Row0b` together with a base-change statement. `Row0b` (`Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean`) says: for every CM field E, prime ℓ, and regular algebraic polarized cuspidal automorphic representation π of GL_a over E, there is a continuous semisimple ℓ-adic representation of the Galois group of E with the Hodge–Tate weights given by π's infinitesimal character, crystalline where π is spherical. Its compatibility with π away from ℓ is partial (`AwayB`, same file): the dimensions agree; the two parameters are equal when π's is a sum of characters with trivial monodromy; and for tame, square-free parameters at places whose completion is ℚ_g with g > 16a², the characteristic polynomials on inertia agree. So this is existence in the generality of Clozel, Harris–Taylor, Shin and Chenevier–Harris, with less than Caraiani's local-global compatibility. The fuller reading is `slices/galois-from-theta.md`.

**7. Galois representations from theta lifts.** `Row0b` is `galoisRepresentations_of_thetaLift tLiftK`, using a geometric statement `GeoOne` (*name only*) and `TLiftK` (`Foundations/GaloisRepresentations/ThetaParseval/HalfIndexLattices/TLiftK.lean`): for a CM field E and a Hermitian space X of dimension n, there is d₀ such that for every d ≥ d₀, every skew-Hermitian space W of dimension d and every pair of Hecke characters with the right restrictions, each automorphic representation of U(X) with weights above a bound has a lift to U(W). Lifts exist once the target is large enough.

**8. The literature.** One file, `.../ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`, gathers 186 theorems, 155 of them in a namespace called `Published`: resolution of singularities in characteristic zero, Kawamata–Viehweg and Nadel vanishing, arithmetic Hilbert–Samuel, Bhatt–Scholze, Clozel purity, Deligne–Ribet, Casselman–Wallach, Howe duality, Bernstein–Zelevinsky finiteness, a local Langlands correspondence for GL_n. Each row's proof points at a theorem inside the tree. The table is `literature-interface.md`.

## What this reading shows

- **The proof is not a short argument on top of Mathlib.** It is a new argument on top of about 180 published theorems, with every one of those theorems formalized in the same tree. The 17.4 million lines are mostly the second part.
- **The six `Published` statements read so far are general, not special cases.** `ResolutionCharZero` is Hironaka's theorem for every reduced separated scheme of finite type over a field of characteristic zero. If the tree compiles, it contains machine-checked proofs of theorems that, as far as I know, have not been formalized before. That is a second extraordinary claim inside the first, and it is where a failed build is most likely to show.
- **The correctness of RH does not depend on those statements meaning what their names say.** The final theorem is Mathlib's statement with no hypotheses. A mislabelled intermediate statement would damage an exposition, not the proof.
- **The author's own boundary between known and new is in the code.** The hypothesis `O` and the namespace `Published` mark what he treats as literature. Everything between that file and `EveryCharacter` is the new argument.

## The statement nobody has written

The release has no intelligible statement of the proof: the note is a timeline, and the Lean's top theorem is one line resting on 175,187 files. The code already contains the cut along which one can be written:

> **Theorem.** Assume the following published theorems [the audited list]. Then for every Dirichlet character χ and every s with Re s > 1/2, L(χ, s) ≠ 0.
>
> **Proof, in five steps.** (a) Lifts exist [7]. (b) Hence Galois representations with local-global compatibility [6]. (c) Hence the cohomological bound in the tower [5]. (d) Hence, with the theta-integral identities and the covolume bound, the family bound [4]. (e) Hence the one-sided bound on G, and Landau [3].

Each bracket points at a statement in the tree that can be transcribed into ordinary mathematical language and checked against the Lean. Steps (a) and (b) are, on their face, known theorems proved a new way; (c), (d) and the passage inside (e) are where the new mathematics must live.

## Not yet read

- `TopG`, `HostExW`, `FamP`, the datum `D7` and the class `Closed`: the objects step 3 and step 4 are stated in.
- `LinkN` was read as a formula (a ramification-weighted sum bounded by a rank times a size term plus the cohomological sum), not understood.
- `GeoOne`, `Green`, `OpenImageCondition`, `ThetaIntegralsAgree` and `LocalMatching` beyond their signatures.
- Where a determinant and Weil positivity enter, and where Stepanov's multiplicity is counted. The note puts these at the centre; the top of the proof term does not show them.
