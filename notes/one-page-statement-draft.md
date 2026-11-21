# The argument on one page (draft 0)

Status: a draft written on 2026-11-20 from the Lean source text alone, before the build has finished. Everything here is our reading, not the author's wording, and it is conditional on the archive compiling. The readings are `spine-first-reading.md`, `second-reading-the-analytic-step.md`, `third-reading-the-inputs.md` and the files in `slices/`. **Which claims the author has read in the source, and which rest on a delegated reading, is recorded line by line in `audit-of-the-one-page-draft.md`.** Several lines below are still delegated; none of those should be quoted as established.

## Statement

**Theorem.** For every primitive Dirichlet character χ, L(s, χ) has no zero with Re s > 1/2.

## Proof in six steps

Fix χ of order o and a small ε > 0. Write G(x) for the smoothed sum over prime powers n ≤ x of Λ(n) times a non-negative combination of the powers of χ(n).

**1. Landau on windows.** If G(x) ≤ x^(1/2 + Cε) for all x in a set that contains, beyond every point, a whole interval [Y, Y^(3/2)], then no power of χ has a zero with Re s > 1/2 + Cε. *(A Dirichlet series with non-negative coefficients; the classical theorem needs every large x, this one needs only windows.)*

**2. A host field and an exact identity.** At a scale x choose primes q, d and a 2-power level so that E = ℚ(√−q, √−d)·(a real 2-power cyclotomic layer)·(the field of χ) is a CM field with Galois group 𝔊 = (ℤ/2)² × H and CM type Φ induced from ℚ(√−d). For a size a and positive weights w on Φ, put

    ASK = Σ_p 2·log p · Σ_{i ≥ 1, Frob_p^i ∉ Φ} max(a/p^i − w, 0),
    MAIN = a·( log a − 1 − γ + L′/L(1, χ_Φ) − mean of log w ).

Then ASK − MAIN equals, exactly, a character-weighted sum of G-functions at the points a/w. *(Character orthogonality; nothing is estimated.)*

**3. From a count to G.** Take sizes a ≈ x·b and m systems of weights equal to b on a thick set of density x^(−ε) and tiny elsewhere, and average over translates in H. Every character of H dies; the tiny weights land at a scale where the classical zero-free region suffices; the three other characters of (ℤ/2)² have conductor far above every power of x and are bounded at x by a mean-square estimate and a zero-density count near Re s = 1. What remains is

    G(x) ≤ 4·x^(1/2 + ε) + (mean of ASK − MAIN) / (normalisation).

So it is enough to prove an upper bound: **the prime-power count ASK is at most its main term, up to an error.**

**4. The count is squeezed between two slopes.** For each of many indices u there is a lattice M_u of vector-valued algebraic modular forms on a definite unitary group over E, and a map B_u sending a form to the periods of its m-fold iterated theta lift, with values in one lattice of periods P.

- *Gains.* At a prime p whose Frobenius is outside Φ, those periods are divisible by p to the power about a/p + a/p³ + ⋯ (step 5). So B_u still maps the larger lattice N_u = M_u·∏ 𝔭^(−gain) into P, and the slope of N_u exceeds that of M_u by the total gain, which is at least ASK up to a loss.
- *The slope inequality.* The maps B_u form a nearly tight frame at one infinite place, so the mean over u of slope(N_u) − height(B_u) is at most slope(P), up to explicit errors (Theorem F, a statement about Hermitian lattices alone).
- *The period side.* On each Hecke piece the m-fold lift composed with its adjoint is the product of the m single-step scalars, so determinants multiply, and the slope of P is bounded by a ledger over the steps: a kernel cost log(ν!) − ν·log Ω per step, repaid by the step's eigenvalue and by the covolume of an auxiliary lattice except for the top term. That covolume bound is an input from arithmetic geometry: it is proved by Arakelov-style slope estimates for integral forms on a moduli space of the indefinite unitary group, and its hypotheses include an arithmetic Hilbert–Samuel statement, toroidal compactifications, resolution of singularities and heights of Chow forms. The result is slope(P) ≤ m·log(a!/Ω^a) − a·log T + small, where Ω is a CM period with mean log Ω = γ + log(π/v) − L′/L(1, χ_Φ) by the Chowla–Selberg formula, and T is a level prime fixed by a dimension count. With the count for T this equals MAIN identically. The cohomological bound of step 6 enters here once, bounding the discriminants of the lift lattices at the level primes through congruence ideals.

Chaining the three: ASK ≤ MAIN + Err, with Err of size x/m (the main term spread over m lifts), m (the price of each lift) and k/n² (a rank term).

**5. Why the periods are divisible.** A CM elliptic curve for ℚ(√−d) has good reduction at p, and at an inert p its formal group has height two, with logarithm Σ X^(p^(2j))/p^j. The complex coordinate z is a unit times that logarithm. The theta kernel of the lift is an integral power series in X, and a period is a polynomial in its derivatives in z at 0. Since the exponential of the height-two group has n-th coefficient of valuation at least −n/(p² − 1), a derivative of order n has valuation at least v(n!) − n/(p² − 1) ≈ n·p/(p² − 1) = n/p + n/p³ + ⋯.

**6. The three inputs.** (i) *A bound on cohomology:* for the host field, Σ_ℓ log ℓ · Σ_{1 ≤ e < t} length of the locally trivial part of H¹(G_S, ℚ_ℓ/ℤ_ℓ(−e)) is at most exp(x^ε). The slope argument needs no more than that; the tree proves about exp(x^(4ε/5)). The proof bounds all but boundedly many twists by Iwasawa theory in cyclotomic towers, and the rest by congruence numbers between cusp forms and Eisenstein classes on U(3) and GSp4: one non-zero integer whose ℓ-adic valuations bound the ℓ-parts for every ℓ at once. (ii) *Hosts exist* at every scale in windows of exponent 3/2, with their auxiliary characters bounded as a family by a mean square and a zero-density count near Re s = 1. (iii) *The lattices have the right size:* M_u is the space of all algebraic modular forms of its weight and level on the definite group, so nothing has to be shown to exist; what is needed is its exact dimension, from the mass formula, with the level prime T chosen to match the dimension of the target.

**Balance.** With m ≈ √x all three parts of Err are x^(1/2 + O(ε)), so G(x) ≤ x^(1/2 + Cε) on the windows, and step 1 finishes. ∎

## What this page does not yet earn

- Much of step 4 is stated from delegated readings: the proof of the slope inequality past its first two lemmas, the trace formula behind the frame, the ledger for the main term, and the nature of the auxiliary lattices. The audit note lists each.
- The page hides a large input. The covolume bound in step 4 rests on about fifteen statements of algebraic and arithmetic geometry, each claimed proved in the tree. An honest paper has to say that the slope argument is not elementary lattice theory plus automorphic forms: it also uses arithmetic intersection theory on a Shimura variety.
- Step 6 (iii): the forms are all algebraic modular forms and the content is a dimension count. The class number formula behind the count is delegated.
- The constants and the exact shape of each error are in the notes, not here.
- Nothing here is verified by us until the build is green; and a green build verifies the theorem, not this account of it.

## Where the page could be shortened further

The exponent 1/2 comes out of one optimisation: a main term of size x divided by the number m of lifts, against a cost linear in m. That is the shape of Stepanov's method, with iterated theta lifts in the place of high-order vanishing. A statement that isolates this as a single inequality about lattices, with the divisibility of step 5 as its only arithmetic input, would be the form to aim at.
