/-
Targets: statements that follow from GRH for Dirichlet `L`-functions by known arguments and are
worth formalizing on top of the archive. This file states them and proves nothing. Each `def` is a
proposition, checked by Lean only for being well formed. None is used by anything else.

The constants are those of the cited papers and must be checked against the papers before a
formalization relies on them.

Compile with Mathlib alone:  `lake env lean Targets.lean`
-/
import Mathlib

namespace CarryForward.Targets

/-- `n` passes the strong probable-prime test to base `a`:
writing `n - 1 = 2 ^ s * d` with `d` odd, either `a ^ d = 1` or `a ^ (2 ^ r * d) = -1`
for some `r < s`, in `ZMod n`. -/
def IsStrongProbablePrime (n a : ℕ) : Prop :=
  (a : ZMod n) ^ ((n - 1) / 2 ^ (n - 1).factorization 2) = 1 ∨
    ∃ r < (n - 1).factorization 2,
      (a : ZMod n) ^ (2 ^ r * ((n - 1) / 2 ^ (n - 1).factorization 2)) = -1

/-- Miller's deterministic primality test with Bach's explicit bound
(G. L. Miller 1976; E. Bach 1990): an odd `n > 2` is prime if and only if it passes the strong
probable-prime test to every base `2 ≤ a < n` with `a ≤ 2 (log n)²`. -/
def MillerTestIsCorrect : Prop :=
  ∀ n : ℕ, 2 < n → Odd n →
    (n.Prime ↔
      ∀ a : ℕ, 2 ≤ a → a < n → (a : ℝ) ≤ 2 * Real.log n ^ 2 → IsStrongProbablePrime n a)

/-- The bound Miller's test needs (Ankeny 1952 without the constant; Bach 1990 with it):
for a non-principal Dirichlet character `χ` modulo `N`, some positive integer `a < 2 (log N)²`
has `χ a ≠ 1`. -/
def SmallNonresidue : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∃ a : ℕ, 0 < a ∧ (a : ℝ) < 2 * Real.log N ^ 2 ∧ χ (a : ZMod N) ≠ 1

/-- The prime number theorem with the error term the Riemann Hypothesis gives
(von Koch 1901): `|π(x) - li(x)| ≤ C · √x · log x` for `x ≥ 2`, where
`li(x) = ∫_2^x dt / log t`. -/
def PrimeCountingError : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤ C * Real.sqrt x * Real.log x

/-- Primes in short intervals under the Riemann Hypothesis (Cramér 1921):
for large `x` there is a prime in `(x, x + C · √x · log x]`. -/
def PrimeInShortInterval : Prop :=
  ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + C * Real.sqrt x * Real.log x

/-- The least prime in an arithmetic progression under GRH, with an unspecified constant:
for coprime `a` and `q` there is a prime `p ≡ a (mod q)` with `p ≤ C · (φ(q) · log q)²`. -/
def LeastPrimeInProgression : Prop :=
  ∃ C : ℝ, ∀ q a : ℕ, 2 ≤ q → Nat.Coprime a q →
    ∃ p : ℕ, p.Prime ∧ p % q = a % q ∧ (p : ℝ) ≤ C * ((Nat.totient q : ℝ) * Real.log q) ^ 2

end CarryForward.Targets
