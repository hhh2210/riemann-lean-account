/-
Immediate corollaries of the top theorems of the archive, stated in forms people use.
Each is proved here from the archive's `Main` and Mathlib alone, with no new axiom.

Compile against a built copy of the archive:  `lake env lean Corollaries.lean`
-/
import Main

open Complex

namespace CarryForward

/-- The Riemann zeta function has no zero with real part greater than `1/2`.
The point `s = 1` is excluded because it is the pole. -/
theorem riemannZeta_ne_zero_of_half_lt_re (s : ℂ) (hs : 1 / 2 < s.re) (h1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  have h := LFunction_ne_zero_of_half_lt_re 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr h1)
  rwa [DirichletCharacter.LFunction_modOne_eq] at h

/-- No exceptional (Siegel) zeros: a Dirichlet `L`-function of a non-trivial character has no
real zero in the interval `(1/2, 1]`. -/
theorem LFunction_ne_zero_of_real_of_half_lt (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (σ : ℝ) (hσ : 1 / 2 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
  LFunction_ne_zero_of_half_lt_re N χ (σ : ℂ) (by simpa using hσ) (Or.inl hχ)

/-- Every zero of a Dirichlet `L`-function in the open critical strip lies on the critical line.
This is the archive's `LFunction_eq_zero_re`, restated with its hypotheses named. -/
theorem LFunction_zero_on_critical_line (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : DirichletCharacter.LFunction χ s = 0) :
    s.re = 1 / 2 :=
  LFunction_eq_zero_re N χ s h0 h1 hz

end CarryForward

#print axioms CarryForward.riemannZeta_ne_zero_of_half_lt_re
#print axioms CarryForward.LFunction_ne_zero_of_real_of_half_lt
#print axioms CarryForward.LFunction_zero_on_critical_line
