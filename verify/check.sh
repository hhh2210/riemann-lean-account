#!/usr/bin/env bash
# After the build: prints the type of the main theorem, the axioms each of the five theorems
# depends on, and the modules in which Mathlib's statement and zeta function are declared.
cd lean && . "$HOME/.elan/env"
cat > Check.lean <<'EOL'
import Main
open Lean in
#eval show CoreM Unit from do
  for n in [``RiemannHypothesis, ``riemannZeta] do
    let env ← getEnv
    let m := (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)
    IO.println s!"{n} is declared in {m}"
#check (riemannHypothesis : RiemannHypothesis)
#print RiemannHypothesis
#print axioms riemannHypothesis
#print axioms riemannZeta_eq_zero_re
#print axioms LFunction_ne_zero_of_half_lt_re
#print axioms LFunction_eq_zero_re
#print axioms LFunction_eq_zero_re_of_isPrimitive
EOL
lake env lean Check.lean
echo "CHECK-EXIT $?"
