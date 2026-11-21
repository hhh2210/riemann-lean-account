#!/usr/bin/env bash
# After the build: computes the dependency cone of riemannHypothesis (cut/CutMain.lean).
# Usage, from the working directory of setup.sh:   bash cut.sh /path/to/this/verify/cut  out-dir
. "$HOME/.elan/env"
prog=$(cd "$1" && pwd); out=$(mkdir -p "$2" && cd "$2" && pwd)
(cd "$prog" && lake build cut) || exit 1
cd lean && lake env "$prog/.lake/build/bin/cut" "$out"
echo "CUT-EXIT $?"
