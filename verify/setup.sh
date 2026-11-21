#!/usr/bin/env bash
# Fetches the archive from its author's site, checks its hash, unpacks it, installs the pinned
# toolchain and fetches Mathlib's prebuilt cache for the pinned commit.
# Run in an empty working directory with about 150 GB free:   bash setup.sh
set -uo pipefail
for t in git curl zstd tar sha256sum; do command -v $t >/dev/null || { echo "SETUP-FAILED missing $t"; exit 1; }; done
command -v elan >/dev/null || curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
. "$HOME/.elan/env"
for i in $(seq -w 1 14); do
  curl -sSfL --retry 5 -o lean.tar.gz.part$i https://alpo.ge/lean.tar.gz.part$i || { echo "SETUP-FAILED part$i"; exit 1; }
done
cat lean.tar.gz.part?? > lean.tar.gz && rm lean.tar.gz.part??
echo "9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc  lean.tar.gz" | sha256sum -c - || { echo "SETUP-FAILED hash"; exit 1; }
tar xzf lean.tar.gz && cd lean || { echo "SETUP-FAILED untar"; exit 1; }
echo "lean files: $(find src -name '*.lean' | wc -l)"
lake exe cache get 2>&1 | tail -3
lean --version
lake build Statements 2>&1 | tail -5
[ -f .lake/build/lib/lean/Statements.olean ] && echo SETUP-DONE || echo "SETUP-FAILED statements"
