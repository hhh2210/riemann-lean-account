#!/usr/bin/env bash
# Run beside the build. Lake writes a 5 MB `.setup.json` for every module that imports all of
# Mathlib: for the 175,187 modules of this archive they would take about 900 GB. A module's file
# is read once, when its compile starts, and lake accepts a built module without it, so each is
# deleted as soon as the module's .olean exists. Stop it when the build has ended.
cd lean/.lake/build || exit 1
while true; do
  n=0
  while IFS= read -r f; do
    m=${f#ir/}; m=${m%.setup.json}
    [ -f "lib/lean/$m.olean" ] && rm -f "$f" && n=$((n + 1))
  done < <(find ir -name '*.setup.json')
  printf '%(%s)T removed %s, disk %s\n' -1 "$n" "$(df -h . | awk 'END {print $3 " used of " $2}')"
  sleep 60
done
