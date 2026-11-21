#!/usr/bin/env bash
# Builds everything Main imports and stamps each output line with the time. The last lines give
# lake's exit code. Run janitor.sh beside it. Run in the working directory of setup.sh:
#   bash build.sh > build.log 2>&1 &     bash janitor.sh > janitor.log 2>&1 &
cd lean && . "$HOME/.elan/env"
export LEAN_NUM_THREADS=$(nproc)
printf 'START %(%s)T threads=%s\n' -1 "$LEAN_NUM_THREADS"
lake build Main 2>&1 | while IFS= read -r l; do printf '%(%s)T %s\n' -1 "$l"; done
printf 'LAKE-EXIT %s\n' "${PIPESTATUS[0]}"
printf 'END %(%s)T\n' -1
