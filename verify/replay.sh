#!/usr/bin/env bash
# After the build: replays every declaration Main imports through the kernel, from an empty
# environment (replay/ReplayMain.lean). Our run used up to about 30 GB beyond the page cache
# on 28 threads.
# Usage, from the working directory of setup.sh:   bash replay.sh /path/to/this/verify/replay  out-dir
. "$HOME/.elan/env"
prog=$(cd "$1" && pwd); out=$(mkdir -p "$2" && cd "$2" && pwd)
(cd "$prog" && lake build replay) || exit 1
ulimit -s 1048576 2>/dev/null || ulimit -s unlimited 2>/dev/null
cd lean && LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-$(nproc)} lake env "$prog/.lake/build/bin/replay" "$out"
echo "REPLAY-EXIT $?"
