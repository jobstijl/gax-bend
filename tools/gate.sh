#!/usr/bin/env bash
# The project gate. Passes only when
#   1. `bend PROOF.bend` prints ALL PROOFS CHECK,
#   2. every tests/*.bend prints exactly the `#|` lines it ends with,
#   3. every negative control tests/neg/*.bend fails to check.
# Usage: tools/gate.sh [-q]    (-q: one line per failure only)
set -u
cd "$(dirname "$0")/.."
. tools/env.sh
quiet=${1:-}
fail=0
say() { [ "$quiet" = "-q" ] || echo "$@"; }

out=$(tools/cap.sh bend PROOF.bend 2>&1)
if [ "$(printf '%s\n' "$out" | head -1)" = "ALL PROOFS CHECK" ]; then
  say "ok    PROOF.bend"
else
  echo "FAIL  PROOF.bend"; printf '%s\n' "$out" | head -20; fail=1
fi

for f in tests/*.bend; do
  want=$(sed -n 's/^#|//p' "$f")
  got=$(tools/cap.sh bend "$f" 2>&1)
  if [ "$want" = "$got" ]; then
    say "ok    $f"
  else
    echo "FAIL  $f"; diff <(printf '%s\n' "$want") <(printf '%s\n' "$got") | head -20; fail=1
  fi
done

for f in tests/neg/*.bend; do
  [ "$(basename "$f")" = common.bend ] && continue
  [ -e "$f" ] || continue
  got=$(tools/cap.sh bend "$f" 2>&1 | head -1)
  if [ "$got" = "SOME PROOFS FAIL" ]; then
    say "ok    $f (fails, as a negative control must)"
  else
    echo "FAIL  $f: a negative control passed"; fail=1
  fi
done

[ $fail = 0 ] && say "GATE PASSES" || echo "GATE FAILS"
exit $fail
