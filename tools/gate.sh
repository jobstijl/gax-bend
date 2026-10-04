#!/usr/bin/env bash
# The project gate. Passes only when
#   1. `bend PROOF.bend` prints ALL PROOFS CHECK,
#   2. algebras/ and the generated proofs/ modules are what the generators
#      write (tools/regen.sh --check),
#   3. every generated algebras/*/proofs.bend checks (kernel == spec), and
#      every algebras/*/f32.bend checks,
#   4. every tests/*.bend and examples/*.bend prints exactly the `#|` lines
#      it ends with,
#   5. every negative control tests/neg/*.bend fails to check.
# Usage: tools/gate.sh [-q] [--full]
#   -q      one line per failure only
#   --full  also check the slow proof files (CGA3D's, about an hour).
#   --csta  also check CSTA's proof files (estimated at about 10 hours;
#           not yet run in full). Without these flags they are counted as
#           skipped.
set -u
cd "$(dirname "$0")/.."
. tools/env.sh
quiet=""
full=""
csta=""
for a in "$@"; do
  case "$a" in
    -q) quiet=-q ;;
    --full) full=1 ;;
    --csta) csta=1 ;;
  esac
done
SLOW="algebras/cga3d/"
SLOWER="algebras/csta/"
fail=0
say() { [ "$quiet" = "-q" ] || echo "$@"; }

out=$(tools/cap.sh bend PROOF.bend 2>&1)
if [ "$(printf '%s\n' "$out" | head -1)" = "ALL PROOFS CHECK" ]; then
  say "ok    PROOF.bend"
else
  echo "FAIL  PROOF.bend"; printf '%s\n' "$out" | head -20; fail=1
fi

if tools/regen.sh --check > /dev/null 2>&1; then
  say "ok    algebras/ and proofs/ match the generators"
else
  echo "FAIL  generated sources are stale: run tools/regen.sh"; fail=1
fi

skipped=0
for f in algebras/*/proofs.bend algebras/*/proofs_*.bend; do
  [ -e "$f" ] || continue
  case "$f" in
    "$SLOW"*) if [ -z "$full" ]; then skipped=$((skipped + 1)); continue; fi ;;
    "$SLOWER"*) if [ -z "$csta" ]; then skipped=$((skipped + 1)); continue; fi ;;
  esac
  out=$(tools/cap.sh bend "$f" 2>&1)
  if [ "$(printf '%s\n' "$out" | head -1)" = "ALL PROOFS CHECK" ]; then
    say "ok    $f"
  else
    echo "FAIL  $f"; printf '%s\n' "$out" | head -20; fail=1
  fi
done

[ $skipped = 0 ] || echo "skip  $skipped proof files under $SLOW and $SLOWER (slow: tools/gate.sh --full, --csta)"

for f in algebras/*/f32.bend; do
  [ -e "$f" ] || continue
  out=$(tools/cap.sh bend "$f" --check-only 2>&1)
  if [ "$(printf '%s\n' "$out" | head -1)" = "ALL PROOFS CHECK" ]; then
    say "ok    $f"
  else
    echo "FAIL  $f"; printf '%s\n' "$out" | head -20; fail=1
  fi
done

for f in tests/*.bend examples/*.bend; do
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
