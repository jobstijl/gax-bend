#!/usr/bin/env bash
# Regenerate the generated sources with the Bend generators:
#   algebras/          from gen/main.bend (kernels, kinds, mirror proofs)
#                      and gen/equiv_main.bend (equiv_all.bend: the
#                      equivariance laws for every kind pair)
#   proofs/<generated> from gen/proofs/main.bend (the Layer-S proof modules
#                      and the rounding-error theorem, err.bend;
#                      proofs/base, leaf, add and sgn are hand-written)
#   tools/regen.sh                   write all of them but equiv_all.bend
#   tools/regen.sh --equiv           write all of them
#   tools/regen.sh --check           regenerate into temporary directories and
#                                    fail unless the committed files are
#                                    byte-identical (equiv_all.bend excepted)
#   tools/regen.sh --check --equiv   the same, equiv_all.bend included
# gen/equiv_main.bend runs as a native build with an unlimited stack: its
# polynomials nest deeper than the interpreter's stack allows. It takes
# about half an hour (CGA3D's null-basis laws), so only --equiv runs
# it (tools/gate.sh --full does).
set -eu
cd "$(dirname "$0")/.."
. tools/env.sh
check=""
equiv=""
for a in "$@"; do
  case "$a" in
    --check) check=1 ;;
    --equiv) equiv=1 ;;
  esac
done
gbin=$(mktemp -d)
trap 'rm -rf "$gbin"' EXIT
equiv_gen() {
  bend gen/equiv_main.bend -o "$gbin/equiv" > /dev/null
  (ulimit -s unlimited; "$gbin/equiv" "$1" > /dev/null)
}
if [ -n "$check" ]; then
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp" "$gbin"' EXIT
  mkdir "$tmp/algebras" "$tmp/proofs"
  bend gen/main.bend "$tmp/algebras" > /dev/null
  bend gen/proofs/main.bend "$tmp/proofs" > /dev/null
  excl="-x equiv_all.bend"
  if [ -n "$equiv" ]; then equiv_gen "$tmp/algebras"; excl=""; fi
  bad=0
  if diff -r $excl "$tmp/algebras" algebras > /dev/null; then
    echo "algebras/ is up to date"
  else
    echo "algebras/ differs from the generator's output; run tools/regen.sh" >&2
    diff -r $excl "$tmp/algebras" algebras | head -20 >&2
    bad=1
  fi
  for f in "$tmp"/proofs/*.bend; do
    g=proofs/$(basename "$f")
    if ! cmp -s "$f" "$g"; then
      echo "$g differs from the proof writer's output; run tools/regen.sh" >&2
      diff "$f" "$g" | head -20 >&2
      bad=1
    fi
  done
  [ $bad = 0 ] && echo "proofs/ is up to date"
  exit $bad
else
  bend gen/main.bend algebras
  if [ -n "$equiv" ]; then equiv_gen algebras; fi
  bend gen/proofs/main.bend proofs
fi
