#!/usr/bin/env bash
# Regenerate the generated sources with the Bend generators:
#   algebras/          from gen/main.bend (kernels, kinds, mirror proofs)
#   proofs/<generated> from gen/proofs/main.bend (the Layer-S proof modules
#                      and the rounding-error theorem, err.bend;
#                      proofs/base, leaf, add and sgn are hand-written)
#   tools/regen.sh           write both
#   tools/regen.sh --check   regenerate into temporary directories and fail
#                            unless the committed files are byte-identical
set -eu
cd "$(dirname "$0")/.."
. tools/env.sh
if [ "${1:-}" = "--check" ]; then
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  mkdir "$tmp/algebras" "$tmp/proofs"
  bend gen/main.bend "$tmp/algebras" > /dev/null
  bend gen/proofs/main.bend "$tmp/proofs" > /dev/null
  bad=0
  if diff -r "$tmp/algebras" algebras > /dev/null; then
    echo "algebras/ is up to date"
  else
    echo "algebras/ differs from the generator's output; run tools/regen.sh" >&2
    diff -r "$tmp/algebras" algebras | head -20 >&2
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
  bend gen/proofs/main.bend proofs
fi
