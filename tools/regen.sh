#!/usr/bin/env bash
# Regenerate algebras/ from gen/specs.bend with the Bend generator.
#   tools/regen.sh           write algebras/
#   tools/regen.sh --check   regenerate into a temporary directory and fail
#                            unless algebras/ is byte-identical to it
set -eu
cd "$(dirname "$0")/.."
. tools/env.sh
if [ "${1:-}" = "--check" ]; then
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  bend gen/main.bend "$tmp" > /dev/null
  if diff -r "$tmp" algebras > /dev/null; then
    echo "algebras/ is up to date"
  else
    echo "algebras/ differs from the generator's output; run tools/regen.sh" >&2
    diff -r "$tmp" algebras | head -20 >&2
    exit 1
  fi
else
  bend gen/main.bend algebras
fi
