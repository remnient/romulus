#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== lake build =="
lake build

echo "== proof placeholders in the verified core =="
if grep -rnE '\b(sorry|admit|axiom)\b' romulus romulusTests romulus.lean romulusTests.lean Main.lean; then
  echo "error: proof placeholder found" >&2
  exit 1
fi
echo "none found"

echo "== markdown files =="
stray=$(find . -name '*.md' ! -name 'README.md' ! -path './.lake/*' ! -path './.git/*')
if [ -n "$stray" ]; then
  echo "error: unexpected markdown files:" >&2
  echo "$stray" >&2
  exit 1
fi
echo "only README.md"

echo "== diagrams match their dot sources =="
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
for name in ownership revocation; do
  dot -Tsvg "assets/$name.dot" -o "$tmp/$name.svg"
  if ! diff -q "assets/$name.svg" "$tmp/$name.svg" > /dev/null; then
    echo "error: assets/$name.svg is stale; run scripts/render-graphs.sh" >&2
    exit 1
  fi
done
echo "svgs are current"

echo "== executable scenarios =="
lake exe romulus-demo

echo "all checks passed"
