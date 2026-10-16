#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== regenerating graphviz diagrams =="
dot -Tsvg assets/ownership.dot -o assets/ownership.svg
dot -Tsvg assets/revocation.dot -o assets/revocation.svg
echo "wrote assets/ownership.svg assets/revocation.svg"
