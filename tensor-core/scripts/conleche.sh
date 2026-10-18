#!/usr/bin/env bash
# Re-check every declaration of `TensorCore` and `TensorCoreTests` with con-leche, an external Lean checker
# proven never to accept a proof of False (https://github.com/leanprover/con-leche), from a
# lean4export export (https://github.com/leanprover/lean4export). `example`s are not declarations,
# so they are not exported or re-checked.
#
# Usage: EXPORTER=/path/to/lean4export CHECKER=/path/to/con-leche bash scripts/conleche.sh [OUT]
set -uo pipefail
: "${EXPORTER:?set EXPORTER to the lean4export binary}" "${CHECKER:?set CHECKER to the con-leche binary}"
cd "$(dirname -- "${BASH_SOURCE[0]}")/.."
OUT="${1:-.lake/conleche}"; mkdir -p "$OUT"
mods() { (cd "$1" && find "$2" -name '*.lean' | sed 's|\.lean$||; s|/|.|g' | sort); }
lake build TensorCore TensorCoreTests >/dev/null || exit 1
lake env "$EXPORTER" $(mods . TensorCore) TensorCore $(mods tests TensorCoreTests) TensorCoreTests > "$OUT/tensorcore.ndjson" || { echo "FAIL export"; exit 1; }
"$CHECKER" --verified --jobs=4 "$OUT/tensorcore.ndjson" > "$OUT/tensorcore.txt" 2>&1 || { echo "FAIL check"; tail -5 "$OUT/tensorcore.txt"; exit 1; }
rm -f "$OUT/tensorcore.ndjson"
echo "ok   tensorcore: $(tail -1 "$OUT/tensorcore.txt")"
