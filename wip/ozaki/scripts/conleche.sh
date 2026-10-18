#!/usr/bin/env bash
# Re-check every named declaration with con-leche, an external Lean checker proven never to accept
# a proof of False (https://github.com/leanprover/con-leche). Exports each library set with
# lean4export (https://github.com/leanprover/lean4export) and checks it in --verified mode.
#
# Usage: EXPORTER=/path/to/lean4export CHECKER=/path/to/con-leche bash wip/ozaki/scripts/conleche.sh [OUT]
# Both tools must be built for this repository's Lean version (lean4export) or accept its exports
# (con-leche). `example`s are not declarations, so they are not exported or re-checked.
set -uo pipefail
: "${EXPORTER:?set EXPORTER to the lean4export binary}" "${CHECKER:?set CHECKER to the con-leche binary}"
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)"
OUT="${1:-$ROOT/wip/ozaki/.lake/conleche}"; mkdir -p "$OUT"
mods() { (cd "$1" && find "$2" -name '*.lean' | sed 's|\.lean$||; s|/|.|g' | sort); }
check() { # name dir modules...
  local name="$1" dir="$2"; shift 2
  (cd "$dir" && lake env "$EXPORTER" "$@" > "$OUT/$name.ndjson") || { echo "FAIL export $name"; return 1; }
  "$CHECKER" --verified --jobs=4 "$OUT/$name.ndjson" > "$OUT/$name.txt" 2>&1 || { echo "FAIL check $name"; tail -5 "$OUT/$name.txt"; return 1; }
  echo "ok   $name: $(tail -1 "$OUT/$name.txt")"
}
(cd "$ROOT/tensor-core" && lake build TensorCore TensorCoreTests >/dev/null) && (cd "$ROOT/matrix-core" && lake build MatrixCore MatrixCoreTests >/dev/null) || exit 1
check tensorcore "$ROOT/tensor-core" $(mods "$ROOT/tensor-core" TensorCore) TensorCore $(mods "$ROOT/tensor-core/tests" TensorCoreTests) TensorCoreTests
check matrixcore "$ROOT/matrix-core" $(mods "$ROOT/matrix-core" MatrixCore) MatrixCore $(mods "$ROOT/matrix-core/tests" MatrixCoreTests) MatrixCoreTests
check ozaki-tc "$ROOT/wip/ozaki" $(mods "$ROOT/wip/ozaki" Ozaki) Ozaki $(mods "$ROOT/wip/ozaki" OzakiTC) OzakiTC $(mods "$ROOT/wip/ozaki/tests" OzakiTCTests) OzakiTCTests
check ozaki-mc "$ROOT/wip/ozaki" $(mods "$ROOT/wip/ozaki" Ozaki) Ozaki $(mods "$ROOT/wip/ozaki" OzakiMC) OzakiMC $(mods "$ROOT/wip/ozaki/tests" OzakiMCTests) OzakiMCTests
