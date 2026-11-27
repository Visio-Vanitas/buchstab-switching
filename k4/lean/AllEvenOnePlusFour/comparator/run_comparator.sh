#!/bin/bash
# Comparator run for lean/AllEvenOnePlusFour (needs elan; Lean v4.36.0 ships lake comparator,
# leanexport, leanchecker-paranoid and nanoda_bin). Output goes to comparator_output.txt.
# It runs comparator without its sandbox, so run it in a VM or sandbox of your own.
set -u
cd "$(dirname "$0")/.."; R=$PWD
export PATH="$HOME/.elan/bin:$PATH" LEAN_ABORT_ON_PANIC=1
O=$R/comparator_output.txt
log(){ echo "$@" | tee -a $O; }
run(){ log "\$ $*"; "$@" >> $O 2>&1; r=$?; log "[exit $r]"; return $r; }
: > $O; mkdir -p .lake
log "== toolchain"; run lean --version; run lake --version
log "== Mathlib cache"; lake exe cache get > .lake/cache.log 2>&1; log "[cache exit $?] (Mathlib only; the project itself is compiled below)"
log "== build"; run lake build Challenge AllEvenOnePlusFour
T=$R/.lake/exp; mkdir -p $T
if command -v cygpath >/dev/null 2>&1; then
  R_HOST="$(cygpath -m "$R")"
  T_HOST="$R_HOST/.lake/exp"
  COMP_HOST="$R_HOST/.lake/comparator"
  P="$(cygpath -u "$(lean --print-prefix)")/bin"
  PW="$(cygpath -m "$(lean --print-prefix)")/bin"
else
  R_HOST="$R"
  T_HOST="$T"
  COMP_HOST="$PWD/.lake/comparator"
  P="$(lean --print-prefix)/bin"
  PW="$P"
fi
log "== setup 1: comparator.json (challenge Challenge.lean, theorem all_even_one_plus_four)"
run bash -c "lake env leanexport Challenge -- \$(tr -d '\r' < export-targets.txt) > '$T/challenge.export'"
run bash -c "lake env leanexport AllEvenOnePlusFour -- \$(tr -d '\r' < export-targets.txt) > '$T/solution.export'"
SHA_TOOL=$(command -v sha256sum || echo "shasum -a 256")
log "sha256: $($SHA_TOOL "$T/challenge.export" | cut -c1-64) challenge.export; $($SHA_TOOL "$T/solution.export" | cut -c1-64) solution.export"
log "external kernels available: $(ls "$P" | grep -E 'leanchecker|nanoda' | tr '\n' ' ')"
if [ -f "$P/leanchecker-paranoid.exe" ]; then
  sed "s|\"leanchecker-paranoid\"|\"$PW/leanchecker-paranoid.exe\"|g; s|\"nanoda_bin\"|\"$PW/nanoda_bin.exe\"|g" "$R/comparator.json" > "$T/comparator.runtime.json"
  sed "s|\"leanchecker-paranoid\"|\"$PW/leanchecker-paranoid.exe\"|g; s|\"nanoda_bin\"|\"$PW/nanoda_bin.exe\"|g" "$R/comparator/reduction.json" > "$T/reduction.runtime.json"
else
  cp "$R/comparator.json" "$T/comparator.runtime.json"
  cp "$R/comparator/reduction.json" "$T/reduction.runtime.json"
fi
rm -rf "$T/j1" "$T/j2" "$T/j3"
mkdir -p "$T/j1" && (cd "$T/j1" && PATH="$P:$PATH" run lake comparator --inadvisably-no-sandbox --config "$T_HOST/comparator.runtime.json" --challenge-from-export "$T_HOST/challenge.export" --solution-from-export "$T_HOST/solution.export")
log "== setup 2: comparator/reduction.json (challenge comparator/ChallengeReduction.lean, the conditional reduction)"
mkdir -p .lake/comparator
for m in ChallengeReductionStatement ChallengeReductionWeights ChallengeReduction; do
  run env LEAN_PATH="$COMP_HOST" lake env lean --root=comparator -o ".lake/comparator/$m.olean" "comparator/$m.lean"
done
run bash -c "LEAN_PATH='$COMP_HOST' lake env leanexport ChallengeReduction -- \$(tr -d '\r' < comparator/reduction-export-targets.txt) > '$T/red-challenge.export'"
run bash -c "lake env leanexport AllEvenOnePlusFour -- \$(tr -d '\r' < comparator/reduction-export-targets.txt) > '$T/red-solution.export'"
log "sha256: $($SHA_TOOL "$T/red-challenge.export" | cut -c1-64) red-challenge.export; $($SHA_TOOL "$T/red-solution.export" | cut -c1-64) red-solution.export"
mkdir -p "$T/j2" && (cd "$T/j2" && PATH="$P:$PATH" run lake comparator --inadvisably-no-sandbox --config "$T_HOST/reduction.runtime.json" --challenge-from-export "$T_HOST/red-challenge.export" --solution-from-export "$T_HOST/red-solution.export")
log "== rehearsal: setup 2 with the challenge itself as solution (must be rejected for sorryAx)"
mkdir -p "$T/j3" && (cd "$T/j3" && PATH="$P:$PATH" run lake comparator --inadvisably-no-sandbox --config "$T_HOST/reduction.runtime.json" --challenge-from-export "$T_HOST/red-challenge.export" --solution-from-export "$T_HOST/red-challenge.export")
log "== DONE"
