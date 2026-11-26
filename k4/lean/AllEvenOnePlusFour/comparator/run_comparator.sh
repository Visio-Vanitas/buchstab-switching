#!/bin/bash
# Comparator run for lean/AllEvenOnePlusFour (needs elan; Lean v4.37.0-rc1 ships lake comparator,
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
log "== setup 1: comparator.json (challenge Challenge.lean, theorem all_even_one_plus_four)"
run bash -c "lake env leanexport Challenge -- \$(cat export-targets.txt) > $T/challenge.export"
run bash -c "lake env leanexport AllEvenOnePlusFour -- \$(cat export-targets.txt) > $T/solution.export"
log "sha256: $(sha256sum $T/challenge.export | cut -c1-64) challenge.export; $(sha256sum $T/solution.export | cut -c1-64) solution.export"
P="$(lean --print-prefix)/bin"; log "external kernels available: $(ls $P | grep -E 'leanchecker|nanoda' | tr '\n' ' ')"
mkdir -p $T/j1 && (cd $T/j1 && PATH="$P:$PATH" run lake comparator --inadvisably-no-sandbox --config $R/comparator.json --challenge-from-export $T/challenge.export --solution-from-export $T/solution.export)
log "== setup 2: comparator/reduction.json (challenge comparator/ChallengeReduction.lean, the conditional reduction)"
mkdir -p .lake/comparator
for m in ChallengeReductionStatement ChallengeReductionWeights ChallengeReduction; do
  run env LEAN_PATH=$PWD/.lake/comparator lake env lean --root=comparator -o .lake/comparator/$m.olean comparator/$m.lean
done
run bash -c "LEAN_PATH=$PWD/.lake/comparator lake env leanexport ChallengeReduction -- \$(cat comparator/reduction-export-targets.txt) > $T/red-challenge.export"
run bash -c "lake env leanexport AllEvenOnePlusFour -- \$(cat comparator/reduction-export-targets.txt) > $T/red-solution.export"
log "sha256: $(sha256sum $T/red-challenge.export | cut -c1-64) red-challenge.export; $(sha256sum $T/red-solution.export | cut -c1-64) red-solution.export"
mkdir -p $T/j2 && (cd $T/j2 && PATH="$P:$PATH" run lake comparator --inadvisably-no-sandbox --config $R/comparator/reduction.json --challenge-from-export $T/red-challenge.export --solution-from-export $T/red-solution.export)
log "== rehearsal: setup 2 with the challenge itself as solution (must be rejected for sorryAx)"
mkdir -p $T/j3 && (cd $T/j3 && PATH="$P:$PATH" run lake comparator --inadvisably-no-sandbox --config $R/comparator/reduction.json --challenge-from-export $T/red-challenge.export --solution-from-export $T/red-challenge.export)
log "== DONE"
