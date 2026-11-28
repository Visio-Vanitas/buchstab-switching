#!/usr/bin/env bash
set -u
cd "$(dirname "$0")/.."
R="$PWD"
export PATH="$HOME/.elan/bin:$PATH" LEAN_ABORT_ON_PANIC=1
O="$R/comparator_output.txt"
log() { echo "$@" | tee -a "$O"; }
run() { log "\$ $*"; "$@" >> "$O" 2>&1; local r=$?; log "[exit $r]"; return $r; }
: > "$O"
mkdir -p .lake .lake/comparator .lake/exp
log "== toolchain"
run lean --version || exit 1
run lake --version || exit 1
log "== build OnePlusOne"
run lake build OnePlusOne || exit 1
log "== axioms check"
run lake env lean AxiomsCheckOnePlusOne.lean || exit 1

T="$R/.lake/exp"
COMP="$R/.lake/comparator"
P="$(lean --print-prefix)/bin"

for m in ChallengeOnePlusOneDefs ChallengeOnePlusOnePremises ChallengeOnePlusOneReduction; do
  run env LEAN_PATH="$COMP" lake env lean -Dpp.unicode.fun=true -DautoImplicit=false -DrelaxedAutoImplicit=false --root=comparator -o "$COMP/$m.olean" "comparator/$m.lean" || exit 1
done

ulimit -s hard 2>/dev/null || true
run bash -c "LEAN_PATH='$COMP' lake env leanexport ChallengeOnePlusOneReduction -- \$(tr -d '\r' < comparator/reduction-export-targets.txt) > '$T/red-challenge.export'" || exit 1
run bash -c "lake env leanexport OnePlusOne -- \$(tr -d '\r' < comparator/reduction-export-targets.txt) > '$T/red-solution.export'" || exit 1

SHA_TOOL=$(command -v sha256sum || echo "shasum -a 256")
log "sha256: $($SHA_TOOL "$T/red-challenge.export" | cut -d' ' -f1) red-challenge.export; $($SHA_TOOL "$T/red-solution.export" | cut -d' ' -f1) red-solution.export"
log "external kernels available: $(ls "$P" | grep -E 'leanchecker|nanoda' | tr '\n' ' ')"

rm -rf "$T/j2" "$T/j3"
mkdir -p "$T/j2"
(cd "$T/j2" && PATH="$P:$PATH" run lake comparator --inadvisably-no-sandbox --config "$R/comparator/reduction.json" --challenge-from-export "$T/red-challenge.export" --solution-from-export "$T/red-solution.export") || exit 1

log "== rehearsal: self-challenge (must reject sorryAx)"
mkdir -p "$T/j3"
set +e
(cd "$T/j3" && PATH="$P:$PATH" run lake comparator --inadvisably-no-sandbox --config "$R/comparator/reduction.json" --challenge-from-export "$T/red-challenge.export" --solution-from-export "$T/red-challenge.export")
SELF_RC=$?
set -e
if [ "$SELF_RC" -eq 0 ]; then
  log "ERROR: self-challenge unexpectedly succeeded!"
  exit 1
fi
log "== DONE (comparator verified, self-challenge rejected with exit $SELF_RC)"
