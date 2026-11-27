#!/bin/bash
set -u
cd "$(dirname "$0")/.."; R=$PWD
export PATH="$HOME/.elan/bin:$PATH" LEAN_ABORT_ON_PANIC=1
O="$R/comparator_output.txt"
log(){ echo "$@" | tee -a "$O"; }
run(){ log "\$ $*"; "$@" >> "$O" 2>&1; r=$?; log "[exit $r]"; return $r; }
: > "$O"; mkdir -p .lake
log "== toolchain"; run lean --version; run lake --version
log "== build BuchstabSwitching"; run lake build BuchstabSwitching
log "== axioms check"; run lake env lean AxiomsCheckK3.lean
run lake env lean BuchstabSwitching/Sieve/AxiomsAudit.lean
T="$R/.lake/exp"; mkdir -p "$T" .lake/comparator
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
cp BuchstabSwitching/Certificates/Types.lean comparator/ChallengeK3Types.lean
sed 's/import BuchstabSwitching.Certificates.Types/import ChallengeK3Types/' BuchstabSwitching/Certificates/Data.lean > comparator/ChallengeK3Data.lean
for m in ChallengeK3Types ChallengeK3Data ChallengeK3MertensTwoVar ChallengeK3DirichletGRH ChallengeK3Schoenfeld ChallengeK3MertensExt ChallengeK3Constants ChallengeK3Reduction; do
  run env LEAN_PATH="$COMP_HOST" lake env lean --root=comparator -o ".lake/comparator/$m.olean" "comparator/$m.lean"
done
ulimit -s hard 2>/dev/null || true
run bash -c "LEAN_PATH='$COMP_HOST' lake env leanexport ChallengeK3Reduction -- \$(tr -d '\r' < comparator/reduction-export-targets.txt) > '$T/red-challenge.export'"
run bash -c "lake env leanexport BuchstabSwitching -- \$(tr -d '\r' < comparator/reduction-export-targets.txt) > '$T/red-solution.export'"
SHA_TOOL=$(command -v sha256sum || echo "shasum -a 256")
log "sha256: $($SHA_TOOL "$T/red-challenge.export" | cut -d' ' -f1) red-challenge.export; $($SHA_TOOL "$T/red-solution.export" | cut -d' ' -f1) red-solution.export"
log "external kernels available: $(ls "$P" | grep -E 'leanchecker|nanoda' | tr '\n' ' ')"
if [ -f "$P/leanchecker-paranoid.exe" ]; then
  sed "s|\"leanchecker-paranoid\"|\"$PW/leanchecker-paranoid.exe\"|g; s|\"nanoda_bin\"|\"$PW/nanoda_bin.exe\"|g" "$R/comparator/reduction.json" > "$T/reduction.runtime.json"
else
  cp "$R/comparator/reduction.json" "$T/reduction.runtime.json"
fi
rm -rf "$T/j2" "$T/j3"
mkdir -p "$T/j2" && (cd "$T/j2" && PATH="$P:$PATH" run lake comparator --inadvisably-no-sandbox --config "$T_HOST/reduction.runtime.json" --challenge-from-export "$T_HOST/red-challenge.export" --solution-from-export "$T_HOST/red-solution.export")
log "== rehearsal: self-challenge (must reject sorryAx)"
mkdir -p "$T/j3" && (cd "$T/j3" && PATH="$P:$PATH" run lake comparator --inadvisably-no-sandbox --config "$T_HOST/reduction.runtime.json" --challenge-from-export "$T_HOST/red-challenge.export" --solution-from-export "$T_HOST/red-challenge.export")
log "== DONE"
