#!/usr/bin/env bash
# RHV3Lean — exécution de Comparator sur les cibles gelées.
#
# Maître Lean § M.1, M.4, M.8, M.9.
#
#   run_comparator.sh                    -> cumul de toutes les cibles
#   run_comparator.sh --delta <TOUR_ID>  -> même cumul, étiqueté pour un tour
#
# Statuts émis (§ M.9) : PASS, FAIL_STATEMENT, FAIL_AXIOMS, FAIL_KERNEL,
# INFRA_MISSING, NOT_RUN.  INFRA_MISSING et NOT_RUN ne valent JAMAIS PASS.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

MODE="cumulative"
TOUR_ID="-"
case "${1:-}" in
  "") ;;
  --delta)
    MODE="delta"
    TOUR_ID="${2:?usage: run_comparator.sh --delta <TOUR_ID>}"
    ;;
  *)
    echo "usage: $0 [--delta <TOUR_ID>]" >&2
    exit 64
    ;;
esac

echo "RHV3_COMPARATOR_MODE=$MODE"
echo "RHV3_COMPARATOR_TOUR_ID=$TOUR_ID"

# --- 0. gardes SPECIFICATION et STRENGTH, AVANT toute certification --------
# Comparator compare des ENONCES ; il ne mesure jamais leur FORCE, et il ne
# distingue pas un habitant d'un type d'un objet canoniquement déterminé.  Ces
# deux défauts doivent donc être écartés avant qu'il ne s'exécute, sans quoi il
# certifierait une route dont un contrat vaut la conclusion elle-même.
if ! ./audit_strength.sh "$([[ "$TOUR_ID" != "-" ]] && echo "$TOUR_ID" || true)"; then
  echo "RHV3_COMPARATOR=NOT_RUN"
  echo "REASON=SPECIFICATION_OR_STRENGTH_AUDIT_FAILED"
  exit 6
fi

# --- 1. le blob du challenge doit être resté identique ---------------------
EXPECTED_BLOB="$(tr -d '[:space:]' < Certification/CHALLENGE_FROZEN_GIT_BLOB)"
ACTUAL_BLOB="$(git hash-object Certification/Challenge.lean)"
echo "CHALLENGE_BLOB=$ACTUAL_BLOB"
if [[ "$ACTUAL_BLOB" != "$EXPECTED_BLOB" ]]; then
  echo "CHALLENGE_STATEMENT_MUTATION=1"
  echo "EXPECTED_BLOB=$EXPECTED_BLOB"
  echo "RHV3_COMPARATOR=FAIL_STATEMENT"
  exit 3
fi
echo "CHALLENGE_BLOB_FROZEN=PASS"

# --- 2. les cibles listées doivent exister des DEUX côtés ------------------
missing_target=0
while IFS= read -r fq; do
  name="${fq##*.}"
  grep -qE "^theorem[[:space:]]+${name}([[:space:]]|$)" Certification/Challenge.lean ||
    { echo "TARGET_MISSING_IN_CHALLENGE=$fq"; missing_target=$((missing_target + 1)); }
  grep -qE "^theorem[[:space:]]+${name}([[:space:]]|$)" Certification/Solution.lean ||
    { echo "TARGET_MISSING_IN_SOLUTION=$fq"; missing_target=$((missing_target + 1)); }
done < <(python3 -c '
import json,sys
print("\n".join(json.load(open("Certification/comparator.json"))["theorem_names"]))')
echo "COMPARATOR_TARGETS=$(python3 -c '
import json;print(len(json.load(open("Certification/comparator.json"))["theorem_names"]))')"
echo "TARGETS_MISSING=$missing_target"
if [[ "$missing_target" -ne 0 ]]; then
  echo "RHV3_COMPARATOR=FAIL_STATEMENT"
  exit 3
fi

# --- 3. axiomes autorisés uniquement --------------------------------------
axiom_out="$(lake env lean Certification/PrintAxioms.lean 2>&1)"
if grep -qE "sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler" <<< "$axiom_out"; then
  echo "RHV3_COMPARATOR=FAIL_AXIOMS"
  exit 3
fi
echo "PERMITTED_AXIOMS=[propext, Quot.sound, Classical.choice]"
echo "AXIOMS=PASS"

# --- 4. le replay kernel Comparator ---------------------------------------
# `lean4export` lit les `.olean` du projet : il DOIT être construit avec la
# version Lean exacte du `lean-toolchain`, sinon l'export meurt sur un en-tête
# incompatible.
COMPARATOR_TOOLCHAIN_BIN="${COMPARATOR_TOOLCHAIN_BIN:-$HOME/.local/rhv2-comparator/bin}"
if [[ -d "$COMPARATOR_TOOLCHAIN_BIN" ]]; then
  PATH="$COMPARATOR_TOOLCHAIN_BIN:$PATH"
  export PATH
fi

COMPARATOR_BIN="${COMPARATOR_BIN:-comparator}"
infra_missing=""
command -v "$COMPARATOR_BIN" >/dev/null 2>&1 || infra_missing="comparator"
[[ -n "${COMPARATOR_LEAN4EXPORT:-}" ]] || command -v lean4export >/dev/null 2>&1 ||
  infra_missing="${infra_missing:+$infra_missing,}lean4export"
[[ -n "${COMPARATOR_LANDRUN:-}" ]] || command -v landrun >/dev/null 2>&1 ||
  infra_missing="${infra_missing:+$infra_missing,}landrun"
command -v systemd-run >/dev/null 2>&1 ||
  infra_missing="${infra_missing:+$infra_missing,}systemd-run"

if [[ -n "$infra_missing" ]]; then
  echo "RHV3_COMPARATOR_INFRA_MISSING=$infra_missing"
  echo "RHV3_COMPARATOR=INFRA_MISSING"
  exit 4
fi

EXPECTED_LEAN="$(tr -d '[:space:]' < lean-toolchain | sed 's|.*:v||')"
EXPORT_BIN="${COMPARATOR_LEAN4EXPORT:-lean4export}"
ACTUAL_LEAN="$("$EXPORT_BIN" --version 2>/dev/null |
  sed -n 's/.*"lean":{[^}]*"version":"\([^"]*\)".*/\1/p')"
echo "COMPARATOR_TOOLCHAIN_ID=lean-$EXPECTED_LEAN"
if [[ "$ACTUAL_LEAN" != "$EXPECTED_LEAN" ]]; then
  echo "EXPECTED_LEAN=$EXPECTED_LEAN"
  echo "LEAN4EXPORT_LEAN=${ACTUAL_LEAN:-unknown}"
  echo "RHV3_COMPARATOR=FAIL_KERNEL"
  exit 5
fi

if [[ -z "${COMPARATOR_NANODA:-}" && -x /usr/local/bin/nanoda_bin ]]; then
  COMPARATOR_NANODA=/usr/local/bin/nanoda_bin
fi

SYSTEMD_ENV=(-E "PATH=$PATH")
for var in COMPARATOR_LANDRUN COMPARATOR_LEAN4EXPORT COMPARATOR_NANODA; do
  [[ -n "${!var:-}" ]] && SYSTEMD_ENV+=(-E "$var=${!var}")
done

systemd-run \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --user --pty \
  "${SYSTEMD_ENV[@]}" \
  --working-directory "$ROOT" \
  -- bash -lc "lake env '$COMPARATOR_BIN' Certification/comparator.json"

echo "LEAN_KERNEL_REPLAY=PASS"
echo "RHV3_COMPARATOR=PASS"
