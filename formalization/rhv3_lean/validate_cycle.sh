#!/usr/bin/env bash
# RHV3Lean — porte globale de validation d'un tour (maître Lean § N.11, M.10).
#
#   validate_cycle.sh <TOUR_ID> [--with-comparator]
#
# Agrège : build, audit de contrats, Comparator delta, audit de fidélité,
# axiomes.  Ne renvoie PASS que si TOUT passe.  Comparator est coûteux (export
# de l'environnement complet) : il est exécuté sur demande explicite, et son
# absence d'exécution est enregistrée comme NOT_RUN, jamais comme PASS.
set -euo pipefail
cd "$(dirname "$0")"

TOUR_ID="${1:?usage: validate_cycle.sh <TOUR_ID> [--with-comparator]}"
WITH_COMPARATOR="${2:-}"

fail=0
run() {
  local label="$1"; shift
  if "$@" > "/tmp/rhv3_${label}.log" 2>&1; then
    echo "${label}=PASS"
  else
    echo "${label}=FAIL"
    tail -20 "/tmp/rhv3_${label}.log" >&2
    fail=1
  fi
}

echo "RHV3_CYCLE_TOUR_ID=$TOUR_ID"

run BUILD lake build
run CONTRACT_AUDIT ./audit_contracts.sh
run SPECIFICATION_STRENGTH_AUDIT ./audit_strength.sh "$TOUR_ID"
run FIDELITY_AUDIT ./audit_fidelity.sh "$TOUR_ID"

# axiomes : seuls propext / Quot.sound / Classical.choice sont permis
if lake env lean Certification/PrintAxioms.lean 2>&1 |
    grep -qE 'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler'; then
  echo "AXIOMS=FAIL"
  fail=1
else
  echo "AXIOMS=PASS"
fi

if [[ "$WITH_COMPARATOR" == "--with-comparator" ]]; then
  run COMPARATOR_DELTA ./Certification/run_comparator.sh --delta "$TOUR_ID"
else
  echo "COMPARATOR_DELTA=NOT_RUN"
  echo "NOTE=NOT_RUN n'est jamais PASS (maître M.9) ; relancer avec --with-comparator"
  fail=1
fi

if [[ "$fail" -ne 0 ]]; then
  echo "RHV3_CYCLE_VALIDATION=FAIL"
  exit 2
fi
echo "RHV3_CYCLE_VALIDATION=PASS"
