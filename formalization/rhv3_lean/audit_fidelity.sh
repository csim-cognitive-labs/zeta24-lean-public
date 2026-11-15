#!/usr/bin/env bash
# RHV3Lean — audit de fidélité d'un tour (maître Lean § N.2, N.3, N.4).
#
#   audit_fidelity.sh <TOUR_ID>
#
# Il ne remplace pas le raisonnement : il rend MECANIQUE tout ce qui peut
# l'être, parce qu'un rapport de fidélité écrit à la main a déjà été faux dans
# ce projet.  Il refuse un tour dont le manifeste est absent, incomplet, ou dont
# la colonne FIDELITE emploie un mot non autorisé.
set -euo pipefail
cd "$(dirname "$0")"

TOUR_ID="${1:?usage: audit_fidelity.sh <TOUR_ID>}"
MANIFEST="audits/tours/${TOUR_ID}.md"

fail=0
echo "RHV3_FIDELITY_TOUR_ID=$TOUR_ID"

# --- 1. le manifeste du tour existe et porte les champs imposés ------------
if [[ ! -f "$MANIFEST" ]]; then
  echo "TOUR_MANIFEST_MISSING=$MANIFEST"
  echo "RHV3_FIDELITY_AUDIT=FAIL"
  exit 2
fi
echo "TOUR_MANIFEST=$MANIFEST"

required_fields=(
  TOUR_ID TIMESTAMP HEAD_BEFORE HEAD_AFTER ORIGIN_MAIN_SHA FILES_CHANGED
  PUBLIC_REALISERS_ADDED PUBLIC_REALISERS_MODIFIED SEMANTIC_STEPS
  MATHEMATICAL_STEPS COMPARATOR_TARGETS COMPARATOR_DELTA_RESULT
  CONTRACT_AUDIT_RESULT FIDELITY_AUDIT_RESULT SAME_OBJECT_RESULTS
  AXIOMS_RESULT BUILD_RESULT RESIDUAL_OBLIGATIONS_BEFORE
  RESIDUAL_OBLIGATIONS_AFTER NEXT_CONSUMER PUSH_STATUS
)
missing_fields=0
for f in "${required_fields[@]}"; do
  if ! grep -qE "^[[:space:]]*${f}[[:space:]]*=" "$MANIFEST"; then
    echo "MANIFEST_FIELD_MISSING=$f"
    missing_fields=$((missing_fields + 1))
  fi
done
echo "MANIFEST_FIELDS_MISSING=$missing_fields"
[[ "$missing_fields" -eq 0 ]] || fail=1

# --- 2. la colonne FIDELITE n'emploie que le vocabulaire autorisé ----------
# N.3 : EXACT | PARTIAL | CONDITIONAL | MISSING | CONTRADICTS_MASTER.
bad_verdicts=0
while IFS= read -r verdict; do
  case "$verdict" in
    EXACT|PARTIAL|CONDITIONAL|MISSING|CONTRADICTS_MASTER) ;;
    *) echo "FIDELITY_VERDICT_NOT_ALLOWED=$verdict"; bad_verdicts=$((bad_verdicts + 1)) ;;
  esac
done < <(
  grep -E '^\|' "$MANIFEST" | grep -v '^|---' |
    awk -F'|' 'NF>2 {gsub(/ /,"",$(NF-1)); print $(NF-1)}' |
    grep -vE '^(Fidélité|Fidelite|)$' || true
)
echo "FIDELITY_VERDICTS_NOT_ALLOWED=$bad_verdicts"
[[ "$bad_verdicts" -eq 0 ]] || fail=1

# --- 3. « 100 % » n'est écrit que si aucune ligne n'est non-EXACT ----------
if grep -qE '100[[:space:]]*%' "$MANIFEST"; then
  non_exact="$(
    grep -E '^\|' "$MANIFEST" | grep -v '^|---' |
      awk -F'|' 'NF>2 {gsub(/ /,"",$(NF-1)); print $(NF-1)}' |
      grep -cE '^(PARTIAL|CONDITIONAL|MISSING|CONTRADICTS_MASTER)$' || true
  )"
  echo "HUNDRED_PERCENT_CLAIMED=1"
  echo "NON_EXACT_ROWS=$non_exact"
  if [[ "$non_exact" -ne 0 ]]; then
    echo "HUNDRED_PERCENT_NOT_ALLOWED=1"
    fail=1
  fi
else
  echo "HUNDRED_PERCENT_CLAIMED=0"
fi

# --- 4. audit NEGATIF sur le code exécutable (N.4) -------------------------
# Code seul : les commentaires citent volontairement les lois retirées pour
# expliquer pourquoi elles sont interdites.
lean_code="$(
  find RHV3Lean Certification -name '*.lean' -print0 2>/dev/null | xargs -0 -r cat |
    perl -0777 -pe 's{/-.*?-/}{}gs; s/--.*$//gm'
)"

negative=0
report_negative() {
  echo "NEGATIVE_CHECK_FAIL=$1"
  negative=$((negative + 1))
}

# 4a. noms révoqués. T1/count-one est désormais une loi active ; l'audit ne
# doit plus la rejeter, mais les sélections par adresse imposée restent exclues.
if grep -qE '\bO-ADR\b|\bO-SEP\b' <<< "$lean_code"; then
  report_negative REVOKED_NAME_IN_CODE
fi

# 4b. anti-circularité : aucune surface publique ne peut prendre RH en entrée,
#     hors le contrôle explicite qui lit la position radiale SOUS RH.
#     Deux conditions, toutes deux mecaniques : le nom doit figurer dans la
#     liste `audits/RH_REVERSE_CONTROLS.txt`, ET aucune autre declaration de
#     RHV3Lean ne doit le referencer, de sorte qu'il ne peut alimenter aucun
#     theoreme de la route.
rh_controls="$(grep -vE '^[[:space:]]*(#|$)' audits/RH_REVERSE_CONTROLS.txt || true)"
route_code="$(
  find RHV3Lean -name '*.lean' -print0 2>/dev/null | xargs -0 -r cat |
    perl -0777 -pe 's{/-.*?-/}{}gs; s/--.*$//gm'
)"
rh_consumers=0
while IFS= read -r decl; do
  [[ -n "$decl" ]] || continue
  if ! grep -qxF "$decl" <<< "$rh_controls"; then
    echo "RH_HYPOTHESIS_NOT_DECLARED_AS_CONTROL=$decl"
    rh_consumers=$((rh_consumers + 1))
    continue
  fi
  uses="$( { grep -oE "\\b${decl}\\b" <<< "$route_code" || true; } | wc -l)"
  if [[ "$uses" -gt 1 ]]; then
    echo "RH_CONTROL_IS_CONSUMED_BY_THE_ROUTE=$decl"
    rh_consumers=$((rh_consumers + 1))
  fi
done < <(
  awk '
    /^(noncomputable[ \t]+)?(theorem|def)[ \t]+[A-Za-z_]/ {
      match($0, /(theorem|def)[ \t]+[A-Za-z_][A-Za-z_0-9]*/)
      decl = substr($0, RSTART, RLENGTH)
      sub(/^(theorem|def)[ \t]+/, "", decl)
      current = decl
    }
    /\(h[A-Za-z]*[ \t]*:[ \t]*RiemannHypothesis\)/ { if (current != "") print current }
  ' <<< "$lean_code" | sort -u
)
echo "RH_HYPOTHESIS_CONSUMERS=$rh_consumers"
if [[ "$rh_consumers" -gt 0 ]]; then
  report_negative RIEMANN_HYPOTHESIS_USED_AS_HYPOTHESIS
fi

# 4c. recherche de kappa ou m : S4 l'interdit explicitement.
if grep -qE '(fn|find|search|choose)[A-Za-z]*(Kappa|Span|EntryAddress)[A-Za-z]*[[:space:]]*\(' <<< "$lean_code"; then
  report_negative SEARCH_FUNCTION_FOR_KAPPA_OR_M
fi

# 4d. R-ATT hors portée : aucun théorème ne peut conclure que deux occurrences
#     de provenances distinctes portent des premiers distincts.
if grep -qE 'tProvenance.*≠.*nPrime|nPrime.*≠.*tProvenance' <<< "$lean_code"; then
  report_negative R_ATT_USED_TO_SEPARATE_PRIMES
fi

# 4e. trous statiques et axiomes
if grep -qE '\b(sorry|admit)\b|^[[:space:]]*(axiom|constant)[[:space:]]' <<< "$lean_code"; then
  report_negative STATIC_HOLE_OR_AXIOM
fi

echo "NEGATIVE_CHECKS_FAILED=$negative"
[[ "$negative" -eq 0 ]] || fail=1

# --- 5. SAME-OBJECT : un seul porteur CANONIQUE ----------------------------
# Les habitants de CONTROLE et les applications DERIVEES entre porteurs sont
# déclarés dans `audits/`, et ne comptent pas : un habitant ne détermine rien,
# une application dérivée ne fait que traduire un porteur déjà donné.  Ce qui
# est compté ici, ce sont les porteurs prétendument canoniques.
declared_controls="$(
  { grep -vE '^[[:space:]]*(#|$)' audits/CONTROL_ONLY_INHABITANTS.txt || true
    grep -vE '^[[:space:]]*(#|$)' audits/DERIVED_CARRIER_MAPS.txt || true; }
)"
canonical_carriers=0
while IFS= read -r decl; do
  [[ -n "$decl" ]] || continue
  grep -qxF "$decl" <<< "$declared_controls" || {
    echo "CANONICAL_CARRIER_CLAIMED=$decl"
    canonical_carriers=$((canonical_carriers + 1))
  }
done < <(
  grep -oE "^(noncomputable[[:space:]]+)?def[[:space:]]+[A-Za-z_][A-Za-z_0-9]*[[:space:]]*:[[:space:]]*(TCanonicalTowerOperator|TTrueTowerCarrier)([[:space:]]|$)" <<< "$lean_code" |
    sed -E 's/^(noncomputable[[:space:]]+)?def[[:space:]]+([A-Za-z_][A-Za-z_0-9]*).*/\2/' | sort -u
)
echo "CANONICAL_CARRIERS_CLAIMED=$canonical_carriers"
if [[ "$canonical_carriers" -gt 1 ]]; then
  echo "SAME_OPERATOR=FAIL"
  fail=1
elif [[ "$canonical_carriers" -eq 1 ]]; then
  echo "SAME_OPERATOR=PASS"
else
  echo "SAME_OPERATOR=PASS_NO_CANONICAL_CARRIER_CLAIMED"
fi

# --- 6. couverture Comparator des cibles du tour ---------------------------
uncovered=0
while IFS= read -r name; do
  [[ -n "$name" ]] || continue
  [[ "$name" != "-" && "$name" != "aucun" ]] || continue
  grep -qF "$name" Certification/Challenge.lean ||
    { echo "TOUR_TARGET_NOT_IN_CHALLENGE=$name"; uncovered=$((uncovered + 1)); }
done < <(
  # Le champ vaut soit une liste de noms `cmp_*`, soit le chemin d'une
  # configuration Comparator dont on lit les cibles.
  raw="$(sed -n 's/^[[:space:]]*COMPARATOR_TARGETS[[:space:]]*=[[:space:]]*//p' "$MANIFEST")"
  if [[ "$raw" == *comparator.json* ]]; then
    python3 -c '
import json
print("\n".join(n.split(".")[-1]
      for n in json.load(open("Certification/comparator.json"))["theorem_names"]))'
  else
    tr ', ' '\n\n' <<< "$raw" | sed '/^$/d' | grep -E '^cmp_' || true
  fi
)
echo "TOUR_TARGETS_NOT_COVERED=$uncovered"
[[ "$uncovered" -eq 0 ]] || fail=1

if [[ "$fail" -ne 0 ]]; then
  echo "RHV3_FIDELITY_AUDIT=FAIL"
  exit 2
fi
echo "RHV3_FIDELITY_AUDIT=PASS"
