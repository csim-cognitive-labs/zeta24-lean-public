#!/usr/bin/env bash
# RHV3Lean — gardes SPECIFICATION et STRENGTH.
#
# Deux défauts que ni le build, ni Comparator, ni l'audit de contrats ne
# peuvent voir, et qui ont tous deux déjà été commis dans ce projet :
#
#   SPECIFICATION : présenter un simple HABITANT d'un type comme réalisateur
#                   d'un objet dit CANONIQUE.  Un habitant prouve que le type
#                   n'est pas vide ; il ne fournit aucune règle de
#                   détermination, et c'est la règle qui est l'obligation.
#
#   STRENGTH      : faire certifier par Comparator un contrat dont la force est
#                   celle de la conclusion elle-même, sans l'avoir signalé.
#                   Comparator compare des énoncés ; il ne mesure pas leur
#                   force.  Le signalement doit donc précéder son exécution.
set -euo pipefail
cd "$(dirname "$0")"

MANIFEST_ARG="${1:-}"
fail=0

lean_code="$(
  find RHV3Lean -name '*.lean' -print0 2>/dev/null | xargs -0 -r cat |
    perl -0777 -pe 's{/-.*?-/}{}gs; s/--.*$//gm'
)"

controls="$(grep -vE '^[[:space:]]*(#|$)' audits/CONTROL_ONLY_INHABITANTS.txt || true)"
derived="$(grep -vE '^[[:space:]]*(#|$)' audits/DERIVED_CARRIER_MAPS.txt || true)"

# --- S1. tout habitant CLOS d'un type porteur est déclaré ------------------
carrier_types='TCanonicalTowerOperator|TTrueTowerCarrier'
undeclared=0
while IFS= read -r decl; do
  [[ -n "$decl" ]] || continue
  registered="$({ sed -n '/^| objet/,/^$/p' CONTRACTS.md | grep '^|' | grep -v '^|---' |
    awk -F'|' 'NF>2 {gsub(/ /,"",$(NF-1)); print $(NF-1)}' | grep -xcF "$decl"; } || true)"
  if ! grep -qxF "$decl" <<< "$controls" && ! grep -qxF "$decl" <<< "$derived" &&
      [[ "$registered" -eq 0 ]]; then
    echo "CARRIER_INHABITANT_NOT_DECLARED_AS_CONTROL=$decl"
    undeclared=$((undeclared + 1))
  fi
done < <(
  grep -oE "^(noncomputable[[:space:]]+)?def[[:space:]]+[A-Za-z_][A-Za-z_0-9]*[[:space:]]*:[[:space:]]*(${carrier_types})([[:space:]]|$)" <<< "$lean_code" |
    sed -E 's/^(noncomputable[[:space:]]+)?def[[:space:]]+([A-Za-z_][A-Za-z_0-9]*).*/\2/' | sort -u
)
echo "CARRIER_INHABITANTS_NOT_DECLARED=$undeclared"
[[ "$undeclared" -eq 0 ]] || fail=1

# --- S1bis. le réalisateur S4 actif est exclusivement contacts-only --------
# §T.8 interdit ces dépendances dans le producteur canonique. Les contrôles
# historiques peuvent encore les contenir hors de cette tranche active.
s4_active="$({
  sed -n '/structure TTrueHarmonicTowerState/,/end TTrueHarmonicTowerState/p' \
    RHV3Lean/Objects/TrueTowerState.lean
  sed -n '/structure TTrueTowerCarrier/,/namespace TTrueTowerCarrier/p' \
    RHV3Lean/Objects/TrueTowerCarrier.lean
} | perl -0777 -pe 's{/-.*?-/}{}gs; s/--.*$//gm')"
s4_forbidden='recoveredKappa|recoveredSpan|kEntryAddress|nSpan|tRecoveredWindow|tRatioFourOperator|canonicalWideOperator'
s4_bad="$(grep -oE "$s4_forbidden" <<< "$s4_active" | sort -u || true)"
if [[ -n "$s4_bad" ]]; then
  while IFS= read -r name; do
    echo "S4_ACTIVE_FORBIDDEN_DEPENDENCY=$name"
  done <<< "$s4_bad"
  fail=1
  echo "S4_CONTACTS_ONLY_SPECIFICATION=FAIL"
else
  echo "S4_CONTACTS_ONLY_SPECIFICATION=PASS"
fi

# R-PASS reçoit le passage source complet : son gap et sa nullité restent donc
# des projections disponibles et ne sont jamais perdus. Ils ne doivent pas
# être reposés comme champs de preuve indépendants dans le contrat. Surtout,
# aucune clause ne doit convertir cette nullité source en diagonalité de
# l'image première.
rpass_def="$(sed -n '/^def PIsMemberSensitivePassageTransport/,/^variable /p' \
  RHV3Lean/Objects/Passage.lean | perl -0777 -pe 's{/-.*?-/}{}gs; s/--.*$//gm')"
if grep -qE 'PZeroPassageRelationNull|PImageRelationNull|PNoNullZeroPassage' \
    <<< "$rpass_def"; then
  echo "R_PASS_CONTAINS_NULLITY=1"
  fail=1
else
  echo "R_PASS_SOURCE_NULLITY_DERIVED_NOT_REPOSED=PASS"
fi
if grep -qE '(^|[^A-Za-z_0-9])PNoNullZeroPassage([^A-Za-z_0-9]|$)' \
    <<< "$lean_code"; then
  echo "P_NO_NULL_ZERO_PASSAGE_IN_ACTIVE_CODE=1"
  fail=1
else
  echo "P_NO_NULL_ZERO_PASSAGE_IN_ACTIVE_CODE=0"
fi

# La branche principale a déjà causé une fausse fermeture de S4. Si elle est
# compilée, elle doit être explicitement classée comme contrôle et ne peut être
# enregistrée comme réalisateur.
if grep -qE '^noncomputable def tPrincipalBranchCarrier[[:space:]]*:' \
    RHV3Lean/Objects/TrueTowerCarrier.lean; then
  if ! grep -qxF tPrincipalBranchCarrier <<< "$controls"; then
    echo "PRINCIPAL_BRANCH_NOT_CONTROL_ONLY=1"
    fail=1
  else
    echo "PRINCIPAL_BRANCH_CONTROL_ONLY=PASS"
  fi
fi

# Contrôle numérique indépendant des quatre cellules historiques publiées.
if [[ ! -x contact_regression.sh ]]; then
  echo "CONTACT_REGRESSION_SCRIPT_NOT_EXECUTABLE=1"
  fail=1
elif ! ./contact_regression.sh; then
  fail=1
fi

# E60 est un contrôle de fidélité séparé et ne doit jamais devenir une
# prémisse Lean. Le script ne fait que vérifier le JSON de recherche publié.
if [[ ! -x e60_control.sh ]]; then
  echo "E60_CONTROL_SCRIPT_NOT_EXECUTABLE=1"
  fail=1
elif ! ./e60_control.sh; then
  fail=1
fi

# La route collision ne doit identifier ni contacts ni cellules et ne doit
# importer aucune prémisse expérimentale ou RH-équivalente globale.
collision_code="$(perl -0777 -pe 's{/-.*?-/}{}gs; s/--.*$//gm' \
  RHV3Lean/Objects/SamePrimeCollision.lean)"
if grep -qE 'PSameHeightSameCentralPrime|same_true_contacts|sameCell|same_cell|E60|PNoNullZeroPassage|nullityPreserved' \
    <<< "$collision_code"; then
  echo "SAME_PRIME_COLLISION_FORBIDDEN_DEPENDENCY=1"
  fail=1
else
  echo "DISTINCT_CONTACT_SYSTEMS_ALLOWED=PASS"
  echo "DISTINCT_CELLS_ALLOWED=PASS"
  echo "NO_EMPIRICAL_PREMISE=PASS"
fi

# --- S2. un habitant de contrôle ne réalise RIEN dans le registre ----------
control_realisers=0
while IFS= read -r name; do
  [[ -n "$name" ]] || continue
  if sed -n '/^| objet/,/^$/p' CONTRACTS.md | grep '^|' | grep -v '^|---' |
      awk -F'|' 'NF>2 {gsub(/ /,"",$(NF-1)); print $(NF-1)}' | grep -qxF "$name"; then
    echo "CONTROL_INHABITANT_USED_AS_REALISER=$name"
    control_realisers=$((control_realisers + 1))
  fi
done <<< "$(printf '%s\n%s\n' "$controls" "$derived")"
echo "CONTROL_INHABITANTS_USED_AS_REALISER=$control_realisers"
[[ "$control_realisers" -eq 0 ]] || fail=1

# --- T1. chaque contrat RH-équivalent porte ses deux preuves compilées -----
strength_bad=0
declared_contracts=()
while read -r contract forward backward; do
  [[ -n "${contract:-}" ]] || continue
  [[ "${contract:0:1}" != "#" ]] || continue
  declared_contracts+=("$contract")
  for name in "$contract" "$forward" "$backward"; do
    if ! grep -qE "(^|[^A-Za-z_0-9])${name}([^A-Za-z_0-9]|$)" <<< "$lean_code"; then
      echo "RH_EQUIVALENT_EVIDENCE_MISSING=$name"
      strength_bad=$((strength_bad + 1))
    fi
  done
done < <(grep -vE '^[[:space:]]*(#|$)' audits/RH_EQUIVALENT_CONTRACTS.txt || true)
echo "RH_EQUIVALENT_CONTRACTS_DECLARED=${#declared_contracts[@]}"
echo "RH_EQUIVALENT_EVIDENCE_MISSING_COUNT=$strength_bad"
[[ "$strength_bad" -eq 0 ]] || fail=1

# --- T2. le manifeste du tour les signale, AVANT Comparator ----------------
if [[ -n "$MANIFEST_ARG" ]]; then
  M="audits/tours/${MANIFEST_ARG}.md"
  if [[ ! -f "$M" ]]; then
    echo "STRENGTH_MANIFEST_MISSING=$M"
    fail=1
  else
    announced="$(sed -n 's/^[[:space:]]*RH_EQUIVALENT_CONTRACTS[[:space:]]*=[[:space:]]*//p' "$M" |
      tr ',' '\n' | tr -d ' ' | sed '/^$/d' | sort -u)"
    expected="$(printf '%s\n' "${declared_contracts[@]}" | sort -u)"
    if [[ "$announced" != "$expected" ]]; then
      echo "RH_EQUIVALENT_CONTRACTS_NOT_ANNOUNCED_IN_MANIFEST=1"
      echo "  manifeste : $(tr '\n' ' ' <<< "$announced")"
      echo "  attendu   : $(tr '\n' ' ' <<< "$expected")"
      fail=1
    else
      echo "RH_EQUIVALENT_CONTRACTS_ANNOUNCED=PASS"
    fi
  fi
fi

if [[ "$fail" -ne 0 ]]; then
  echo "RHV3_SPECIFICATION_STRENGTH_AUDIT=FAIL"
  exit 2
fi
echo "RHV3_SPECIFICATION_STRENGTH_AUDIT=PASS"
