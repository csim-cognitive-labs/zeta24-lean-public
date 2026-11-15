#!/usr/bin/env bash
# RHV3Lean — audit mécanique du registre de production.
#
# Il existe parce qu'un rapport de fidélité écrit à la main a déjà été FAUX :
# le contrat de la Tour listait l'adresse d'entrée et le nombre d'étages parmi
# les attributs, et le rapport a déclaré « 7/7 attributs prouvés » alors
# qu'aucune déclaration Lean ne les portait.  Aucun pourcentage de fidélité ne
# doit plus être écrit sans que ce script l'ait vérifié.
#
# Trois contrôles :
#   1. toute déclaration nommée dans une fiche de traçabilité existe vraiment ;
#   2. tout module sous Objects/ est importé par la racine ;
#   3. tout réalisateur nommé dans la table de CONTRACTS.md existe vraiment,
#      et les attributs sans réalisateur sont comptés et affichés.
set -euo pipefail
cd "$(dirname "$0")"

fail=0

decls="$(
  find RHV3Lean -name '*.lean' -print0 | xargs -0 -r cat |
    grep -oE '^(noncomputable[[:space:]]+)?(protected[[:space:]]+)?(def|theorem|abbrev|structure|inductive)[[:space:]]+[A-Za-z_][A-Za-z_0-9.]*' |
    sed -E 's/.*[[:space:]]([A-Za-z_][A-Za-z_0-9.]*)$/\1/' | sort -u
)"
# les projections de structure et les champs comptent comme déclarations
fields="$(
  find RHV3Lean -name '*.lean' -print0 | xargs -0 -r cat |
    grep -oE '^  [a-z][A-Za-z_0-9]*[[:space:]]*:' | sed -E 's/^  ([A-Za-z_0-9]*).*/\1/' | sort -u
)"
known="$(printf '%s\n%s\n' "$decls" "$fields" | sort -u)"

echo "RHV3_DECLARATIONS=$(printf '%s\n' "$decls" | grep -c . || true)"

# --- 1. les noms cités dans les fiches de traçabilité existent -------------
missing_card=0
while IFS= read -r name; do
  [[ -n "$name" ]] || continue
  if ! grep -qxF "$name" <<< "$known"; then
    echo "CARD_NAME_NOT_FOUND=$name"
    missing_card=$((missing_card + 1))
  fi
done < <(
  find RHV3Lean -name '*.lean' -print0 | xargs -0 -r cat |
    sed -n '/LEAN_DEFINITION/,/SAME_MEMBER_CHECK/p' |
    grep -oE '[A-Za-z_][A-Za-z_0-9]{3,}' |
    grep -E '^(thm_[A-Za-z_0-9]+|[a-zA-Z][A-Za-z0-9]*[A-Z][A-Za-z0-9]*)$' |
    grep -vE '^[A-Z_]+$' |
    grep -vE '^(LEAN_DEFINITION|LEAN_THEOREM|SAME_MEMBER_CHECK)$' | sort -u
)
echo "CARD_NAMES_MISSING=$missing_card"
[[ "$missing_card" -eq 0 ]] || fail=1

# --- 1bis. les 18 champs sont présents dans CHAQUE module public ----------
# Un module d'Objects est public exactement lorsqu'il est importé par la
# racine RHV3Lean.lean. La présence est contrôlée module par module : une fiche
# complète ailleurs ne peut pas masquer un champ absent ici.
required_trace_fields=(
  TRACE_ID SEMANTIC_OBJECT SEMANTIC_STATEMENT MATHEMATICAL_STATEMENT
  MATHEMATICAL_PARENT PROOF_STRATEGY REQUIRED_LEMMAS WHY_EACH_LEMMA_EXISTS
  LEAN_DEFINITION LEAN_THEOREM SAME_MEMBER_CHECK SAME_PASSAGE_CHECK
  SAME_MIDDLE_CHECK SAME_HISTORY_CHECK FORBIDDEN_PREMISES NEXT_CONSUMER
  AXIOMS LEAN_STATUS
)
trace_fields_missing=0
for f in RHV3Lean/Objects/*.lean; do
  m="RHV3Lean.Objects.$(basename "$f" .lean)"
  grep -qF "import $m" RHV3Lean.lean || continue
  for field in "${required_trace_fields[@]}"; do
    if ! grep -qE "^[[:space:]]*${field}[[:space:]]*:" "$f"; then
      echo "PUBLIC_MODULE_TRACE_FIELD_MISSING=$m:$field"
      trace_fields_missing=$((trace_fields_missing + 1))
    fi
  done
done
echo "PUBLIC_MODULE_TRACE_FIELDS_MISSING=$trace_fields_missing"
[[ "$trace_fields_missing" -eq 0 ]] || fail=1

# --- 2. tout module d'objet est dans la racine -----------------------------
orphans=0
for f in RHV3Lean/Objects/*.lean; do
  m="RHV3Lean.Objects.$(basename "$f" .lean)"
  if ! grep -qF "import $m" RHV3Lean.lean; then
    echo "MODULE_NOT_IN_ROOT=$m"
    orphans=$((orphans + 1))
  fi
done
echo "MODULES_NOT_IN_ROOT=$orphans"
[[ "$orphans" -eq 0 ]] || fail=1

# --- 3. la table des réalisateurs de CONTRACTS.md --------------------------
produced=0
absent=0
bad=0
while IFS='|' read -r _ _obj _attr real _; do
  real="$(tr -d ' ' <<< "${real:-}")"
  [[ -n "$real" ]] || continue
  [[ "$real" != "réalisateur" ]] || continue
  if [[ "$real" == "—" ]]; then
    absent=$((absent + 1))
    continue
  fi
  produced=$((produced + 1))
  if ! grep -qxF "$real" <<< "$known"; then
    echo "REALISER_NOT_FOUND=$real"
    bad=$((bad + 1))
  fi
done < <(sed -n '/^| objet/,/^$/p' CONTRACTS.md | grep '^|' | grep -v '^|---')
echo "ATTRIBUTES_WITH_REALISER=$produced"
echo "ATTRIBUTES_WITHOUT_REALISER=$absent"
echo "REALISERS_NOT_FOUND=$bad"
[[ "$bad" -eq 0 ]] || fail=1
if [[ "$absent" -eq 0 ]]; then
  echo "RHV3_ROUTE_REALISERS_COMPLETE=YES"
else
  echo "RHV3_ROUTE_REALISERS_COMPLETE=NO"
fi

# --- 4. trous statiques ----------------------------------------------------
holes="$(
  find RHV3Lean -name '*.lean' -print0 | xargs -0 -r cat |
    perl -0777 -pe 's{/-.*?-/}{}gs; s/--.*$//gm' |
    grep -cE '\b(sorry|admit)\b|^[[:space:]]*(axiom|constant)[[:space:]]' || true
)"
echo "STATIC_HOLES_OR_AXIOMS=$holes"
[[ "$holes" -eq 0 ]] || fail=1

# --- 5. infrastructure de validation obligatoire (maître M/N/O/P) ----------
# Un audit de registre ne doit plus pouvoir afficher PASS si la boucle
# Comparator/fidélité imposée par le maître n'est même pas installée.
validation_missing=0
required_validation_files=(
  "Certification/Challenge.lean"
  "Certification/Solution.lean"
  "Certification/comparator.json"
  "Certification/CHALLENGE_FROZEN_GIT_BLOB"
  "Certification/run_comparator.sh"
  "Certification/PrintAxioms.lean"
  "audit_fidelity.sh"
  "audit_strength.sh"
  "validate_cycle.sh"
  "audits/CONTROL_ONLY_INHABITANTS.txt"
  "audits/DERIVED_CARRIER_MAPS.txt"
  "audits/RH_EQUIVALENT_CONTRACTS.txt"
)
for f in "${required_validation_files[@]}"; do
  if [[ ! -f "$f" ]]; then
    echo "VALIDATION_INFRA_MISSING=$f"
    validation_missing=$((validation_missing + 1))
  fi
done
echo "VALIDATION_INFRA_MISSING_COUNT=$validation_missing"
if [[ "$validation_missing" -eq 0 ]]; then
  echo "RHV3_VALIDATION_INFRA=PASS"
else
  echo "RHV3_VALIDATION_INFRA=FAIL"
  fail=1
fi

# --- 6bis. couverture Comparator (maître M.10) -----------------------------
# Le script de contrats n'exécute PAS Comparator : il vérifie que la
# configuration existe, que chaque cible listée est réellement déclarée des
# deux côtés, et que le nombre d'obligations sans réalisateur du registre est
# exactement le nombre d'obligations enregistrées NOT_REALISED dans le
# manifeste.  Une obligation manquante ne peut donc plus disparaitre d'un des
# deux comptages sans faire échouer l'audit.
cmp_missing=0
while IFS= read -r fq; do
  name="${fq##*.}"
  grep -qE "^theorem[[:space:]]+${name}([[:space:]]|$)" Certification/Challenge.lean ||
    { echo "COMPARATOR_TARGET_NOT_IN_CHALLENGE=$fq"; cmp_missing=$((cmp_missing + 1)); }
  grep -qE "^theorem[[:space:]]+${name}([[:space:]]|$)" Certification/Solution.lean ||
    { echo "COMPARATOR_TARGET_NOT_IN_SOLUTION=$fq"; cmp_missing=$((cmp_missing + 1)); }
done < <(python3 -c '
import json
print("\n".join(json.load(open("Certification/comparator.json"))["theorem_names"]))')
echo "COMPARATOR_TARGETS_MISSING=$cmp_missing"
[[ "$cmp_missing" -eq 0 ]] || fail=1

not_realised="$(python3 -c '
import json
m = json.load(open("Certification/comparator_manifest.json"))
print(sum(1 for t in m["not_realised_targets"] if t["status"] == "NOT_REALISED"))')"
echo "MANIFEST_NOT_REALISED=$not_realised"
if [[ "$not_realised" -ne "$absent" ]]; then
  echo "REGISTRY_MANIFEST_MISMATCH=registry:$absent manifest:$not_realised"
  fail=1
fi

# --- 6. le maître consolidé doit rester présent ----------------------------
master="../../docs/RH_STRATEGIE_LEAN.md"
master_missing=0
for marker in   "RH — MAÎTRE LEAN ACTIF DE TRAÇABILITÉ SÉMANTIQUE, MATHÉMATIQUE ET FORMELLE"   "2. Graphe global de la démonstration à transcrire"   "6. T2 — producteur canonique du transport"   "7. R-PASS complet"   "11. Matrice L01–L30"   "13. Classification des modules RHV3"; do
  if [[ ! -f "$master" ]] || ! grep -qF "$marker" "$master"; then
    echo "MASTER_GOVERNANCE_MARKER_MISSING=$marker"
    master_missing=$((master_missing + 1))
  fi
done
echo "MASTER_GOVERNANCE_MARKERS_MISSING=$master_missing"
[[ "$master_missing" -eq 0 ]] || fail=1

if [[ "$fail" -ne 0 ]]; then
  echo "RHV3_CONTRACT_AUDIT=FAIL"
  exit 2
fi
echo "RHV3_CONTRACT_AUDIT=PASS"
