#!/usr/bin/env bash
# Statut de RHV6Fresh (auteur, 2026-10-09 : une seule chaîne Lean intégrée, une seule commande de build, ses erreurs réelles).
#   scripts/status.sh           relit la sortie du dernier `lake build RHV6Fresh`
#   scripts/status.sh --build   relance `lake build RHV6Fresh`, réécrit sa sortie, puis affiche
# Affiché : ÉTAT (experiments/audit_semantique/main_build_state.md : ce qui a été fait, réécrit à chaque livraison), HEAD, BUILD, SORRY/ADMIT, AXIOMS, puis pour chaque erreur du compilateur : fichier, ligne, nature, signature du
# théorème (lue dans la source), contexte complet et but restant, tels que Lean les écrit ; puis l'analyse
# (experiments/audit_semantique/main_build_error_analysis.md, première ligne `SIGNATURE=<sha>` = signature affichée, sinon
# PÉRIMÉE). Statut habituel rétabli (auteur, 2026-10-09 : « reprends le statut habituel ») : après les erreurs, SEMANTIC LOCK
# (experiments/audit_semantique/semantic_lock.md), puis l'analyse en sections : explication de chaque erreur, progrès vers la
# clôture (fait, certifié compilé), reste à faire, prémisses et suppositions, réfuté (maîtres et démarche, jamais le code).
set -u
cd "$(dirname "$0")/.."
OUT=experiments/audit_semantique/main_build_error_20261005.txt
ANA=experiments/audit_semantique/main_build_error_analysis.md
STATE=experiments/audit_semantique/main_build_state.md
LOCK=experiments/audit_semantique/semantic_lock.md
for a in "$@"; do
  case "$a" in
    --build) lake build RHV6Fresh > "$OUT" 2>&1; echo "EXIT=$?" >> "$OUT" ;;
  esac
done
echo "ÉTAT"
[ -f "$STATE" ] && sed 's/^/  /' "$STATE"
echo
echo "HEAD=$(git rev-parse --short HEAD)$( [ "$(git rev-parse HEAD)" = "$(git rev-parse origin/main 2>/dev/null)" ] && echo ' (= origin/main)')"
EXIT=$(grep -o '^EXIT=[0-9]*' "$OUT" | tail -1 | cut -d= -f2)
NERR=$(grep -c '^error: .*\.lean:' "$OUT")
echo "BUILD_DU=$(date -r "$OUT" '+%Y-%m-%d %H:%M')$( [ -n "$(git status --porcelain -- RHV6Fresh ../rhv3_lean 2>/dev/null)" ] && echo ' (sources Lean modifiées depuis : rebuild requis)')"
if [ "$EXIT" = 0 ]; then echo "BUILD=PASS (lake build RHV6Fresh, EXIT=0, 0 erreur)"; else echo "BUILD=FAIL (lake build RHV6Fresh, EXIT=$EXIT, $NERR erreur(s) : buts non fermés de la chaîne unique)"; fi
echo "SORRY=$(grep -c "declaration uses 'sorry'" "$OUT")  ADMIT=$(grep -rlw admit RHV6Fresh --include=*.lean | xargs -r grep -cwE '^\s*admit' | awk -F: '{s+=$2} END{print s+0}')"
AX=$(grep -o 'depends on axioms: \[[^]]*\]' "$OUT" | sed 's/.*\[//; s/\]//' | tr ',' '\n' | sed 's/^ *//' | sort -u | paste -sd, | sed 's/,/, /g')
echo "AXIOMS=${AX:-aucun relevé}"
# erreurs triées par fichier et ligne, chaque bloc = tout ce que Lean écrit jusqu'à l'erreur suivante
ERR=$(awk '/^error: .*\.lean:/{on=1; split($2,a,":"); key=sprintf("%s:%08d:%08d", a[1], a[2], a[3])} /^error: Lean exited/{on=0} /^warning:/{on=0} /^\[[0-9]+\/[0-9]+\]/{on=0} on{ printf "%s\t%08d\t%s\n", key, NR, $0 }' "$OUT" | LC_ALL=C sort -t "$(printf '\t')" -k1,1 -k2,2 | cut -f3-)
SIG=$(if [ "$EXIT" = 0 ]; then printf 'BUILD=PASS\n' | sha1sum | cut -c1-12; else printf '%s\n' "$ERR" | sha1sum | cut -c1-12; fi)
echo
echo "ERREURS DU COMPILATEUR (lake build RHV6Fresh)"
if [ -z "$ERR" ]; then echo "  aucune"; else
i=0
printf '%s\n' "$ERR" | grep -n '^error: .*\.lean:' | cut -d: -f1 | while read -r ln; do
  i=$((i+1))
  BLK=$(printf '%s\n' "$ERR" | awk -v s="$ln" 'NR>=s{ if (NR>s && /^error: .*\.lean:/) exit; print }')
  HDR=$(printf '%s\n' "$BLK" | head -1 | sed 's/^error: //')
  F=$(printf '%s' "$HDR" | cut -d: -f1); L=$(printf '%s' "$HDR" | cut -d: -f2)
  echo "  [$i] $HDR"
  echo "      signature du théorème :"
  awk -v L="$L" 'NR<=L && /^(theorem|lemma) /{start=NR} {lines[NR]=$0} END{ if(start){ for(k=start;k<=L;k++){ print "        " lines[k]; if (lines[k] ~ /:= *by *$|:= *$/) break } } }' "$F"
  echo "      contexte complet et but :"
  printf '%s\n' "$BLK" | tail -n +2 | sed 's/^/        /'
done
fi
echo "  signature : $SIG (empreinte du texte de l'erreur, contexte compris ; change à chaque fait ajouté : ce n'est PAS une mesure de progrès)"
echo
echo "BUT MINIMAL ET DÉPENDANCES (mesure de progrès : ce que consomme la ligne d'obligation)"
python3 scripts/goal_dependencies.py
echo
echo "SEMANTIC LOCK"
[ -f "$LOCK" ] && sed 's/^/  /' "$LOCK"
if [ "$EXIT" != 0 ]; then
  echo
  echo "ANALYSE"
  if [ ! -f "$ANA" ]; then echo "  ABSENTE ($ANA)"
  else
    [ "$(head -1 "$ANA")" = "SIGNATURE=$SIG" ] || echo "  PÉRIMÉE : écrite pour $(head -1 "$ANA"), l'état affiché a changé ; à réécrire."
    tail -n +2 "$ANA" | sed 's/^/  /'
  fi
fi
