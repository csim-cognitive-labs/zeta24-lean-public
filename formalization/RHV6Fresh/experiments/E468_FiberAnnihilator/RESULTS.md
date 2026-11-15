# E468 (Ψ2 = Φ9) — résultats (2026-11-13) — verdict A

Compilation : les journaux `build_attempt1/2` échouent par l'import de Ψ1 (module non vérifié) ; première vérification propre
`build_attempt3.txt` : 1 erreur (un terme de preuve mal formé pour « a ≤ a·e^{π/T} ») ; `build_attempt4.txt` : EXIT=0. Huit `#print axioms`
propres, tous standard. Jumeau (section `psi2`, 2 000 zéros, 40 chiffres) : identité d'annulation d'une Tour exacte à 9·10^-40 sur
5 Tours × 8 cellules ; résidu de l'annulateur de la ligne nul (3·10^-41) sur une Tour de ligne, égal à la forme close pour la paire témoin.

## Constats
* Le total d'une cellule de pas T est l'aire de la demande (E465) moins la variation du fond (F1).
* Deux totaux consécutifs combinés avec le facteur de la Tour ne contiennent plus la Tour : ce qui reste est la somme des AUTRES
  membres (F2, `annihilate_one_tower`). Trois totaux consécutifs avec les deux facteurs éliminent la paire Tour + miroir (F3) ; les
  termes de la Tour et du miroir y sont nuls (F3). Les N identités consécutives se somment (F4).
* Annulée avec le coefficient de la LIGNE, une Tour laisse le résidu `(f_β − f_{1/2})·part`, nul si et seulement si la Tour est sur
  la ligne (F5), et ce résidu à la N-ième cellule est `(f_β − f_{1/2}) f_β^N · part` : il croît comme la dérive de Ψ1.
## Lecture
M2 du point d'étape est levée : une Tour (ou une paire) est RETIRÉE du total sur ses propres cellules, par une combinaison d'aires
de demande lues sur les premiers seuls. Le reste est « ce que les autres hauteurs déposent », écrit. Non établi : une borne sur ce reste.
