# E467 (Ψ1) — résultats (2026-11-13) — verdict A (avec écart de règle consigné)

Compilation : tentative 1 (`attempts/build_attempt1.txt`) 5 erreurs de tactique (un `ring` de trop après `field_simp` ×3, un nom de lemme,
un sens de réécriture) ; tentative 2 : 1 erreur restante (sens d'une réécriture) ; tentative 3 : EXIT=0. Écart à la règle « deux
tentatives » consigné dans `attempts/NOTE_attempt3.md` (ordre de l'auteur du jour : enchaîner tout le plan). Neuf `#print axioms`, tous
`[propext, Classical.choice, Quot.sound]`. Build complet du paquet : « Build completed successfully (9064 jobs) ».
Jumeau (`twin_results.json`, section `psi1`, mpmath 40 chiffres) : part relative CONSTANTE sur 20 Tours réelles × 2 000 cellules (écart
max 4,5·10^-41) ; forme close du produit des facteurs (1,4·10^-36) ; paire témoin à la hauteur 1 419,42 : forme close vérifiée (9·10^-40) ;
après 2 000 cellules, part relative du membre bas multipliée par 0,41 / 0,64 / 0,80 et celle du miroir par 2,42 / 1,56 / 1,25 pour
β = 0,3 / 0,4 / 0,45.

## Constats
* Le facteur de cellule composé N fois donne la part exacte à la N-ième cellule (C1) ; rapportée à l'échelle de la ligne, la part est
  multipliée par `e^{π(β−1/2)/T}` par cellule (C2), soit `A^{β−1/2}` sur une plage de facteur A : la dérive est écrite en forme close.
* Constante d'une cellule à la suivante si et seulement si sur la ligne (C3). Le miroir d'une paire hors ligne dépasse toute borne
  (C4), le membre bas s'évanouit (C4), la paire est non bornée (C5).
* Par cellule, l'écart à la ligne est compris entre `e^{−π/(2T)}` et `e^{π/(2T)}` (C6) : pour la Tour 1 000 (hauteur 1 419), moins de
  0,12 % par cellule ; 2 000 cellules plus loin, un facteur 2,4 pour β = 0,3. « Fractionnel à chaque pas, explosif au cumul », compilé.
* Dans toute recomposition arithmétique des premiers, la part relative d'une porteuse est strictement positive sur chaque cellule (C7).
## Ce qui n'est pas établi
Que la dérive doive être payée par les autres hauteurs d'une façon impossible : c'est Ψ2–Ψ4. Rien n'exclut seul un zéro hors ligne.
