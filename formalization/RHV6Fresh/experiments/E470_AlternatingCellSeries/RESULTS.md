# E470 (Ψ4 + Ψ6) — résultats (2026-11-13) — verdict A

Compilation : première vérification propre `build_attempt4.txt` : 3 erreurs (deux `ring` de trop après `field_simp`, un `dsimp` sans effet) ;
`build_attempt5.txt` : EXIT=0. Huit `#print axioms` propres, tous standard. Build complet : vert (`logs_lake_build_full.txt`, 9 064 jobs).
Jumeau (section `psi4`) : forme close de la somme alternée vérifiée à 6,9·10^-39 (5 Tours réelles × 500 cellules) ; sur la ligne, le
rapport de la somme alternée relative à sa borne atteint exactement 1,0 et jamais plus ; paire témoin (hauteur 1 419,42) : somme alternée
relative du miroir 3,9·10^-6 → 2,5·10^-3 de 1 à 2 000 cellules (β = 0,3), celle du membre bas plafonne.

## Constats
* La somme alternée des parts d'une Tour sur N cellules est une série géométrique de raison `e^{π(1+β)/T}` (G1) ; rapportée à l'échelle
  de la ligne elle a une forme close (G2).
* Sur la ligne elle est BORNÉE par une constante explicite, part initiale divisée par (raison − 1) et par x^{3/2} (G3) : l'alternance
  annule la croissance. C'est la « stabilité de la grammaire » écrite comme mécanisme.
* Pour le miroir d'une paire hors ligne elle dépasse toute borne (G4) ; la paire est non bornée (G6, Ψ6).
* Côté premiers : la somme alternée des totaux de cellules ne contient que des aires de demande et le fond (G5), et elle égale la somme,
  sur tous les membres, de leurs sommes alternées (G5, `alternatingCellTotal_eq_tsum`, `tower_term_alternating`).
## La cible unique, écrite en série
Budget alterné des premiers B_N (G5) = Σ_membres sommes alternées. La paire y est non bornée relativement (G6). Donc : « B_N reste à
l'échelle de la ligne » force les autres hauteurs à compenser exactement une divergence, et « B_N reste à l'échelle de la ligne » est
un énoncé sur les premiers seuls. C'est la cible qui reste, et une seule. Elle est de la force de RH (R-RH : attendu, pas une objection).
Ce que le corpus n'a pas : une annulation entre cellules des aires de demande, lue sur les premiers, meilleure que l'exposant 1.
