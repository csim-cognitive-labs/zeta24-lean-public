# E469 (Ψ3) — résultats (2026-11-13) — verdict A

Compilation : `attempts/build_attempt1.txt`, EXIT=0 à la PREMIÈRE tentative ; six `#print axioms`, tous `[propext, Classical.choice,
Quot.sound]`. Jumeau : `../E467_MemberConstancySeries/twin_results.json` section `psi3`, identité cumul = (1 − 2β)·θ(N) vérifiée
à 1,9·10^-14 sur les 78 498 premiers ≤ 10^6, nulle à β = 1/2.

## Constats, un à un
* Par premier, l'asymétrie des deux termes de la paire vaut exactement `(1 − 2β) log p` : une fraction fixe du poids du premier,
  au plus le poids entier (A1, `abs_pairAsymmetryAt_le`). C'est le « fractionnel » de l'auteur, compilé.
* Cumulée sur les premiers jusqu'à N, elle vaut `(1 − 2β)` fois la fonction de Tchebychev (A2). Nulle si et seulement si la
  Tour est sur la ligne, dès N ≥ 2 (A3).
* La fonction de Tchebychev n'est pas bornée (A4, par l'infinité des premiers, `Nat.tendsto_primeCounting'`, aucune borne analytique
  nécessaire) ; donc l'asymétrie cumulée d'une paire hors ligne n'est pas bornée : vers le haut pour le membre bas (A5), vers le bas
  pour le miroir.

| N | premiers | θ(N) | asymétrie cumulée β = 0,3 | β = 0,4 | β = 0,45 |
|---|---|---|---|---|---|
| 10^3 | 168 | 956 | 382 | 191 | 96 |
| 10^4 | 1 229 | 9 896 | 3 958 | 1 979 | 990 |
| 10^5 | 9 592 | 99 685 | 39 874 | 19 937 | 9 969 |
| 10^6 | 78 498 | 998 484 | 399 394 | 199 697 | 99 848 |

## Lecture par rapport à la stratégie
Le décalage « progressif mais monstrueux » de l'auteur a maintenant une forme exacte : linéaire en θ(N), donc en N par le théorème des
nombres premiers, invisible en un premier (fraction ≤ 1 d'un seul poids), non borné au cumul. Ce qui n'est PAS établi : que les autres
hauteurs ne peuvent pas payer cette asymétrie sur tous les premiers (côté premiers : Ψ2/Ψ4). Rien n'exclut seul un zéro hors ligne.
