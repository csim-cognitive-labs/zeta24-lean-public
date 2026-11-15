# E472 — résultats (2026-11-13)

Pré-enregistrement : `README.md` (commit `766581a0`, avant toute compilation). Phase A = module isolé
`Terminal/ArithmeticBudgetSeparation.lean` ; phase B = `twin_e472.py` (premiers réels jusqu'à 3·10^7, 2 001 052 zéros).

## Phase A — compilation
* Tentative 1 (`attempts/build_attempt1.txt`) : UNE erreur, `towerNaturalSum_telescope` (un `simp` final sans effet après la
  réécriture du télescopage) ; les 17 autres énoncés vérifiés.
* Tentative 2 (`attempts/build_attempt2.txt`) : EXIT=0, `Build completed successfully (9106 jobs)` ; 18 `#print axioms`, tous
  `[propext, Classical.choice, Quot.sound]` ; aucun `sorry`. Build complet `lake build RHV6Fresh` : vert (`logs_lake_build_full.txt`).
* Après coup : une note de vocabulaire ajoutée à l'en-tête de `AlternatingCellSeries.lean` (commentaire seul, aucun code) ; rebuild du
  module E472 journalisé dans `attempts/build_after_header_note.txt`.

## Phase A — ce qui est compilé, réserve par réserve
* **P1 (fond dans le budget).** `alternatingCellTotal = arithmeticAlternatingBudget − backgroundAlternatingBudget`, le premier terme
  réel et écrit sur `demandArea` seul (premiers), le second sur `residualBackground` seul. Le budget alterné ne dépend d'AUCUNE
  recomposition (`alternatingCellTotal_independent`). Le fond est borné par `C(e^{π/T}+1)/(e^{π/T}−1)·x_N` (constante compilée
  `backgroundConstant`), donc rapporté à l'échelle de la ligne il est `≤ C'/x_N^{1/2}` : il s'efface (`background_relative_le`).
  Le budget NATUREL (sans signes) télescope : son fond se réduit aux deux bords (`naturalCellTotal_eq_telescope`).
* **P3 (signes rectifiés).** `‖towerAlternatingSum‖ = Σ‖parts‖` (`norm_towerAlternatingSum_eq_sum_norms`) : ce n'est pas une
  annulation. La somme naturelle `towerNaturalSum` télescope (`w·(K(x_N) − K(x_0))`), est une série géométrique de raison le facteur
  de cellule (négatif), et vérifie `(g−1)/(g+1)·‖rectifiée‖ ≤ ‖naturelle‖ ≤ ‖rectifiée‖`. Même classement : bornée sur la ligne
  (`relativeNatural_line_le`), divergente pour le miroir (`relativeNatural_unbounded_of_half_lt`).
* **P2 (somme de normes).** La contribution COMPLEXE de la paire, `‖S_β + S_{1−β}‖/x_N^{3/2}`, est non bornée pour `0 ≤ β < 1/2`,
  `w' ≠ 0` (`pairComplexRelative_unbounded_of_lt_half`), de même pour la forme naturelle (`pairNaturalRelative_unbounded_of_lt_half`) ;
  avec le coefficient IMPOSÉ par la recomposition dès que le miroir est porteur (`recomposition_mirror_pair_unbounded`). Le mécanisme :
  le membre bas est borné à l'échelle de la ligne pour tout `β ≤ 1/2` (`relativeAlternating_le_of_le_half`), le miroir diverge, la
  norme de la somme domine la différence des normes.
* **P4 (Ψ3 définitionnel).** `pairAsymmetryAt β p = log‖part'(p)‖ − log‖part(p)‖ − const` et la forme cumulée
  (`cumulativeAsymmetry_eq_sum_log_share_ratio`) : pont GÉOMÉTRIQUE exact aux termes de fibre de la paire aux abscisses premières.
  Consigné : aucun pont de l'asymétrie cumulée à un résidu de `fiberCellTotal` ni à une obligation arithmétique n'est compilé ; Ψ3
  reste une mesure géométrique, comme l'audit l'a dit.

## Phase B — mesures (`logs_twin_run.txt`, `twin_results.json`, 84,6 s)
Point 1 (définitions) : `demandArea` cumulée contre directe 5,7e-10 ; `demandArea_add` 1,1e-11 — conformes.
Point 2 (télescopage côté premiers) : conforme (≤ 3,3e-9) pour les Tours 1, 2, 3, 5, 10, 100 ; NON conforme pour les Tours 20
(3,3e-8) et 1000 (1,0e-7). Contrôle a posteriori (`check_telescope_fsum.py`, `logs_check_telescope_fsum.txt`) : la sommation exacte
(`math.fsum`) donne les MÊMES écarts (3,3e-8 ; 7,0e-8) : ce n'est pas l'accumulation de la somme, c'est l'annulation flottante
INTERNE à la formule cumulée de l'aire à `x ≈ 3·10^7` (termes `x·ψ(x) ≈ 10^15` pour un résultat `≈ 10^9`). Le seuil 1e-8 était
trop serré pour le double à cette plage ; l'identité compilée n'est pas en cause. Verdict B par la lettre du pré-enregistrement.
Point 6 : `‖naturelle‖/‖rectifiée‖` dans `[(g−1)/(g+1), 1]` pour toutes les Tours et tous les N (égal à la borne basse aux N pairs) ;
formes closes à 1e-13 — conforme.

Points 3–5 (mesures, aucune borne supposée) :
| Tour (zéro n°) | T | cellules | max |A_N|/x_N^{3/2} | max |Nat_N|/x_N^{3/2} | Σ|a_n|/x_N^{3/2} (fin) | résidu/x_N (fin) | borne fond/x_N | troncature 1M→2M (rel. ligne) | aires alternant de signe |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 14,13 | 45 | 0,075 | 0,031 | 0,049 | −0,203 | 49 | 3e-9 | 100 % |
| 2 | 21,02 | 67 | 0,063 | 0,032 | 0,053 | −0,137 | 73 | 8e-9 | 61 % |
| 3 | 25,01 | 81 | 0,066 | 0,035 | 0,051 | −0,115 | 87 | 6e-9 | 64 % |
| 5 | 32,94 | 107 | 0,041 | 0,031 | 0,061 | −0,088 | 115 | 2e-9 | 50 % |
| 10 | 49,77 | 162 | 0,032 | 0,037 | 0,062 | +0,058 | 173 | 2e-9 | 46 % |
| 20 | 77,15 | 252 | 0,030 | 0,037 | 0,071 | +0,037 | 269 | 9e-9 | 39 % |
| 100 | 236,5 | 775 | 0,012 | 0,037 | 0,085 | −0,012 | 823 | 4e-9 | 25 % |
| 1000 | 1419,4 | 4656 | 0,0026 | 0,037 | 0,094 | +0,002 | 4941 | 1e-7 | 11 % |

Constats de mesure.
* Le budget arithmétique alterné relatif `A_N/x_N^{3/2}`, lu sur les premiers seuls, reste au-dessous de 0,08 sur toutes les Tours
  et toute la plage `10^3 ≤ x_N ≤ 3·10^7` ; il décroît avec la hauteur de la Tour (0,075 → 0,0026). Ce n'est pas un théorème.
* Le côté des zéros (formes closes, 2M zéros) reproduit `A_N` à `10^{-3}` près (petit x) puis `10^{-7}` (grand x) à l'échelle de la
  ligne ; le résidu rapporté à `x_N` est borné (|·| ≤ 0,31) et TRÈS en dessous de la borne compilée du fond : le fond est bien à
  l'échelle `x_N`. La troncature à 2M zéros est de `10^{-9}`–`10^{-7}` à l'échelle de la ligne : négligeable (séparation demandée).
* Le résidu NATUREL rapporté à `x_N` tend vers −1,8378 = −log(2π) pour toutes les Tours : c'est exactement le terme de bord du fond
  (`−ζ'/ζ(0)`), confirmation numérique de `naturalCellTotal_eq_telescope`.
* Sur les cellules de la Tour n°1, 45 aires sur 45 alternent de signe ; la fraction décroît avec T (cellules de plus en plus fines).
* Paire artificielle à la hauteur de la Tour n°1000 (β = 0,3 / 0,4 / 0,45), fin de plage (`N = 4656`, `x_N ≈ 3·10^7`) : défaut
  relatif par rapport à la Tour de ligne 0,0158 / 0,0026 / 0,0010, contre un budget mesuré |A_N|/x_N^{3/2} ≤ 0,0026 sur cette Tour,
  un résidu de `4·10^{-7}` et une troncature de `10^{-7}`. Pour β = 0,3 le défaut dépasse le budget entier mesuré (facteur ≈ 6) et le
  résidu (facteur ≈ 4·10^4). Norme de la somme et somme des normes coïncident à 4 décimales sur ce témoin (phases alignées).
  Ceci DISTINGUE (sensibilité) et ne CONTREDIT pas (R-Φ octies) : une compensation par les autres hauteurs n'est pas exclue par une mesure.

## Verdict
B (point 2, deux Tours, cause flottante identifiée et consignée) ; phase A entièrement compilée ; toutes les mesures 3–5 rapportées.
Les quatre réserves de l'audit sont levées en Lean ; la cible unique de §19.101 se réécrit sans ambiguïté :
« `arithmeticAlternatingBudget T x N / x_N^{3/2}` (premiers seuls, aucune recomposition) reste borné » — le fond est déjà hors jeu
(théorème), la contribution complexe de la paire y est non bornée (théorème). Ce qui manque reste la borne depuis les premiers.
