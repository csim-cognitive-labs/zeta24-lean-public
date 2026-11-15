# E473 — résultats (2026-11-13)

Pré-enregistrement : `README.md` (commit `7a1ce3cc`, avant toute compilation). Phase A = module isolé `Terminal/CellAreaGrammar.lean` ;
phase B = `twin_e473.py` (premiers réels jusqu'à 3·10^7, Tours = zéros n° 1, 2, 3, 5, 10, 20, 100, 1000, cellules = contacts réels de
chaque Tour, β = 1/2).

## Phase A — compilation
* Tentative 1 (`attempts/build_attempt1.txt`) : erreurs de surface seulement (arguments implicites `β` non inférables dans des `have`,
  un nom déjà déclaré `cellLength_add_nat` — réutilisé d'E441 —, `abs_add` renommé `abs_add_le`, une réassociation manquante) et UNE
  erreur de fond : dans `budget_recurrence`, les deux `Finset.sum_range_succ` réécrivaient le même membre ; corrigé en nommant les
  bornes (`_ N`, `_ (N + 1)`) et en concluant par `linear_combination ih + (−(−1)^N)·hloc`.
* Tentative 2 (`attempts/build_attempt2.txt`) : EXIT=0, `Build completed successfully (9107 jobs)` ; 18 `#print axioms`, tous
  `[propext, Classical.choice, Quot.sound]` ; aucun `sorry`. Build complet `lake build RHV6Fresh` : vert (`logs_lake_build_full.txt`).

## Phase A — ce qui est compilé
* **G1, identité exacte des contributions premières.** `cellArea = cellDescentArea + cellExitWeight` : l'aire d'une cellule est
  (demande au contact d'entrée × longueur) − (demi-carré de la longueur) + (poids des entiers franchis, pesés par leur distance au
  contact de sortie). `cellExitWeight + cellEntryWeight = cellWeight × cellLength` ; les deux poids pesés sont ≥ 0 et ≤ poids × longueur.
  Les déviations `exitDeviation = aire − demande d'entrée × longueur`, `entryDeviation = demande de sortie × longueur − aire` sont les
  poids pesés moins leur part de Lebesgue : elles ne dépendent que des premiers DANS la cellule.
* **G2, grammaire locale.** `cellArea (k+1) − e^{π/T}·cellArea k = localGrammarTerm k = exitDeviation (k+1) + e^{π/T}·entryDeviation k`.
  La demande au contact (seule mémoire de tous les premiers antérieurs) est ÉLIMINÉE : la différence géométrique de deux aires
  consécutives ne dépend que des premiers des deux cellules et de leurs longueurs. Bornes de signe : le terme local est minoré par
  −e^{π/T}(1+e^{π/T})ℓ²/2 (part de Lebesgue) et majoré par les poids des deux cellules fois leurs longueurs moins cette part ;
  sans aucun poids dans les deux cellules il vaut exactement la part de Lebesgue négative.
* **G3, récurrence du budget.** `(1 + e^{π/T}) A_{N+1} = a_{k₀} + (−1)^N e^{π/T} a_{k₀+N} − Σ_{n<N} (−1)^n L_{k₀+n}` ; pont compilé
  avec E472 : `arithmeticAlternatingBudget T C_{k₀} N = Σ (−1)^n cellArea (k₀+n)`. Le budget est donc, au facteur `1 + e^{π/T}`,
  la première aire, la dernière aire et la somme alternée des termes LOCAUX.
* **G4, contrôle des signes.** Si deux aires consécutives sont de signes opposés, `|a_{k+1}| + e^{π/T}|a_k| ≤ |L_k|` : chaque aire est
  bornée par le terme local ; sous alternance sur une fenêtre, `|A_{N+1}| ≤ |a_{k₀}| + Σ|L_n|`.
* **G5, échelle inconditionnelle (PNT porté).** `|cellArea| ≤ (1/2 + ε)·cellLength²` à partir d'un rang, et pour toute fenêtre
  `|A| ≤ (1/2+ε)·e^{2π/T}/(e^{2π/T}−1)·(dernière longueur)²` : la vérité compilée depuis les premiers seuls est à l'échelle `x_N^2`.
* **G6, clôtures conditionnelles.** `(1+e^{π/T})|A_{N+1}| ≤ |a_{k₀}| + e^{π/T}|a_{k₀+N}| + Σ b_n` dès que `|L_n| ≤ b_n` ; à
  l'échelle de la ligne : si `|L_n| ≤ C·C_n^{3/2}` et si la première et la dernière aire sont `≤ C·C^{3/2}`, alors
  `(1+e^{π/T})|A_{N+1}| ≤ C(1 + e^{π/T} + 1/(e^{3π/(2T)}−1))·C_{k₀+N}^{3/2}`. Les antécédents sont des hypothèses du théorème ;
  rien n'est admis ailleurs. Celui sur la dernière aire est la cible elle-même à une cellule ; celui sur `L_n` est la cible locale.

## Phase B — mesures (`logs_twin_run.txt`, `twin_results.json`, 45,7 s)
Points 1–3 (jumeaux de G1, G2, G3) : conformes sur toutes les cellules de toutes les Tours (G1 ≤ 2,3e-16 ; G2 ≤ 7,4e-12 ; G3 ≤ 3,6e-11,
rapportés à `ℓ²`). Verdict A.
Point 4 (stabilité) : la formule CUMULÉE d'E472 (`b·Σ Λ − Σ nΛ`) s'écarte de la formule de cellule (G1, sommes directes sur les entiers
de la cellule, `math.fsum`) de 1e-10 en médiane mais jusqu'à 5e-7 (Tours 1–20), 1,6e-5 (Tour 100) et 3,6e-4 (Tour 1000) sur une
cellule : c'est l'annulation flottante déjà identifiée dans E472 (termes `x·ψ ≈ 10^15`), aggravée pour les cellules fines. La formule
de cellule est la forme stable ; elle est désormais la forme compilée G1.

| Tour | T | cellules | x début → fin | max |L_k|/C_k^{3/2} | max |a_k|/C_k^{3/2} | |a_k|/ℓ_k² (fin) | changements de signe | max |A_N|/C_N^{3/2} | C mesurée (G6) | borne G6 |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 14,13 | 45 | 1095 → 2,4e7 | 0,0285 | 0,0217 | 2,2e-5 | 50 % | 0,0175 | 0,0285 | 0,061 |
| 2 | 21,02 | 68 | 1041 → 2,7e7 | 0,0580 | 0,0307 | 1,1e-4 | 67 % | 0,0295 | 0,0580 | 0,165 |
| 3 | 25,01 | 81 | 1065 → 2,8e7 | 0,0663 | 0,0314 | 1,3e-4 | 56 % | 0,0370 | 0,0663 | 0,216 |
| 5 | 32,94 | 107 | 1007 → 2,7e7 | 0,0454 | 0,0328 | 2,2e-4 | 50 % | 0,0402 | 0,0454 | 0,186 |
| 10 | 49,77 | 163 | 1003 → 2,9e7 | 0,0363 | 0,0266 | 1,5e-5 | 43 % | 0,0305 | 0,0363 | 0,213 |
| 20 | 77,15 | 252 | 1036 → 3,0e7 | 0,0225 | 0,0193 | 2,8e-4 | 36 % | 0,0243 | 0,0225 | 0,197 |
| 100 | 236,5 | 775 | 1006 → 3,0e7 | 0,0061 | 0,0076 | 2,1e-3 | 24 % | 0,0108 | 0,0076 | 0,195 |
| 1000 | 1419,4 | 4657 | 1001 → 3,0e7 | 0,0007 | 0,0017 | 1,9e-3 | 12 % | 0,0026 | 0,0017 | 0,253 |

Constats de mesure.
* Les termes locaux rapportés à l'échelle de la ligne restent au-dessous de 0,07 sur toutes les Tours et décroissent avec T ; les
  aires et le budget aussi. Ce ne sont pas des théorèmes.
* `|a_k|/ℓ_k²` vaut 1e-5 à 2e-3 en fin de plage : l'échelle inconditionnelle G5 (`x_N^2`) est très au-dessus de ce qui est observé ;
  l'écart d'exposant (1/2) est exactement ce que les premiers doivent donner et que G5 ne donne pas. Aux petites abscisses des Tours
  fines, `|a_k|/ℓ_k²` dépasse 1 (jusqu'à 9 pour la Tour 1000 : une cellule de longueur ≈ 2 contenant un premier) : G5 est asymptotique.
* Signes : avec les cellules alignées sur les CONTACTS RÉELS de la Tour, la fraction de paires consécutives de signes opposés est
  50 % pour la Tour 1 (contre 100 % dans E472, dont les cellules partaient de `x₀ = 1000` sans rapport avec la phase de la Tour) et
  décroît avec T jusqu'à 12 %. Lecture (non compilée) : les contacts sont les extrema de la valeur réelle de la Tour, la part de la Tour
  elle-même sur ses propres cellules est alors réduite du facteur `(1+β)/‖ρ+1‖`, et les autres hauteurs décident du signe. La règle
  « les aires alternent » dépend du découpage et ne doit plus être énoncée sans le préciser.
* Transmission G4 : les fenêtres initiales d'alternance n'ont que 1 à 2 cellules ; sur les deux fenêtres à 2 cellules (Tours 2, 3), le
  budget vaut 0,69 et 0,62 de la borne `|a_0| + Σ|L|`, conforme.
* Clôture conditionnelle G6 : avec la constante MESURÉE `C = max(|L_n|/C_n^{3/2}, |a|/C^{3/2})`, la borne compilée du budget à l'échelle
  de la ligne vaut 0,06 à 0,25 selon la Tour, contre un budget mesuré ≤ 0,04 : la borne est lâche d'un facteur 3 à 100 mais du bon
  ordre ; elle n'est un théorème que sous ses antécédents.
* Le terme local est négatif sur 47 % à 52 % des cellules : la part de Lebesgue et la part des premiers sont du même ordre et se
  compensent cellule par cellule, aucune direction privilégiée.

## Verdict
A (points 1–3 conformes, toutes les valeurs 4–5 rapportées) ; phase A entièrement compilée.
Ce qui est nouveau et compilé : l'ÉLIMINATION de la demande au contact dans la relation entre deux aires consécutives (G2), la
réécriture exacte du budget en première aire + dernière aire + somme alternée de termes locaux (G3), la transmission sous changement
de signe (G4), l'échelle inconditionnelle `x_N^2` depuis les premiers (G5). Ce qui n'est pas obtenu : une borne du terme local ou de la
dernière aire à l'échelle `x^{3/2}` depuis les premiers seuls ; G6 réduit la cible unique à ces deux antécédents locaux, ce qui est une
réduction exacte, non une obligation nouvelle qui la ferme. Honnêtement : aucune obligation arithmétique nouvelle qui borne n'a été
trouvée ; ce qui a été trouvé est la forme locale exacte de ce qu'il faudrait borner.

## Classement (ordre de l'auteur, 2026-11-14, §19.108)
Résultat AUXILIAIRE : théorèmes acquis (axiomes standard, build vert), aucune portée démonstrative vers RH. Les cellules entre contacts
sont des restes partiels d'écart (§19.51) ; la grammaire des aires est une construction sans obligation arithmétique. Voir
`experiments/E475_SharedPrimeObligation/AUDIT_20261114.md`.
