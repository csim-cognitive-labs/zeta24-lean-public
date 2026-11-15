# E474 — résultats (2026-11-13)

Pré-enregistrement : `README.md` (commit `3a1943de`, avant toute compilation ; les quatre hypothèses et leurs seuils y sont écrits).
Démarche TDD : le jumeau a été lancé AVANT la compilation (test d'abord), puis les deux modules ont été compilés.

## Phase A — compilation (deux modules isolés, jamais ajoutés à `RHV6Fresh.lean`)
* `Terminal/CellAreaTent.lean` (10 énoncés). Tentative 1 (`attempts/tent_build_attempt1.txt`, EXIT=1) : trois erreurs — `ring`
  superflu après `rw` dans `contactAt_succ` (« No goals »), `β` implicite non inférable dans deux `have` (`contactAt_succ`,
  `rawDemand_next_contact` : même cause qu'E473, corrigée par `(β := β)`). Tentative 2 (`attempts/tent_build_attempt2.txt`) : EXIT=0,
  `Build completed successfully (9108 jobs)`, 10 `#print axioms` tous `[propext, Classical.choice, Quot.sound]`, aucun `sorry`.
* `Terminal/CellAreaIntegral.lean` (14 énoncés). Tentative 1 (`attempts/integral_build_attempt1.txt`, EXIT=1) : UNE erreur, nom
  `integral_const_mul` ambigu (intervalle / Bochner) → `MeasureTheory.integral_const_mul`. Tentative 2
  (`attempts/integral_build_attempt2.txt`) : EXIT=0, `Build completed successfully (9108 jobs)`, 14 `#print axioms` tous standard.
* Build complet `lake build RHV6Fresh` : voir `logs_lake_build_full.txt`.

## Phase A — ce qui est compilé, hypothèse par hypothèse
* **H1 (tente), théorème.** `localGrammarTerm_eq_tent_sum` : `L_k = Σ_{n∈(C_k,C_{k+2}]} Λ(n)·tentKernel(n) − e^{π/T}(1+e^{π/T})ℓ_k²/2`,
  avec `tentKernel = min(e^{π/T}(t − C_k), C_{k+2} − t)` ; `tentKernel_eq_left/right` (branches), `tentKernel_nonneg`, `tentKernel_peak`
  (sommet `C_{k+1}`, hauteur `ℓ_{k+1}`), `tentKernel_le`. Le terme local est la discrépance des premiers des deux cellules contre un
  noyau chapeau continu dont l'intégrale est la part de Lebesgue.
* **H2 (mémoire un), théorème.** `localGrammarTerm_eq_memory_one` : `L_k = ε_{k+1} − e^{π/T} ε_k + e^{π/T} ℓ_k Δ_k`
  (`Δ_k = rawDemand C_{k+1} − rawDemand C_k`). `alternating_local_eq_exit_form` : la somme alternée des termes locaux s'écrit sur les
  déviations de sortie (premiers INTÉRIEURS à chaque cellule) et les variations de demande pondérées, à deux bords près.
* **H3 (loi d'échelle), explication compilée.** `abs_localGrammarTerm_le_of_demand_bound` : `|L_k| ≤ 2 e^{π/T} ℓ_k M` si `|rawDemand| ≤ M`
  sur `(C_k, C_{k+2}]`. Comme `ℓ_k = (e^{π/T} − 1) C_k` et `T(e^{π/T} − 1) → π`, la loi en `1/T` suit de « demande à l'échelle `√x` ».
* **H4 (contrôle intérieur), théorèmes.** `integral_psi_eq` (sommation d'Abel de Mathlib), `demandArea_eq_integral` : **l'aire de la
  demande EST l'intégrale de `rawDemand`** ; `demandArea_sub_eq_integral`, `exitDeviation_eq_integral` : `ε_k = ∫_{cellule} (D(t) − D(C_k)) dt` ;
  `abs_demandArea_le_of_bound`, `abs_demandArea_sub_le_of_variation`, `abs_cellArea_le_of_bound`, `abs_exitDeviation_le_of_variation`.
* **Clôture conditionnelle par la demande.** `sum_cellLength_eq` (les longueurs télescopent), `budget_le_of_demand_bound` et
  `budget_le_of_demand_bound'` : si `|rawDemand| ≤ M` sur la fenêtre, `(1+e^{π/T})|A_N| ≤ M (1+e^{π/T})² C_{k₀+N}`. Aucune alternance
  n'est utilisée. L'antécédent « `M = O(√x (log x)²)` » est de force RH (R-RH) ; on ne le présente pas comme une obligation nouvelle.

## Phase B — jumeau (`logs_twin_run.txt`, `twin_results.json`, 109 s ; 13 Tours, zéros n° 1 à 5000 ; premiers réels ≤ 3·10^7)
| Tour | T | cellules | H1 (rés./ℓ²) | H2 id. | corr lag 1 | corr lag 2 | T·max|L|/C^{3/2} | serrage médian / max | max M/√x | max ε/(ℓ√x) | max Δ/√x | max V/√x | rms A/B | corr(A,B) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 14,1 | 45 | 2,7e-14 | 1,5e-13 | −0,38 | −0,19 | 0,40 | 0,025 / 0,067 | 0,92 | 0,69 | 0,93 | 1,29 | 1,05 | −0,998 |
| 2 | 21,0 | 68 | 5,0e-14 | 3,2e-13 | −0,53 | −0,40 | 1,22 | 0,12 / 0,28 | 0,87 | 0,48 | 1,00 | 1,08 | 1,25 | −0,91 |
| 3 | 25,0 | 81 | 3,8e-14 | 2,5e-13 | −0,45 | −0,40 | 1,66 | 0,11 / 0,31 | 0,87 | 0,51 | 0,99 | 1,12 | 1,39 | −0,81 |
| 5 | 32,9 | 107 | 8,6e-14 | 3,0e-13 | −0,30 | −0,37 | 1,50 | 0,11 / 0,34 | 0,87 | 0,51 | 0,75 | 0,99 | 1,12 | −0,92 |
| 10 | 49,8 | 163 | 9,6e-14 | 5,0e-13 | −0,25 | −0,26 | 1,81 | 0,13 / 0,39 | 0,84 | 0,70 | 0,80 | 1,16 | 1,07 | −0,88 |
| 20 | 77,1 | 252 | 1,9e-13 | 5,5e-13 | −0,12 | −0,22 | 1,74 | 0,14 / 0,40 | 0,83 | 0,51 | 0,94 | 0,96 | 1,21 | −0,79 |
| 50 | 143 | 468 | 3,5e-13 | 1,3e-12 | −0,05 | −0,18 | 2,07 | 0,13 / 0,47 | 0,81 | 0,39 | 0,69 | 0,75 | 1,05 | −0,72 |
| 100 | 237 | 775 | 3,0e-13 | 1,2e-12 | +0,01 | −0,17 | 1,44 | 0,13 / 0,52 | 0,81 | 0,39 | 0,73 | 0,78 | 1,04 | −0,77 |
| 200 | 396 | 1299 | 4,9e-13 | 1,9e-12 | +0,05 | −0,14 | 1,28 | 0,13 / 0,51 | 0,81 | 0,37 | 0,63 | 0,67 | 0,89 | −0,73 |
| 500 | 811 | 2660 | 1,0e-12 | 2,8e-12 | +0,10 | −0,13 | 1,05 | 0,11 / 0,52 | 0,81 | 0,31 | 0,52 | 0,54 | 0,94 | −0,70 |
| 1000 | 1419 | 4657 | 3,4e-12 | 3,8e-12 | +0,10 | −0,09 | 1,06 | 0,10 / 0,54 | 0,81 | 0,23 | 0,37 | 0,40 | 0,93 | −0,69 |
| 2000 | 2515 | 8252 | 3,1e-12 | 5,0e-12 | +0,12 | −0,09 | 0,81 | 0,09 / 0,63 | 0,80 | 0,19 | 0,30 | 0,33 | 0,89 | −0,67 |
| 5000 | 5448 | 17876 | 1,3e-11 | 9,0e-12 | +0,14 | −0,08 | 0,61 | 0,075 / 0,74 | 0,80 | 0,20 | 0,23 | 0,24 | 0,83 | −0,62 |

(« serrage » = `|L_k| / (2 e^{π/T} ℓ_k M_k)`, l'inégalité compilée de H3 ; A = `ε_{k+1} − e^{π/T} ε_k`, B = `e^{π/T} ℓ_k Δ_k`, les deux
parts de H2 ; M, V = majorants de `|rawDemand|` et de sa variation intérieure, calculés sur les entiers des cellules.)

Tests pré-écrits : **H1 passé** (≤ 1,3e-11) ; **identité H2 passée** (≤ 9e-12) ; **inégalités compilées (H3, H4, budget) vérifiées sur
toutes les cellules** ; **H3 passé** (T·|L|/C^{3/2} ≤ 2,07 < 3) ; **H4a passé** (ε/(ℓ√x) ≤ 0,70, Δ/√x ≤ 1,0) ; **H4b passé** (rms A/B
entre 0,83 et 1,39) ; **H2 autocorrélation ÉCHOUÉ par la lettre** : le signe prédit est confirmé (négatif pour les Tours basses,
−0,38 pour la Tour 1 ; positif à partir de la Tour 100, +0,10 pour la Tour 1000), mais l'amplitude prédite (> +0,2) n'est pas atteinte
et, pour les Tours à moins de 110 cellules, les décalages 3 à 5 sont du bruit d'échantillon (ex. +0,89 au décalage 3 pour la Tour 2).

## Verdict
**B** (par la lettre : H2 autocorrélation). Deux modules verts ; toutes les identités conformes ; toutes les inégalités compilées
vérifiées numériquement ; H3, H4a, H4b passés.

## Constats
1. **Le terme local est une discrépance contre un chapeau** (théorème). Sa base est deux cellules, soit deux demi-tours de la phase de
   la Tour ; sa hauteur est la longueur de la cellule de sortie.
2. **Les deux parts de la mémoire un s'annulent presque** (mesure, pas théorème) : corr(A, B) de −0,998 (Tour 1) à −0,62 (Tour 5000), avec
   des moyennes quadratiques égales. Autrement dit, la différence des demandes moyennes de deux cellules consécutives (= `L_k/(e^{π/T}ℓ_k)`)
   est très inférieure à la différence des demandes aux contacts : le serrage médian de l'inégalité compilée est 0,025 (Tour 1) à 0,13.
   Lecture non compilée : les contacts sont les extrema de la part propre de la Tour ; la moyenne sur une cellule l'efface. Le chapeau
   d'une Tour est un noyau de Fejér de sa propre fréquence. Pour les Tours hautes, les cellules sont fines devant les oscillations basses
   et l'annulation faiblit (serrage max 0,74 à la Tour 5000).
3. **Loi d'échelle** : `T·|L_k|/C_k^{3/2}` entre 0,4 et 2,1 sur treize Tours ; l'explication compilée est `|L_k| ≤ 2e^{π/T}ℓ_k M`
   avec `M/√x ≤ 0,92` mesuré sur la plage : la loi en `1/T` est la longueur de cellule, pas une annulation.
4. **Le budget est très au-dessous de sa borne par la demande** : rapport 4e-5 à 2e-2. La borne compilée `M(1+e^{π/T})² C_N` est à
   l'échelle `x_N · M` ; elle n'utilise aucune alternance, et c'est pour cela qu'elle est lâche.
5. **Honnêtement** : RH n'est pas démontrée ; rien n'a été admis. La réduction compilée la plus courte de la cible est désormais :
   « budget à l'échelle `x_N^{3/2}` ⟸ `|rawDemand| ≤ M` sur la fenêtre avec `M = O(√x (log x)²)` » (force RH, R-RH). Ce n'est pas une
   obligation nouvelle, c'est la même obligation sans intermédiaire.

## Suite proposée (à pré-enregistrer seulement après mesure)
Le constat 2 est le seul fait neuf : l'annulation entre la part « déviations de sortie » et la part « variation de demande » de la
mémoire un. Prochaine mesure : décomposer `L_k` sur les premiers zéros (côté zéros, formes closes déjà compilées dans E472 pour les sommes
de cellules) et mesurer la part de `L_k` expliquée par la Tour elle-même, par les zéros plus bas, par les zéros plus hauts ; si la part
propre de la Tour est bien annulée par le chapeau (noyau de Fejér), l'écrire comme théorème sur le côté géométrique (aucune hypothèse
sur les premiers). Cela ne borne pas `L_k` depuis les premiers ; cela dit quelle part du terme local est déjà hors jeu.

## Classement (ordre de l'auteur, 2026-11-14, §19.108)
Résultat AUXILIAIRE : théorèmes acquis, aucune portée démonstrative vers RH. La tente est une construction géométrique sans obligation
arithmétique ; la « suite proposée » ci-dessus (décomposition côté zéros) est ABANDONNÉE. Voir `experiments/E475_SharedPrimeObligation/AUDIT_20261114.md`.
