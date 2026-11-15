# E446 — Résultats : le régime « une rencontre par cellule » est fini ; le budget exact d'une cellule est sa longueur (2026-11-07)

Pré-enregistrement : `README.md` (copie du §19.68), commit `86cbac83` avant toute compilation et toute exécution.

## Partie compilée : `Terminal/MeetingRegimeFinite.lean` (module isolé, importe `MeetingPriceTheorem` et `LogGapsTheorem`)
Deux tentatives (`attempts/build_attempt1.txt`, `attempts/build_attempt2.txt`).
* **Tentative 1** : 10 erreurs, toutes de forme : (i) argument implicite `β` non inféré dans `cellDemand_eq hT k` et
  `cellWeight_div_cellLength_tendsto_one hT k₀` (lignes 116, 162) ; (ii) `ring` après un `field_simp` qui fermait déjà
  le but (lignes 158, 193, « No goals to be solved »). F1–F4, F7, F9 compilaient déjà sur les axiomes standards ;
  F5–F6 portaient `sorryAx` par propagation des erreurs.
* **Tentative 2** : `(β := β)` explicité, les deux `ring` retirés. **Build completed successfully (9089 jobs)** ; les sept
  déclarations imprimées (`log_ratio_ge_cell_of_meeting`, `two_consecutive_contacts_finite`, `meeting_break_rank_bounded`,
  `cellWeight_div_cellLength_tendsto_one`, `cellDemand_div_cellLength_tendsto_zero`,
  `tower_step_div_cellLength_tendsto_zero`, `valuePrimeSum_balance`) dépendent de `[propext, Classical.choice, Quot.sound]`.
  `lake build RHV6Fresh` complet : vert (9064 jobs).

Énoncés compilés (15 déclarations) :
* F1 `meeting_cell_within_two_gaps` : si l'écart `n` et l'écart `n+1` ont chacun un contact, la cellule de la rencontre
  `p_{n+1}` vérifie `p_n < C_k` et `C_{k+1} ≤ p_{n+2}`.
* F2 `log_ratio_ge_cell_of_meeting` : sous ces hypothèses, `π/T ≤ log p_{n+2} − log p_n`.
* F3 `two_consecutive_contacts_finite` : pour toute Tour `(β, T)`, `∃ N, ∀ n ≥ N`, les écarts `n` et `n+1` n'ont pas
  chacun un contact (par `logGapsVanish_holds`, PNT porté).
* F4 `meeting_series_rank_bounded` (les hypothèses de `valuePrimeSum_eq_meetings` avec `J ≥ 1` imposent `n < N`),
  `meeting_break_rank_bounded` (les hypothèses de `cellPrimeWeight_meeting` imposent `I.rank < N`).
* F5 `cellWeight_eq_psi_diff` (`cellWeight = ψ(C_{k+1}) − ψ(C_k)`), `contactAt_tendsto_atTop`,
  `cellWeight_div_cellLength_tendsto_one` (par `WeakPNT''`).
* F6 `cellDemand_div_cellLength_tendsto_zero`.
* F7 `tower_step_div_cellLength_tendsto_zero` : `|v_{k+1} − v_k| / cellLength_k → 0` pour tout `0 < β < 1`.
* F8 `price_beats_budget_on_line` : `K log x < x^{1/2}` pour `x` grand (P6 vaut sur la ligne).
* F9 `valueNonPrimeSum`, `valuePrimeSum_balance`.

## Expérience chiffrée (`scripts/e446a_regime.py`, journal `logs/e446a_log.txt`, `data/e446a_results.json`)
Premiers ≤ 10⁷ (664 579), sept hauteurs d'Odlyzko (rangs 1, 10, 100, 10³, 10⁴, 10⁵, 2·10⁶), `β ∈ {½ ; 0,3 ; 0,7 ; 0,4 ; 0,6 ;
0,45 ; 0,55}`, 49 configurations, 3,3 s.

**(a) Régime.** Dernier rang `N_obs` où deux écarts consécutifs ont chacun un contact, et nombre de tels rangs :

| rang de la hauteur | T | N_obs | p_{N_obs} | rangs à deux contacts | violations F2 |
|---|---|---|---|---|---|
| 1 | 14,13 | 10 | 31 | 7 | 0 |
| 10 | 49,77 | 60 | 283 | 24 | 0 |
| 100 | 236,5 | 366 | 2 477 | 114 | 0 |
| 1 000 | 1 419 | 2 343 | 20 809 | 603 | 0 |
| 10 000 | 9 878 | 24 985 | 286 873 | 4 007 | 0 |
| 100 000 | 74 921 | 211 310 | 2 917 973 | 29 219 | 0 |
| 2 000 000 | 1 131 944 | 664 564 | 9 999 761 | 366 916 | 0 |

`N_obs` ne dépend pas de `β` (identique pour les sept valeurs, à `T` fixé) ; il croît avec `T` ; pour la hauteur de rang
2·10⁶ le régime n'est **pas résolu sous 10⁷** (le dernier rang est le dernier premier de la table : la finitude est
garantie par F3, non observée dans la plage). 0 violation de F2 sur les 401 890 rangs à deux contacts.

**(b) Budget par cellule.** `max |cellWeight/cellLength − 1|` par décade de `C_k` (moyenne du rapport à 10⁶ : 1,000 pour
toutes les hauteurs) :

| T | 10² | 10³ | 10⁴ | 10⁵ | 10⁶ |
|---|---|---|---|---|---|
| 14,13 | 0,178 | 0,052 | 0,025 | 0,004 | 0,002 |
| 49,77 | 0,686 | 0,238 | 0,087 | 0,021 | 0,010 |
| 236,5 | 3,34 | 1,07 | 0,269 | 0,110 | 0,038 |
| 1 419 | 19,7 | 5,14 | 1,05 | 0,371 | 0,136 |
| 9 878 | 143 | 20,6 | 4,77 | 1,45 | 0,453 |
| 74 921 | 1 089 | 162 | 21,0 | 4,54 | 2,23 |
| 1 131 944 | 16 463 | 2 469 | 331 | 40,5 | 8,96 |

Décroissance monotone vers 0 pour chaque hauteur ; la convergence effective (écart < 0,01) n'est atteinte sous 10⁷ que
pour les deux premières hauteurs : pour les hauteurs élevées les cellules sont encore plus courtes que l'écart moyen
(`C_k π/T < log C_k`), régime où une cellule contient zéro ou un entier (rapport 0 ou grand). Conforme à F5 (limite),
non résolu numériquement pour `T ≥ 236` dans la plage.

**(c) Pas de la Tour sur sa cellule / longueur.** Formule F7 vérifiée à 1,4·10⁻⁹ au pire (hauteur 1,1·10⁶, arrondi
flottant), 10⁻¹⁴–10⁻¹² ailleurs ; rapport décroissant en `C^{β−1}` : à `T = 14,13`, de 6,2·10⁻² (`C = 95`) à 2,4·10⁻⁴
(`C = 6,4·10⁶`) pour `β = ½`, de 2,4·10⁻² à 1,0·10⁻⁵ pour `β = 0,3`, de 1,6·10⁻¹ à 5,6·10⁻³ pour `β = 0,7`.

## Jumeau (`scripts/e446b_twin_mpmath.py`, 30 chiffres, journal `logs/e446b_log.txt`, `data/e446b_twin.json`)
Premiers exacts ≤ 10⁶ (sympy), contacts en mpmath, `Λ` par factorisation exacte. `N_obs` identique à (a) sur les 35
configurations comparables (hauteurs de rangs 1 à 10⁴, où `N_obs` tombe sous 10⁶) ; 0 violation de F2 ; rapports
poids/longueur sur 12 cellules entre 10³ et 10⁴ : autour de 1 pour `T = 14` (0,95–1,06) et `T = 50` (0,76–1,22), 0 ou
grands pour les hauteurs élevées (cellules sans entier), comme en (a). `all_ok = True`.

## Verdict
**A** pour la partie compilée (F1–F9, deux tentatives, axiomes standards) et pour (a) et (c) ; (b) conforme en limite,
résolu numériquement pour les deux premières hauteurs seulement (explicité ci-dessus).

## Ce que cela établit, et ce qui reste
1. Les énoncés « la cellule de rencontre franchit exactement un premier » et toute la série des rencontres à un premier
   par cellule (E439–E445 : `meeting_cell_primes`, `cellPrimeWeight_meeting`, `meeting_cellDemand`,
   `valuePrimeSum_eq_meetings`, `amplitudeMeetingSum`) ne valent qu'à rang borné `N(β, T)` : pour la première Tour,
   jusqu'à `p = 31`. Le prix à `M_n` (P4–P6) n'est confronté au budget `log p` d'une rencontre que sur ce segment fini.
2. Au-delà, le budget exact d'une cellule est `ψ(C_{k+1}) − ψ(C_k)`, équivalent à la longueur de la cellule ; la variation
   de la demande brute sur la cellule est `o(cellule)` (PNT porté) ; le pas de toute Tour `0 < β < 1` sur sa cellule est
   `o(cellule)` : le prix d'une Tour, ON ou OFF, ne bat jamais le budget d'une cellule. P6 n'était pas discriminant (F8).
3. La confrontation ne peut porter que sur la variation de `rawDemand` sur la cellule (objet autorisé) contre le pas de
   la paire ; le corpus ne compile aucune relation entre l'amplitude d'une Tour et cette variation, et ne sait de cette
   variation que `o(cellule)`. C'est l'obligation ouverte, consignée au §19.68, sans objet spectral.

   **Correction de l'auteur (2026-11-07)** : cette obligation n'est pas la bonne ; la contradiction OFF ne doit pas être
   liée à une relation « amplitude ↔ variation de `rawDemand` par cellule ». Elle est retirée (§19.68, « Correction de
   l'auteur »). Les points 1 et 2 restent établis.
