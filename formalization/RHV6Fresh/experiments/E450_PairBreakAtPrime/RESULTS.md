# E450 — Résultats : la cassure de la paire au premier partagé, cellules comprises (K0 + K1, §19.72, 2026-11-08)

Pré-enregistrement : `README.md`, commit `1b13cb42` avant toute compilation et toute exécution.

## Partie compilée : `Terminal/PairBreakAtPrime.lean` (module isolé, importe `BreakAmplitudeSequence`)
Deux sondes en brouillon (`attempts/probe1.txt` : 2 erreurs, toutes deux `linarith` devant `−(décalage)/π` lu comme un atome
distinct de `décalage/π` ; corrigé par `rw [neg_div] at h` ; `attempts/probe2.txt` : EXIT=0, aucun `sorryAx`). **Tentative
définitive 1 : verte** (`attempts/build_attempt1.txt`, 9092 jobs ; seuls avertissements : longueur de ligne de l'en-tête, comme
dans tout le corpus). Axiomes des huit énoncés imprimés : `attempts/axioms_attempt1.txt` (standards). Build complet
`lake build RHV6Fresh` : vert (`logs/lake_build_full.txt`, 9064 jobs). Grep du ban spectral sur le module : vide. 12 déclarations.

* L1 `break_amplitude_exact` : `|v_β(k_β(x))| = x^β · e^{−βπ f_β(x)/T}/‖(β,T)‖` pour tout `β > 0` (généralise E447).
* L2 `mirror_cellFraction` : `f_{1−β}(x) = fract(f_β(x) + mirrorPhaseShift β T/π)` ; `abs_mirrorPhaseShift_lt_pi` ;
  `floor_sub_floor_le_one_of_abs_sub_le` ; `mirror_word_difference_le_one` : les deux mots diffèrent d'au plus une cellule.
* L3 `pair_break_product` : produit des deux cassures `= x · e^{−π(β f_β + (1−β) f_{1−β})/T}/(‖(β,T)‖ ‖(1−β,T)‖)` ;
  `pair_effective_fraction_mem` : la fraction effective est dans `[0,1)`.
* L4 `break_amplitude_bounds`, `pair_break_sum_bounds` : `e^{−π/T}(x^β/‖ρ‖ + x^{1−β}/‖ρ'‖) ≤ somme ≤ x^β/‖ρ‖ + x^{1−β}/‖ρ'‖`.
* L5 `pair_break_ratio` : `x^{2β−1} · e^{−π(β f_β − (1−β) f_{1−β})/T} · ‖(1−β,T)‖/‖(β,T)‖` ; `pair_break_ratio_unbounded` :
  pour `β > 1/2`, `∀ K, ∀ᶠ x, K < rapport`.
* L6 `pair_break_product_on_line` : à `β = 1/2`, carré de `line_break_amplitude_exact`.

## Expérience (a) K0 — recensement sur la ligne (`scripts/e450a_census_line.py`, `logs/e450a_log.txt`, `data/e450a_results.json`)
Six zéros (rangs 1 … 100000) et trois contrôles (milieux 1–2, 100–101, 10000–10001), 664 579 premiers ≤ 10⁷, 663 411 ≥ 10³.
| statistique | zéros | contrôles | recouvrement |
|---|---|---|---|
| fraction moyenne | 0,5001 … 0,5144 | 0,4964 … 0,5003 | oui |
| amplitude/√q minimale | 0,8948 … 0,99998 | 0,9145 … 0,99984 | oui |
| part « même cellule » (décades 3–6) | 0,0000 … 1,0000 | 0,0075 … 1,0000 | oui |
| |bilan pondéré| / borne P5 | 3·10⁻⁹ … 0,099 | 5·10⁻⁷ … 0,055 | oui |
`H6_all_overlap = True`. Au rang 1 aucun bloc de 50 cellules ne tient dans une décade (41 cellules de 10³ à 10⁷) : pas de
bilan pondéré pour cette Tour, consigné. La part « même cellule » et le bilan dépendent de la fréquence seule, et les contrôles
de même fréquence approchée (rangs 100–101, 10000–10001) donnent les mêmes valeurs que les zéros voisins à 10⁻³ près.
**Constat K0 : aucune des statistiques du mot, de la suite des amplitudes ni du bilan pondéré ne sépare les zéros des
contrôles.** Conformément à R-E446 et au pré-enregistrement, aucune obligation n'en est tirée et rien n'est lié aux OFF.

## Expérience (b) K1 — paires témoins (`scripts/e450b_pair_break.py`, `logs/e450b_log.txt`, `data/e450b_results.json`)
Première exécution interrompue par une erreur d'indice sur le repère 10⁷ (`logs/e450b_run1_crash.stdout`, conservée) ;
repère corrigé en « dernier premier ≤ 10⁷ », seconde exécution complète. 18 couples (6 fréquences × β ∈ {0,3 ; 0,4 ; 0,45}),
100 000 premiers par couple, `all_ok = True` :
* H1 erreur relative maximale 5,1·10⁻¹⁵ ; H3 7,9·10⁻¹⁵ ; H5 4,4·10⁻¹⁵ (seuil 10⁻¹²).
* H2 : fraction du miroir à 7,4·10⁻¹¹ près au pire (rang 10⁵, perte de précision de `T·log p`) ; `|Δk| ≤ 1` partout ;
  part des premiers où les deux mots diffèrent = décalage/π : 0,0097 (rang 1, β = 0,3) → 0 (rang 10⁵, décalage 5·10⁻⁶).
* H3 : fraction effective dans `[0,001 ; 0,999]`, jamais hors de `[0,1)`. H4 : 0 violation sur 1 800 000 points.
* H5, rapport miroir/Tour au dernier premier ≤ 10⁷ : 631 (β = 0,3), 25,1 (0,4), 5,01 (0,45), identiques à 1 % près à toutes
  les fréquences : c'est `p^{1−2β}` (10^{2,8}, 10^{1,4}, 10^{0,7}), les facteurs de cellule et de norme s'effaçant.

## Jumeau (`scripts/e450b_twin_mpmath.py`, `logs/e450b_twin_log.txt`, `data/e450b_twin.json`)
30 chiffres, rangs 1 et 100, β = 0,4, 2 000 premiers : H1 2·10⁻³⁰, H2 1,3·10⁻²⁸, H3 3·10⁻³⁰, H5 1,9·10⁻³⁰, `|Δk| ≤ 1`
(9 points différents au rang 1, 1 au rang 100), 0 violation H4, `all_ok = True`.

## Verdict
**A** : L1–L6 compilés à la première tentative, (b) et (c) dans les seuils, (a) consigné (H6 : rien ne distingue les zéros).

## Ce que cela établit pour K2, et ce que cela ne dit pas
Les objets du paiement de la paire au premier partagé sont compilés : deux mots décalés d'au plus une cellule, amplitude exacte
de chaque membre, produit de type ligne, somme encadrée par le prix d'E445, rapport des membres `≈ p^{1−2β}` non borné.
Aucune contradiction n'est tirée ici ; K2 devra confronter la SÉPARATION des deux membres à ce que la rencontre exacte impose
aux deux au même premier, sans comparaison « amplitude contre budget » (réfutée par T2 d'E445 et par le budget de cellule
d'E446), et après vérification de non-équivalence avec RH.
