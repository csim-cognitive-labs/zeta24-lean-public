# E450 — La cassure de la paire au premier partagé, cellules comprises (K0 + K1 du plan §19.72) — pré-enregistrement

Date : 2026-11-08. Statut : pré-enregistré avant toute compilation et toute exécution. Ordres : ban spectral total ; troisième
ordre ; R-E446 ; §19.44 ; aucune prémisse équivalente à RH ; deux tentatives de compilation au plus, chacune journalisée dans
`attempts/` ; sondes en `*_SCRATCH.lean` non versionnées, sorties conservées dans `attempts/probe*.txt`.

## Objet
Une paire `(β, T)`, `(1−β, T)` (`0 < β < 1`, `T > 0`) au premier partagé `q`. Objets du corpus : `contactAt`, `contactRealValue`,
`stagePosition`, `lastContactBefore` (le mot), `cellFraction`, `mirrorPhaseShift β T = arctan(T/β) − arctan(T/(1−β))`,
`offPrice`. Rien de spectral.

## Hypothèses
* H1 (amplitude exacte de la cassure, `β` quelconque) : `|v_β(k_β(q))| = q^β · e^{−βπ f_β(q)/T} / ‖(β,T)‖` (généralise
  `line_break_amplitude_exact`).
* H2 (deux mots) : `f_{1−β}(q) = fract(f_β(q) + mirrorPhaseShift β T / π)` ; les deux mots diffèrent d'au plus une cellule en
  chaque point ; décalage nul ⟺ ligne (déjà `mirrorPhaseShift_eq_zero_iff`).
* H3 (règle du carré de la paire) : `|v_β| · |v_{1−β}| = q · e^{−π(β f_β + (1−β) f_{1−β})/T} / (‖(β,T)‖ ‖(1−β,T)‖)` : le produit
  des deux cassures est une cassure de type ligne, avec fraction effective `β f_β + (1−β) f_{1−β} ∈ [0,1)` et norme produit.
* H4 (somme avec cellules) : `|v_β| + |v_{1−β}| ≥ e^{−π/T} (q^β/‖(β,T)‖ + q^{1−β}/‖(1−β,T)‖)` et `≤ q^β/‖(β,T)‖ + q^{1−β}/‖(1−β,T)‖` ;
  le prix d'E445 est retrouvé à un facteur de cellule borné près.
* H5 (séparation) : `|v_β|/|v_{1−β}| = q^{2β−1} · e^{−π(β f_β − (1−β) f_{1−β})/T} · ‖(1−β,T)‖/‖(β,T)‖` ; non borné quand
  `q → ∞` dès que `β > 1/2` (et tend vers `0` si `β < 1/2`).
* H6 (K0, ligne) : sur la ligne, mot, suite des amplitudes de paiement et bilan pondéré normalisé ne distinguent pas les six
  zéros des trois contrôles (milieux entre zéros consécutifs) ; consigné d'avance comme attendu. Si une différence apparaît,
  elle est consignée telle quelle, sans obligation et sans lien aux OFF (R-E446).

## Énoncés Lean (module isolé `Terminal/PairBreakAtPrime.lean`)
* L1 `break_amplitude_exact (hβ : 0 < β) (hT) (hx)` (H1).
* L2 `mirror_cellFraction`, `mirror_word_difference_le_one` (H2 ; lemme auxiliaire `floor_sub_floor_le_one_of_abs_sub_le`).
* L3 `pair_break_product` (H3), `pair_effective_fraction_mem` (`∈ [0,1)` pour `0 ≤ β ≤ 1`).
* L4 `pair_break_sum_bounds` (H4).
* L5 `pair_break_ratio` et `pair_break_ratio_unbounded (hβ : 1/2 < β)` : `∀ K, ∀ᶠ x atTop, K < ratio` (H5).
* L6 `pair_break_product_on_line` : à `β = 1/2`, L3 redonne `line_break_amplitude_exact` au carré (cohérence).

## Expériences
* (a) K0, `scripts/e450a_census_line.py` : six zéros (rangs 1, 10, 100, 1000, 10000, 100000) et trois contrôles (milieux
  rangs 1–2, 100–101, 10000–10001), premiers `≤ 10^7` : statistiques du mot (moyenne, min, max des fractions ; part de paires
  consécutives en même cellule par décade), de la suite des amplitudes (rapport à `√q`, min/max), et bilan pondéré
  `valueCellSum` sur blocs de 50 cellules par décade normalisé par la borne P5 (E445). Critère H6 : les plages zéros et
  contrôles se recouvrent (aucune statistique ne sépare les deux groupes).
* (b) K1, `scripts/e450b_pair_break.py` : paires témoins `β ∈ {0,3 ; 0,4 ; 0,45}` aux fréquences des six zéros ; sur un
  échantillon de 100 000 premiers : H1 (erreur relative `≤ 10^{−12}`), H2 (fractions, 0 violation ; comptage des points où
  les deux mots diffèrent), H3 (produit, erreur `≤ 10^{−12}` ; fraction effective dans `[0,1)`), H4 (0 violation), H5
  (rapport, erreur `≤ 10^{−12}` ; valeur à `10^3, 10^4, …, 10^7`).
* (c) jumeau `scripts/e450b_twin_mpmath.py`, 30 chiffres, rangs 1 et 100, `β = 0,4`, 2 000 premiers : identités à `10^{−25}`.

## Verdict
A : L1–L6 compilent en ≤ 2 tentatives, (b) et (c) dans les seuils, (a) consigné. B : compilé, seuils manqués par précision
(expliqué). C : un énoncé ne compile pas (consigné, erreur exacte). Aucune conclusion de contradiction OFF n'est tirée d'E450 :
K1 fournit les objets, K2 posera la question.
