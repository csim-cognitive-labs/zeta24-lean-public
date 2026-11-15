# E448 — La suite des amplitudes de paiement d'une Tour de la ligne aux rencontres successives (pré-enregistrement, §19.70, 2026-11-08)

Ordre de l'auteur (R-LIGNE) : tant qu'il reste du Lean à écrire, ne pas chercher la contradiction ; maîtriser le mécanisme
de cassure depuis la ligne (zéros ON, `β = 1/2`). Candidat C3 du hand-over du 2026-11-07, choisi en l'absence d'indication
de l'auteur. Objets autorisés : une Tour `(1/2, T)`, ses contacts, ses cellules, sa fraction de cellule `f`, ses valeurs
réelles aux contacts ; les premiers consécutifs. Aucune somme de Tours, aucun objet spectral, aucune hypothèse, aucun
énoncé sur `β ≠ 1/2`, aucune obligation proposée.

## Point de départ (E447, compilé)
La cassure `log q` au premier `q` est payée avec l'amplitude du dernier contact avant `q`, EXACTEMENT
`√q · e^{−π f(q)/(2T)} / ‖(1/2, T)‖`, où `f(q)` est la fraction de cellule au point `q` (`line_break_amplitude_exact`).
La question d'E448 : comment cette amplitude évolue-t-elle d'un premier au suivant, et par quoi la suite est-elle déterminée ?

## Hypothèses (à décider par le compilateur, puis par le nombre)
* H1 (orbite de la fraction) : la fraction de cellule au point suivant est la partie fractionnaire de la fraction au point
  courant plus `T·log(y/x)/π` : `f(y) = fract(f(x) + T·log(y/x)/π)`. La suite des fractions aux premiers consécutifs est
  donc une orbite de translations par `T·log(p_{n+1}/p_n)/π` modulo un, déterminée par les rapports de premiers consécutifs.
* H2 (pas d'amplitude par cellule) : sur la ligne, `|v_{k+1}| = e^{π/(2T)} |v_k|` ; donc l'amplitude de paiement au point `y`
  sur celle au point `x` vaut `e^{π (k(y) − k(x))/(2T)}`, où `k(y) − k(x)` est le déplacement de cellules
  (`displacement_rule` : `⌊T·log(y/x)/π⌋` plus une retenue lue par la fraction).
* H3 (forme exacte du rapport) : le même rapport vaut aussi `√(y/x) · e^{−π (f(y) − f(x))/(2T)}` ; les deux écritures sont
  compatibles parce que `T·log(y/x)/π = (k(y) − k(x)) + (f(y) − f(x))`.
* H4 (monotonie) : d'un premier au suivant, l'amplitude de paiement ne décroît jamais ; elle est constante exactement quand
  les deux premiers partagent une cellule (déplacement nul) ; sinon elle est multipliée par au moins `e^{π/(2T)}`.
* H5 (encadrement du rapport) : le rapport des amplitudes entre deux premiers consécutifs est strictement compris entre
  `√(y/x)·e^{−π/(2T)}` et `√(y/x)·e^{π/(2T)}`.
* H6 (télescopage) : sur une série de `J` rencontres, le produit des rapports est `e^{π (k(p_{n+J}) − k(p_n))/(2T)}` ; le
  logarithme de l'amplitude de paiement croît exactement de `π/(2T)` fois le nombre de cellules franchies.

## Énoncés prévus (module isolé `Terminal/BreakAmplitudeSequence.lean`, import `BreakMechanismOnLine`)
L1 `cellFraction_step` (H1), `cellFraction_step_eq_fract_sum` (forme avec la partie fractionnaire du déplacement) ;
L2 `line_abs_value_succ` (`|v_{k+1}| = e^{π/(2T)}|v_k|`), `line_abs_value_add_nat`, `line_abs_value_sub`
(`|v_l| = e^{π(l−k)/(2T)}|v_k|` pour `k ≤ l`) ;
L3 `line_break_amplitude_ratio_cells` (H2), `line_break_amplitude_ratio_exact` (H3), `displacement_eq_stagePosition_sub` (H3) ;
L4 `line_break_amplitude_mono` (H4), `line_break_amplitude_eq_iff_same_cell`, `line_break_amplitude_step_of_new_cell` ;
L5 `line_break_amplitude_ratio_bounds` (H5) ; L6 `line_break_amplitude_telescope` (H6), `line_break_price_mono_of_le`
(le prix `|v|·log q` ne décroît pas non plus).
Deux tentatives de compilation au plus sur le module définitif, chaque sortie conservée dans `attempts/` ; sondes en
`*_SCRATCH.lean` non versionné, supprimé après capture.

## Expérience (après compilation ; zéros d'Odlyzko, `β = 1/2`, 7 hauteurs, premiers ≤ 10⁷)
(a) orbite de la fraction : résidu de `f(p_{n+1}) − fract(f(p_n) + T·log(p_{n+1}/p_n)/π)` sur tous les premiers consécutifs ;
(b) rapport des amplitudes : les deux formes (H2 et H3) contre le calcul direct, résidus ; (c) violations de la monotonie
et de l'encadrement (attendu : zéro) ; (d) nombre de paires de premiers consécutifs qui partagent une cellule, par décade,
contre le nombre total de paires (régime fini d'E446 vu depuis la suite) ; (e) télescopage : logarithme du rapport entre
le premier premier et le dernier premier de chaque décade contre `π/(2T)` fois le nombre de cellules franchies.
Jumeau déterministe mpmath 30 chiffres sur un sous-ensemble (premiers ≤ 10⁶ par sympy, 3 hauteurs).
Critère : A si toutes les identités sont exactes à la précision flottante et (c) est nul ; B si une identité compile mais
le nombre contredit ; C sinon. Aucune conclusion sur les OFF n'est tirée, par ordre.
