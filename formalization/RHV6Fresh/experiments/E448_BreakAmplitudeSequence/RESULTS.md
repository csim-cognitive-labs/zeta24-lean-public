# E448 — Résultats : la suite des amplitudes de paiement d'une Tour de la ligne (§19.70, 2026-11-08)

Pré-enregistrement : `README.md` (commit `b90b7c9e`, avant toute compilation). Ordre R-LIGNE respecté : ligne seulement,
aucune contradiction cherchée, aucune obligation proposée.

## Partie compilée : `Terminal/BreakAmplitudeSequence.lean` (module isolé, importe `BreakMechanismOnLine`)
Sondes en brouillon (`E448_SCRATCH.lean`, supprimé) : `attempts/probe1.txt` (1 erreur : un `ring` après un `field_simp`
qui fermait déjà le but, ligne 102), `attempts/probe2.txt` (vert). Module définitif : `attempts/build_attempt1.txt`
**vert à la première tentative** (9091 jobs), 17 déclarations sur `[propext, Classical.choice, Quot.sound]`.
`attempts/build_attempt2.txt` et `attempts/build_attempt3_docstring_only.txt` : rebuilds après modification de l'en-tête
de documentation SEULEMENT (lignes trop longues puis une ligne dupliquée) ; aucune preuve touchée, verts. Les
avertissements de longueur de ligne sont ceux de tout le corpus (6 358 dans le build d'E447 aussi) ; aucun n'est une erreur.
Grep du ban spectral sur le module : vide. `lake build RHV6Fresh` complet : vert (9064 jobs).

| bloc | énoncés | ce qui est compilé |
|---|---|---|
| L1 | `cellFraction_step`, `cellFraction_step_eq_fract_sum`, `cellFraction_step_gap`, `displacement_add_fraction_eq` | la fraction de cellule au point suivant est la partie fractionnaire de la fraction courante plus `T·log(y/x)/π` (toute `β`) ; déplacement de cellules + variation de fraction = `T·log(y/x)/π` |
| L2 | `line_abs_value_pos`, `line_abs_value_succ`, `line_abs_value_add_nat`, `line_abs_value_sub` | sur la ligne `|v_{k+1}| = e^{π/(2T)}|v_k|`, `|v_l| = e^{π(l−k)/(2T)}|v_k|`, valeurs jamais nulles |
| L3 | `line_break_amplitude_ratio_cells`, `line_break_amplitude_ratio_exact` | rapport des amplitudes de paiement entre deux points = `e^{π·(déplacement)/(2T)}` = `√(y/x)·e^{−π(f(y)−f(x))/(2T)}` |
| L4 | `line_break_amplitude_mono`, `line_break_amplitude_eq_iff_same_cell`, `line_break_amplitude_step_of_new_cell` | l'amplitude ne décroît jamais ; constante si et seulement si même cellule ; sinon multipliée par au moins `e^{π/(2T)}` |
| L5 | `line_break_amplitude_ratio_bounds` | rapport strictement entre `√(y/x)·e^{−π/(2T)}` et `√(y/x)·e^{π/(2T)}` |
| L6 | `line_break_amplitude_telescope`, `line_break_amplitude_series`, `line_break_price_mono` | produit des rapports sur une série = `e^{π·(cellules franchies)/(2T)}` ; instance sur les premiers de rang `n`, `n+J` ; le prix `|v|·log q` ne décroît pas |

Hypothèses H1–H6 du pré-enregistrement : toutes compilées (H1 = L1, H2–H3 = L2–L3, H4 = L4, H5 = L5, H6 = L6).

## Expérience chiffrée (`scripts/e448a_amplitude_sequence.py`, journal `logs/e448a_log.txt`, `data/e448a_results.json`)
Zéros d'Odlyzko (SHA-256 vérifié), `β = 1/2`, 7 hauteurs (rangs 1, 10, 10², 10³, 10⁴, 10⁵, 2·10⁶), 664 578 paires de
premiers consécutifs ≤ 10⁷.

| rang | orbite (résidu circulaire max) | rapport, forme cellules | rapport, forme exacte | monotonie / bornes / « même cellule ⟺ égalité » | paires dans une même cellule |
|---|---|---|---|---|---|
| 1 | 2,2·10⁻¹⁴ | 1,4·10⁻¹⁵ | 3,9·10⁻¹⁵ | 0 / 0 / 0 | 664 512 |
| 10 | 6,3·10⁻¹⁴ | 1,7·10⁻¹⁵ | 3,3·10⁻¹⁵ | 0 / 0 / 0 | 664 374 |
| 10² | 3,6·10⁻¹³ | 1,3·10⁻¹⁵ | 3,8·10⁻¹⁵ | 0 / 0 / 0 | 663 753 |
| 10³ | 2,0·10⁻¹² | 2,4·10⁻¹⁵ | 3,6·10⁻¹⁵ | 0 / 0 / 0 | 660 607 |
| 10⁴ | 1,6·10⁻¹¹ | 2,7·10⁻¹⁵ | 4,9·10⁻¹⁵ | 0 / 0 / 0 | 643 950 |
| 10⁵ | 1,3·10⁻¹⁰ | 1,8·10⁻¹⁵ | 4,4·10⁻¹⁵ | 0 / 0 / 0 | 562 102 |
| 2·10⁶ | 2,0·10⁻⁹ | 2,2·10⁻¹⁵ | 5,6·10⁻¹⁵ | 0 / 0 / 0 | 166 681 |

Le résidu de l'orbite croît avec `T` comme la perte de précision flottante de `T·log p` (position d'étage jusqu'à ~6·10⁶) ;
le jumeau à 30 chiffres le ramène à 10⁻²⁶ ou moins. Identité déplacement + fraction : résidu max 2,0·10⁻⁹ (même cause).
Violations de « nouvelle cellule ⇒ facteur ≥ e^{π/(2T)} » : 0 partout. Télescopage par décade : résidu ≤ 2,4·10⁻¹⁵.
Paires dans une même cellule par décade de `p_n` (rang 10⁴) : 0/4, 0/21, 0/143, 12/1 061, 3 413/8 363, 61 684/68 906,
578 841/586 080 : au-dessus du seuil d'E446 les cellules s'allongent plus vite que les écarts et presque toutes les
rencontres successives partagent une cellule (déplacement 0), donc même amplitude de paiement ; au rang 2·10⁶ le
déplacement maximal entre deux premiers consécutifs est 184 055 cellules dans la première décade et 35 dans la dernière.

## Jumeau (`scripts/e448b_twin_mpmath.py`, 30 chiffres, sympy, journal `logs/e448b_log.txt`, `data/e448b_twin.json`)
Rangs 1, 10², 10⁴, paires avec `p_n < 10⁶` : orbite ≤ 1,7·10⁻²⁶, rapport forme cellules ≤ 1,8·10⁻³⁰, forme exacte
≤ 3,8·10⁻³⁰, 0 violation de monotonie, comptages « même cellule » par décade identiques aux entiers de e448a
(par exemple rang 10⁴ : 0, 0, 0, 12, 3 413, 61 684). `all_ok = True`.

## Verdict
**A** : toutes les identités compilées sont exactes à la précision du calcul (flottant puis 30 chiffres), aucune violation
des inégalités, comptages entiers identiques entre les deux calculs indépendants.

## Ce que cela établit (ligne seulement, par ordre)
La suite des amplitudes avec lesquelles une Tour de la ligne paie les cassures successives est entièrement déterminée
par la suite des rapports de premiers consécutifs : la fraction de cellule suit une orbite de translations par
`T·log(p_{n+1}/p_n)/π` modulo un ; l'amplitude de paiement est multipliée, d'un premier au suivant, par `e^{π/(2T)}`
élevé au nombre de cellules franchies (déplacement exact d'E442), ce qui s'écrit aussi `√(p_{n+1}/p_n)` corrigé par
la variation de fraction ; elle ne décroît jamais, reste constante exactement quand les deux premiers partagent une
cellule, et son logarithme sur une série de rencontres croît exactement de `π/(2T)` fois le nombre de cellules
franchies. Rien n'est dit des OFF ; aucune obligation n'est proposée.
