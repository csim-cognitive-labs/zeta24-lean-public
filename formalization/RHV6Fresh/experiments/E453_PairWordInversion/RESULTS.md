# E453 — K3 : l'inversion d'E449 appliquée au mot du miroir — résultats (2026-11-08)

## Lean
Deux sondes en brouillon (`attempts/probe1.txt` : `rw [div_add_div …]` ne trouve pas son motif dans `word_slope_bracket`,
réécrit par une identité `key` puis `abs_add_le` ; `attempts/probe2.txt` : EXIT 0). Module définitif
`Terminal/PairWordInversion.lean` : **tentative 1 verte** (`attempts/build_attempt1.txt`, 9096 jobs), 12 déclarations, 0
avertissement dans le module, axiomes `[propext, Classical.choice, Quot.sound]` sur les 12 (`attempts/axioms_attempt1.txt`),
grep du ban vide, `lake build RHV6Fresh` complet vert (`logs/lake_build_full.txt`, 9064 jobs).

Compilé : L1 `mirror_tower_of_two_contacts` (deux contacts du miroir rendent `T` et `1−β`), `mirror_word_slope_tendsto`,
`word_slope_bracket` (`|k/log x − T/π| ≤ (|φ|+π)/(π log x)` pour tout mot) ; L2 `mirror_word_determines_mirror` ; L3
`pair_of_same_word`, `mirror_word_of_same_word` (**le mot du miroir est fonction du mot de la Tour**) ; L4
`pair_words_eq_iff` (mots identiques sur tous les premiers ⟺ `β = 1/2`) ; L5 `cellFraction_primes_small_and_near_one_from`,
`pair_words_differ_beyond`, `pair_words_differ_beyond_iff` (hors ligne, mots distincts au-delà de tout rang, et réciproquement) ;
L6 `zero_pair_words_eq_iff`, `zero_pair_words_differ_beyond` (au paramètre d'un zéro vrai et de son miroir).

## Expérience (a) — 24 couples, tous les premiers ≤ 10⁷ (`logs/e453a_log.txt`, `data/e453a_results.json`)
* H2 (encadrement de la pente, deux mots, 664 579 premiers × 24) : **0 violation** ; pente du mot du miroir au dernier premier
  à `3·10⁻²` de `T/π` au rang 1, `6·10⁻²` au rang 10⁵ (écart borné par `(|φ|+π)/(π log p)`).
* Polygone d'E449 appliqué au mot du miroir (X = 10⁴ et 10⁶) : **vrai point `(T, φ*)` dedans pour les 24 couples** ; largeur
  de `T` à X = 10⁶ entre `4·10⁻⁵` et `3·10⁻⁴`.
* H1 (inversion tangentielle du miroir, flottants doubles) : `10⁻¹¹` au rang 1, `4·10⁻¹⁰` au rang 10, `10⁻⁷` au rang 100,
  `10⁻⁵` au rang 10³, `10⁻²` au rang 10⁴, **3,7 à 4,2 au rang 10⁵** (sur la ligne aussi) : le seuil pré-écrit `10⁻¹⁰` n'est
  tenu qu'au rang 1. Cause : conditionnement, `β = T/tan φ` amplifie l'erreur de `φ` par `T`, et `φ_rec = T_rec·log C − kπ`
  perd `T·log C ≈ 10⁶` fois la précision machine ; ce n'est pas l'identité qui manque (voir (c)).
* H4 (mot du miroir recalculé depuis `(β, T)` rendus par l'inversion du mot de la Tour) : 0 écart jusqu'au rang 10³, 1 au rang
  10⁴ (`β = 0,4`), 27 au rang 10⁵ : même cause de conditionnement (voir (c)).
* H5 (ligne) : **0 mot distinct** sur les 6 couples ligne. H6 (hors ligne) : mots distincts 6549 / 3278 / 1613 au rang 1
  (`β = 0,3 / 0,4 / 0,45`), croissant par décade (0, 0, 1, 12, 77, 598, 5861), dernier au-delà de `9,9·10⁶` ; 1635 / 827 / 408
  au rang 10 ; 346 / 172 / 85 au rang 100 ; 62 / 35 / 17 au rang 10³ ; 4 / 4 / 1 au rang 10⁴ ; **1 / 0 / 0 au rang 10⁵**
  (fenêtre `|δ|/π ≈ 4·10⁻⁷`). Le critère pré-écrit « > 0 à chaque décade » est **faux** : aucun premier < 100 ne diffère, et au
  rang 10⁵ la fenêtre est trop étroite pour 10⁷. Le critère était mal écrit ; l'énoncé compilé (« au-delà de tout rang ») ne
  porte aucun taux, et les comptes observés croissent avec la décade sans jamais finir dans la plage là où la fenêtre le permet.

## Expérience (b) — jumeau mpmath 30 chiffres (`logs/e453b_log.txt`, 240 cas)
Mots de la Tour et du miroir **identiques aux mots numpy** (écart 0 sur 240) ; H2 **0 violation** ; H1 : `1,6·10⁻²⁰` au rang 10³,
`10⁻¹⁷` au rang 10⁴, `6·10⁻¹⁵` au rang 10⁵ : 102 cas au-dessus du seuil pré-écrit `10⁻²⁰` (rangs 10³–10⁵), même conditionnement.

## Expérience (c) — contrôle POST-HOC à 30 et 60 chiffres (`logs/e453c_log.txt`, ajouté après lecture de (a)/(b))
Erreur de l'inversion du miroir divisée par `≈ 10³⁰` entre 30 et 60 chiffres sur les 24 couples (`3,5·10⁻⁴⁵` au pire au rang
10⁵) : l'identité est exacte, l'erreur est de conditionnement. H4 à 60 chiffres : **0 écart** sur 240 mots.

## Verdict
**B** sur les critères pré-enregistrés (H1 à `10⁻¹⁰` tenu au rang 1 seulement en doubles, H4 avec écarts aux rangs 10⁴–10⁵,
critère de décade de H6 mal écrit), avec cause de chaque drapeau consignée et confirmée par le contrôle (c). Les douze
énoncés sont compilés sans réserve. Aucune hypothèse posée, aucune contradiction tirée.

## Réponse à la question K3
L'inversion d'E449 appliquée au mot du miroir rend `(1−β, T)` exactement ; toute Tour ayant ce mot est le miroir ; deux Tours
sont lisibles ; **le mot du miroir est fonction du mot de la Tour** (il n'exige aucune donnée que les écarts ne porteraient
qu'une fois : la première donnée le contient). Les deux mots coïncident partout si et seulement si la paire est sur la ligne,
et diffèrent au-delà de tout rang sinon. **Aucune contradiction.** Le plan K0–K3 de §19.72 se ferme sans hypothèse de
contradiction ; consigné tel quel, décision à l'auteur.

## Rectification de l'auteur (2026-11-08, §19.76) : la plage utile est `β ≤ 1/2`

Commentaire de l'auteur : « du fait du régime certifié démarrage à ON, `β > 1/2` est déjà exclu ; c'est compilé et poussé »,
donc « théorème pour toute `β ∈ (0,1)` » (README §non-équivalence, §19.75.2) est inutilement large. Vérifié dans le corpus :
`passage_entry_radial_le_half` (RaccordDetector) donne `β ≤ 1/2` pour le membre d'entrée de toute hauteur nouvelle, par
l'ordre seul, sans hypothèse ; `first_passage_no_shared_frequency` / `anchor_canonical_one` (MeetingPoint) : le premier zéro
est ON et démarre le régime ; `arrival_onLine_or_low` : sous historique ON, arrivée sur la ligne ou strictement en dessous.
Un zéro `β > 1/2` n'est jamais une arrivée, c'est le miroir d'une arrivée basse. Le README n'est pas réécrit (pré-enregistrement) ;
la rectification est consignée ici, en §19.76 et dans le hand-over.

Section L7 ajoutée au module (deuxième tentative de compilation, `attempts/probe3.txt` sonde verte,
`attempts/build_attempt2.txt`, `attempts/axioms_attempt2.txt`) : `low_pair_words_differ_beyond`,
`low_pair_words_differ_beyond_iff` (sous un demi, `β < 1` superflu), `arrival_radial_le_half`,
`arrival_pair_words_differ_beyond_iff` (arrivée : mots distincts au-delà de tout rang ⟺ `β < 1/2`),
`arrival_pair_words_dichotomy` (ligne et mots identiques partout, ou arrivée basse et mots distincts au-delà de tout rang ;
aucun troisième cas). Le verdict B, la réponse à K3 (AUCUNE contradiction) et la fermeture du plan K0–K3 sont inchangés.

