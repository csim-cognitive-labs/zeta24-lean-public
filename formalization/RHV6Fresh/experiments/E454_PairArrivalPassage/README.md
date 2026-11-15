# E454 — K4 : la paire lue comme passage depuis l'arrivée basse — pré-enregistrement

Date : 2026-11-08. Statut : pré-enregistré avant toute compilation (§19.77). Feu vert de l'auteur après K3 (« continues, tu
as le feu vert »). Ordres : ban spectral total (usage et citation ; deux termes au plus, aucune somme de Tours) ; troisième
ordre (contacts lisent `β`) ; R-E446 ; §19.44 ; interdit « amplitude contre budget » ; aucune prémisse équivalente à RH ;
plage utile `β ≤ 1/2` pour l'arrivée (§19.76) ; deux tentatives de compilation au plus, chacune journalisée dans `attempts/`.

## Question K4 (§19.77.2)
K0–K3 décrivent la paire par ses deux termes. Que compile le corpus sur la paire lue comme PASSAGE de l'énumération canonique :
place des deux membres, passage qui sort de l'arrivée basse, lecture de fréquence des deux membres, rapport à la prémisse unique ?

## Vérification de non-équivalence avec RH (faite avant, §19.77.3)
Aucune hypothèse posée ; conditions = cas sur un passage ou un zéro donné ; L6 = contraposée d'une équivalence déjà compilée ;
rien n'est affirmé sur l'existence d'arrivées basses. Réponse attendue consignée d'avance : forme du passage OFF, AUCUNE
contradiction ; la frontière reste la prémisse unique (⟺ RH).

## Énoncés Lean (module isolé `Terminal/PairArrivalPassage.lean`, import `PairWordInversion`)
L1 `arrival_low_of_off` ; L2 `passage_height_le`, `passage_frozen_of_low_entry`, `passage_right_of_low_entry` ;
L3 `low_arrival_precedes_mirror`, `low_entry_successor_radial_le`, `low_entry_successor_band` ;
L4 `low_arrival_contact_ratio_lt`, `low_arrival_term_ratio_tendsto_zero` ; L5 `frozen_passage_same_word_slope` ;
L6 `low_entry_not_expected`, `frozen_passage_has_low_member` ; L7 `arrival_exit_dichotomy`.

## Expériences
Aucune : K4 ne produit aucune conclusion numérique. Preuves d'exécution = journaux de compilation dans `attempts/`.

## Critère
Verdict A si les treize énoncés compilent en au plus deux tentatives, axiomes standards, zéro avertissement dans le module,
grep du ban vide, `lake build RHV6Fresh` complet vert. Sinon verdict B avec chaque échec consigné. Dans tous les cas la
réponse est consignée telle quelle ; toute contradiction qui apparaîtrait serait vérifiée pour non-équivalence avant d'être énoncée.
