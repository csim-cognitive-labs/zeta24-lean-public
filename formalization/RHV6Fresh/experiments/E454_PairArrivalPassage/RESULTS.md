# E454 — K4 : la paire lue comme passage depuis l'arrivée basse — résultats (2026-11-08)

Pré-enregistré (§19.77, commit 32ce2843) avant toute compilation. Feu vert de l'auteur après K3.

## Compilation
* `attempts/probe1.txt` : sonde scratch, EXIT=1 — `passage_height_le` existait déjà (`InterTowerExcess.lean:141`, même énoncé) :
  réutilisé, non dupliqué (règle « grep avant »). Sonde supprimée après capture.
* `attempts/probe2.txt` : sonde corrigée, EXIT=0, 0 avertissement.
* `attempts/build_attempt1.txt` : `lake build RHV6Fresh.Terminal.PairArrivalPassage` vert (9097 jobs), 0 avertissement dans le
  module ; `attempts/axioms_attempt1.txt` : 12/12 déclarations sur `[propext, Classical.choice, Quot.sound]`.
* Grep du ban (`smoothedRemainder|remainderExponent|OffCarrier|complement|familyRe|CollectiveCurvature`) : 0 occurrence.
* `logs/lake_build_full.txt` : `lake build RHV6Fresh` complet vert (9064 jobs). Module isolé, non ajouté à `RHV6Fresh.lean`.

## Énoncés compilés (12)
L1 `arrival_low_of_off` · L2 `passage_frozen_of_low_entry`, `passage_right_of_low_entry` · L3 `low_arrival_precedes_mirror`,
`low_entry_successor_radial_le`, `low_entry_successor_band` · L4 `low_arrival_contact_ratio_lt`,
`low_arrival_term_ratio_tendsto_zero` · L5 `frozen_passage_same_word_slope` · L6 `low_entry_not_expected`,
`frozen_passage_has_low_member` · L7 `arrival_exit_dichotomy`.

## Verdict : A (critère pré-écrit satisfait)
Réponse conforme à l'attente consignée d'avance : forme complète du passage OFF (arrivée basse = membre faible, puis miroir
dominant sans montée de fréquence, successeur dans `(β, 1−β]`, même pente de mot) ; AUCUNE contradiction ; la frontière reste
la prémisse unique `ExpectedFrequencyRisesAtMeetings` (⟺ RH). Aucune expérience numérique (aucune conclusion numérique).
Décision sur la suite : à l'auteur.
