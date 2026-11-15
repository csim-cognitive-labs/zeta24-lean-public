# E455 — K5 : la fibre de l'arrivée basse, en fréquence seule (pré-enregistrement, 2026-11-08)

Référence : `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.78. Question de l'auteur : « les fréquences des OFF sont forcément
différentes de celles des ON : un OFF ne peut pas prendre la hauteur du ON occupée ni atteindre le prochain ON ».

## Audit (avant compilation)
* (a) compilé pour le ON suivi et l'historique (`no_shared_frequency_of_history_onLine`) ; NON compilé pour un ON postérieur de
  même hauteur = `NoMixedHeight` (⟸ RH, jamais dérivée).
* (b) compilé par l'ordre (`consecutive_no_height_between`, `frequency_never_decreases`) ; strict seulement hors fibre mixte.
* (c) compilé comme RÉPÉTITION de fréquence (fibre ≥ 2, `mirror_breaks_frequency_cascade`, `passage_frozen_of_low_entry`), pas
  comme valeur différente (bornes de rang aveugles au radial).

## Module
`RHV6Fresh/Terminal/LowArrivalFrequencyFibre.lean`, isolé, six énoncés M1–M6 (§19.78.3). Aucune amplitude.

## Réponse attendue (consignée d'avance)
Aucune contradiction. Le seul point ouvert est la fibre mixte, décidé par le côté du successeur de l'entrée basse. Frontière
inchangée (prémisse unique ⟺ RH ; `NoMixedHeight` ⟸ RH).

## Protocole
Deux tentatives au plus ; sondes scratch non versionnées, sorties capturées dans `attempts/` ; grep du ban avant build ;
`lake build RHV6Fresh` complet après la tentative verte.
