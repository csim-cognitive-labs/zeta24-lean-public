# E442 — Compiler les règles lues en E441 : déplacement exact par la fraction de cellule, seuil de montée des cellules de rencontre, poids premier signé d'un bloc sans hypothèse de contact

Pré-enregistrement (2026-11-07), avant toute compilation. Suite directe d'E441 (§19.60) sous l'ordre « poursuis le
plus possible ». Interdiction spectrale en vigueur (§19.55) ; ordre de travail §19.53.

## Vérification des neuf erreurs
1. Aucune hypothèse nouvelle : la seule hypothèse ponctuelle (« aucun contact ne tombe sur un entier ») est du même
   type que « aucune rencontre n'est un contact » (E439–E441), mesurée 0 cas ambigu en E441. 2. Le compilateur
   décide. 3. Noms vérifiés par grep (`floor_add_sub_floor`, `stagePosition_contact`, `lastContactBefore_contact`,
   `lastContactBefore_of_mem_cell`, `displacement_rule`, `meetingCell_displacement_rule`, `cellLength_meeting_le`,
   `meeting_rises_of_weight_dominates`, `meeting_falls_of_length_dominates`, `weight_dominates_below_threshold`,
   `signedPrimeSum_eq_primes_in_block` libres). 4. `lake build RHV6Fresh` après tout changement. 5. Aucun premier ni
   OFF testé. 6. Aucune position radiale. 7. Aucune famille. 8. Module isolé. 9. Intervalles = restes partiels.

## Énoncés visés (module isolé `Terminal/ExactDisplacementAndThreshold.lean`, importe `MeetingSignedSeries`)
- D1 `floor_add_sub_floor` : `⌊a + d⌋ − ⌊a⌋ = ⌊d⌋ + [fract a + fract d ≥ 1]` (arithmétique des parties entières).
- D2 `displacement_rule` (R1) : `lastContactBefore y − lastContactBefore x = ⌊T log(y/x)/π⌋ + [cellFraction x +
  fract(T log(y/x)/π) ≥ 1]` ; `meetingCell_displacement_rule` : la même chose entre deux rencontres consécutives.
- D3 `stagePosition_contact`, `lastContactBefore_contact` : la position d'étage d'un contact est son indice.
- D4 `lastContactBefore_of_mem_cell` : un entier de `Ioc ⌊C_k⌋₊ ⌊C_{k+1}⌋₊`, s'il n'est pas le contact `C_{k+1}`, a
  pour dernier contact `k`.
- D5 `signedPrimeSum_eq_primes_in_block` (cas général d'E441) : le poids premier signé d'un bloc de `M` cellules
  est la somme sur les premiers du bloc de `(−1)^{cellule(q) − a}·log q`, sans hypothèse de contact par écart
  (hypothèse ponctuelle : aucun contact du bloc n'est un entier).
- D6 `cellLength_meeting_le`, `meeting_rises_of_weight_dominates` (R4 sûre-zone basse) : si `p(r − 1) ≤ log p`, la
  cellule de rencontre monte ; `meeting_falls_of_length_dominates` (R4 sûre-zone haute) : si `log p + poids non
  premiers < p(1 − 1/r)`, elle descend.
- D7 `weight_dominates_below_threshold` : si `x(r − 1) ≤ log x` et `1/(r − 1) ≤ p ≤ x`, alors `p(r − 1) ≤ log p`
  (le seuil `x*` sépare bien : tout ce qui est en dessous monte).

## Protocole et critères
Sonde non versionnée, deux tentatives au plus pour le module définitif, journaux, `#print axioms`, build complet.
A : contradiction ; B : tout compile ; C : échec en deux tentatives. Attendu : B. Aucune expérience chiffrée
nouvelle : les règles ont été mesurées en E441 (0 violation), E442 les compile.
