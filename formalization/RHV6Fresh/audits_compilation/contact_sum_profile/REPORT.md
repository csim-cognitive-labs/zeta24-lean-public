# Audit de compilation — Terminal/ContactSumProfile.lean (§19.33, 2026-11-02)

Module isolé, non ajouté à `RHV6Fresh.lean`. Import unique : `Terminal/AmplitudeContact` (lui-même isolé).
Douze déclarations : `memberProfile`, `memberProfile_lower`, `memberProfile_norm_le`, `contactSumProfile`,
`contactSumProfile_lower`, `contactSumProfile_eq`, `contactSumProfile_meetingPoint`, `PrimeGapInterval.next`,
`PrimeGapInterval.next_lower`, `contactSumProfile_next_at_meeting`, `contactSumProfile_continuation`,
`contactSumProfile_two_gaps`. Aucun `sorry`, aucun axiome, aucune hypothèse nommée.

## Tentatives (règle : deux tentatives de preuve au plus, toutes journalisées)
1. Tentative 1 (`build_attempt1_extract.txt`) : échec, une seule erreur, identifiant `tsum_sub` inconnu
   (la forme Mathlib est `Summable.tsum_sub`), but non résolu dans `contactSumProfile_eq`. Toutes les autres
   déclarations passent.
2. Tentative 2 (`build_attempt2_extract.txt`) : `(…summable hx).tsum_sub (…)`. Succès, 9 107 tâches.
3. Deux passes cosmétiques ensuite (retour à la ligne des commentaires au-delà de cent caractères) : aucun changement
   de preuve ; dernière compilation sans avertissement (`Built RHV6Fresh.Terminal.ContactSumProfile (7.6s)`).

## Axiomes (`axioms.txt`, sonde hors build `lake env lean`)
Les cinq théorèmes sondés dépendent de `[propext, Classical.choice, Quot.sound]` seulement.

## Dépendances utilisées (toutes des théorèmes existants)
`nontrivial_zero_residue_series_summable` (RHV3Lean), `smoothedRemainder_eq_tsum_residueTerm`,
`norm_residueTerm_eq`, `PrimeGapInterval.one_lt_lower`, `one_lt_meetingPoint`, `localArithmeticTarget`
(définition), `meetingPoint` (définition = `I.upper`).

## Portée (R12)
Tout est sur l'axe réel : vrais écarts (`PrimeGapInterval`), point de rencontre `meetingPoint I = p_{n+1}`, dépôts
lissés ; aucune projection. Le canal brut (fonction en escalier) n'est pas compilé.
