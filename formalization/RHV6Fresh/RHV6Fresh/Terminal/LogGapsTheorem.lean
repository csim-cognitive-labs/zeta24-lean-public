/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RightSetDichotomy
import RHV6Fresh.PNTPort.Consequences

/-!
# Les écarts logarithmiques tendent vers zéro : THÉORÈME (module isolé)

Fermeture de la décision 1 du maître §17.6. Le théorème externe `chebyshev_asymptotic` (projet
PrimeNumberTheoremAnd, porté dans `RHV6Fresh/PNTPort/`, voir `PROVENANCE.md`) est reçu par
`chebyshevAsymptotic_of_isEquivalent` : l'hypothèse nommée `ChebyshevAsymptotic` devient un théorème, et avec
elle `LogGapsVanish` et `MeetingsSampleFrequencies`. Le chemin des zéros ne dépend plus que de l'hypothèse
de clôture et du sommet atteint ; la dichotomie ne dépend plus que de l'hypothèse de clôture.

Aucun axiome au-delà des axiomes standard, aucun `sorry`. La chaîne est intacte.
-/

namespace RHV6Fresh

open Complex RHV3Lean Filter Topology

/-- **Théorème** : l'asymptotique de Tchebychev. -/
theorem chebyshevAsymptotic_holds : ChebyshevAsymptotic :=
  chebyshevAsymptotic_of_isEquivalent chebyshev_asymptotic

/-- **Théorème** : les écarts logarithmiques entre premiers consécutifs tendent vers zéro. -/
theorem logGapsVanish_holds : LogGapsVanish :=
  logGapsVanish_of_chebyshevAsymptotic chebyshevAsymptotic_holds

/-- **Théorème** : les rencontres échantillonnent les fréquences. L'hypothèse nommée de
`MeetingSampling.lean` n'est plus une hypothèse. -/
theorem meetingsSampleFrequencies_holds : MeetingsSampleFrequencies :=
  meetingsSampleFrequencies_of_logGaps logGapsVanish_holds

/-- **Chemin des zéros, sans hypothèse arithmétique** : hypothèse de clôture et sommet atteint donnent RH. -/
theorem riemannHypothesis_of_closure_summit (hdem : DemandBoundedAtMeetings) (hsum : SummitAttained) :
    RiemannHypothesis :=
  riemannHypothesis_of_summitAttained meetingsSampleFrequencies_holds hdem hsum

/-- Sous l'hypothèse de clôture seule : RH, ou bien une infinité d'indices à droite dont le sommet n'est
pas atteint. -/
theorem riemannHypothesis_or_infinite_not_summit_of_closure (hdem : DemandBoundedAtMeetings) :
    RiemannHypothesis ∨
      (Set.Infinite {ρ : ExplicitIndex | 1 / 2 < (ρ : ℂ).re} ∧ ¬ SummitAttained) :=
  riemannHypothesis_or_infinite_not_summit meetingsSampleFrequencies_holds hdem

/-- Sous l'hypothèse de clôture seule, un ensemble droit fini est vide. -/
theorem riemannHypothesis_of_closure_finite_right (hdem : DemandBoundedAtMeetings)
    (hfin : {ρ : ExplicitIndex | 1 / 2 < (ρ : ℂ).re}.Finite) : RiemannHypothesis :=
  riemannHypothesis_of_finite_right meetingsSampleFrequencies_holds hdem hfin

/-- Le Reste 1 (« le reste n'est jamais à droite ») sous clôture et sommet atteint, sans autre hypothèse. -/
theorem restNeverRight_of_closure_summit (hdem : DemandBoundedAtMeetings) (hsum : SummitAttained) :
    RestNeverRight :=
  restNeverRight_of_summitAttained meetingsSampleFrequencies_holds hdem hsum

end RHV6Fresh
