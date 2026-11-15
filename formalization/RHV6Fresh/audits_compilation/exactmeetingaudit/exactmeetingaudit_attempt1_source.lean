/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.OffCarrier
import RHV6Fresh.Terminal.MeetingExactness
import RHV6Fresh.Terminal.DemandLevelPremise
import RHV6Fresh.Terminal.ConstantAmplitudeNeed

/-!
# Audit de la rencontre exacte sur le porteur OFF (module isolé, non importé par la chaîne, 2026-10-31)

Étape B du plan pré-enregistré au maître §19.21.6, complétée par §19.22.4 (B7, B8). Feu vert de l'auteur le 2026-10-31.
Huit énoncés, tous instances ou compositions de théorèmes existants, **aucune hypothèse nouvelle, aucune définition
nouvelle** : chaque énoncé est écrit sur l'objet même que la doctrine P1–P5 et les trois textes de l'auteur visent,
le porteur OFF canonique `C : OffCarrier` (premier changement de régime), son zéro `C.zero`, son écart `C.gap` et la
rencontre `meetingPoint C.gap = p_{n+1}`.

* **B1** `carrier_meeting_exact` : la rencontre de l'écart du porteur est exacte (réciproque de P4 sur le porteur).
* **B2** `carrier_total_eq_pair_add_rest`, `carrier_target_split_mirror` : « total = paire + reste » est une identité,
  pour le porteur comme pour tous (P2).
* **B3** `no_carrier_iff_riemannHypothesis` : « tout porteur est contradictoire » ⟺ RH (P5 nommée, non prouvée).
* **B4** `constantRelativeAmplitude_law_iff_riemannHypothesis`, `carrier_zero_not_constantRelativeAmplitude`,
  `carrier_mirror_not_constantRelativeAmplitude` : la relation supplémentaire de P2 (constance par membre entre
  rencontres) équivaut à RH, et échoue exactement pour l'arrivée basse et son miroir.
* **B5** `panel_two_hypotheses_iff_riemannHypothesis`, `carrier_contradiction_under_panel_two` : le schéma du
  panneau 2 du graphique est un théorème conditionnel dont les hypothèses réunies équivalent à RH.
* **B6** `carrier_rest_unbounded_of_bounded_demand` : aucune borne compilée sur le reste ; sous l'hypothèse nommée
  de demande bornée aux rencontres, le reste relatif du porteur dépasse toute borne à une rencontre.
* **B7** `carrier_no_last_contributor`, `carrier_tail_not_eventually_zero`, `carrier_rest_not_eventually_zero` :
  pas de dernier contributeur sur le porteur ; la queue, et en particulier le reste hors paire, n'est jamais
  identiquement nulle au voisinage de la rencontre du porteur.
* **B8** `carrier_share_eq_target_sub_others`, `carrier_mirror_share_eq_target_sub_others` : la part du membre OFF
  (et de son miroir) sur l'écart du porteur égale cible moins les autres : identité du complément, aucune
  détermination radiale.

Aucun `sorry`, aucun `admit`, aucun axiome. Ce module n'est pas importé par `RHV6Fresh.lean`.
-/

namespace RHV6Fresh

open RHV3Lean Filter Topology

namespace OffCarrier

variable (C : OffCarrier)

/-! ## B1. La rencontre de l'écart du porteur est exacte -/

/-- **B1.** La rencontre de l'écart du porteur OFF est le premier `p_{n+1}` (premier partagé du raccord sortant), et
la demande de cet écart est accomplie par la totalité des zéros, le porteur compris : instance de
`localSynchronization` sur `C.gap`. Aucune hypothèse radiale. -/
theorem carrier_meeting_exact :
    meetingPoint C.gap = fnPrimeAtRank (C.n + 1) ∧
    localArithmeticTarget C.gap = ∑' ρ : ExplicitIndex, smoothedLocalContribution ρ C.gap :=
  ⟨rfl, localSynchronization C.gap⟩

/-- **B1 bis.** À la rencontre du porteur, aucune famille finie n'accomplit la demande sur un voisinage et la
synchronisation tient : `exactness_is_a_demand` sur `C.gap`. -/
theorem carrier_exactness_is_a_demand :
    localArithmeticTarget C.gap = ∑' ρ : ExplicitIndex, smoothedLocalContribution ρ C.gap ∧
    ∀ s : Finset ExplicitIndex,
      ¬ (∀ᶠ x in 𝓝 (meetingPoint C.gap),
          smoothedRemainder x = ∑ ρ ∈ s, nontrivialZeroResidueTerm x ρ) :=
  exactness_is_a_demand C.gap

/-! ## B2. Total = paire + reste, identité -/

/-- **B2.** À la rencontre du porteur, la demande des premiers est la part conjointe du couple (zéro OFF et miroir)
plus la somme de toutes les autres parts. Identité, pas contrainte. -/
theorem carrier_total_eq_pair_add_rest :
    smoothedRemainder (meetingPoint C.gap) =
      pairJoint C.zero (meetingPoint C.gap) + restOfPair C.zero (meetingPoint C.gap) :=
  remainder_eq_pair_add_rest C.zero C.low (one_lt_meetingPoint C.gap)

/-- **B2 bis, cas (a).** Sur l'écart du porteur, la cible lissée est la paire lissée plus la paire conjuguée plus les
autres fréquences : le reste est « cible moins paquet de la fréquence », par définition. -/
theorem carrier_target_split_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    localArithmeticTarget C.gap =
      C.smoothedPair C.gap + C.smoothedConjPair C.gap + C.otherFrequenciesContribution C.gap :=
  C.target_split_of_mirror h C.gap

end OffCarrier

/-! ## B3. P5 restreinte au porteur ⟺ RH -/

/-- **B3.** « Tout porteur OFF est contradictoire » équivaut à RH. P5 est une cible nommée, fermée comme cible, non
prouvée : la prouver pour tout porteur, c'est prouver RH. -/
theorem no_carrier_iff_riemannHypothesis : (∀ C : OffCarrier, False) ↔ RiemannHypothesis := by
  constructor
  · intro h
    by_contra hNot
    obtain ⟨C⟩ := exists_offCarrier_of_not_riemannHypothesis hNot
    exact h C
  · intro hRH C
    exact no_offCarrier_of_riemannHypothesis hRH C

/-! ## B4. La relation supplémentaire de P2 ⟺ RH -/

/-- **B4.** « La part de chaque membre est constante en amplitude relative entre rencontres » (lecture membre par
membre de la demande) équivaut à RH. Jamais posée. -/
theorem constantRelativeAmplitude_law_iff_riemannHypothesis :
    (∀ w : TrueZero, ConstantRelativeAmplitudeAtMeetings w) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_iff_noLowerSide.mpr fun z hlt =>
      absurd ((constantRelativeAmplitude_iff_onLine z).mp (h z)) (ne_of_lt hlt)
  · intro hRH w
    exact (constantRelativeAmplitude_iff_onLine w).mpr
      (thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1)

/-- **B4 bis.** La loi du besoin constant, forme de la chaîne, équivaut aussi à RH (rappel). -/
theorem constantNeed_law_iff_riemannHypothesis' :
    (∀ z : TrueZero, ConstantNeed z) ↔ RiemannHypothesis :=
  constantNeed_law_iff_riemannHypothesis

namespace OffCarrier

variable (C : OffCarrier)

/-- **B4 ter.** Pour le porteur, la relation supplémentaire échoue exactement au zéro OFF. -/
theorem carrier_zero_not_constantRelativeAmplitude : ¬ ConstantRelativeAmplitudeAtMeetings C.zero :=
  low_arrival_not_constantRelativeAmplitude C.zero C.low

/-- **B4 quater.** Et à son miroir. -/
theorem carrier_mirror_not_constantRelativeAmplitude :
    ¬ ConstantRelativeAmplitudeAtMeetings (mirrorMember C.zero) :=
  mirror_not_constantRelativeAmplitude C.zero C.low

end OffCarrier

/-! ## B5. Le schéma du panneau 2 est conditionnel, ses hypothèses réunies ⟺ RH -/

/-- **B5.** Les deux hypothèses du panneau 2 (demande bornée aux rencontres, reste jamais à droite) réunies
équivalent à RH : le « plafond » du graphique n'est pas un fait, c'est la cible. -/
theorem panel_two_hypotheses_iff_riemannHypothesis :
    (DemandBoundedAtMeetings ∧ RestNeverRight) ↔ RiemannHypothesis :=
  expectedFrequencyRises_iff_meetings_and_restNeverRight.symm.trans
    expectedFrequencyRises_iff_riemannHypothesis

namespace OffCarrier

variable (C : OffCarrier)

/-- **B5 bis.** Sous ces deux hypothèses nommées, le porteur est contradictoire : c'est exactement le schéma
« zone inaccessible » du panneau 2, avec ses hypothèses apparentes. -/
theorem carrier_contradiction_under_panel_two (hdem : DemandBoundedAtMeetings)
    (hrest : RestNotRight C.zero) : False :=
  not_low_of_bounded_demand_and_restNotRight C.zero hdem hrest C.low

/-! ## B6. Aucune borne compilée sur le reste -/

/-- **B6.** Sous l'hypothèse nommée de demande bornée aux rencontres, le reste relatif du porteur (tout sauf le
couple) dépasse toute borne à une rencontre. Inconditionnellement : ou la demande n'est pas bornée aux rencontres,
ou le reste ne l'est pas (`totality_pays_or_demand_unbounded`). Aucune borne sur le reste n'est compilée. -/
theorem carrier_rest_unbounded_of_bounded_demand (hdem : DemandBoundedAtMeetings) (c : ℝ) :
    ∃ I : PrimeGapInterval, c < restRelativeAmplitude C.zero (meetingPoint I) := by
  obtain ⟨K, hK⟩ := hdem
  exact rest_unbounded_of_bounded_demand C.zero C.low hK c

/-- **B6 bis.** Forme inconditionnelle sur le porteur. -/
theorem carrier_rest_or_demand_unbounded (c : ℝ) :
    ∃ I : PrimeGapInterval,
      c < demandRelativeLevel (meetingPoint I) + restRelativeAmplitude C.zero (meetingPoint I) :=
  totality_pays_or_demand_unbounded C.zero C.low c

/-! ## B7. Pas de dernier contributeur sur le porteur -/

/-- **B7.** Aucune famille finie de parts n'accomplit la demande sur un voisinage de la rencontre du porteur : il
n'existe pas de « dernier contributeur » qui clorait l'événement `p_{n+1}`. -/
theorem carrier_no_last_contributor (s : Finset ExplicitIndex) :
    ¬ (∀ᶠ x in 𝓝 (meetingPoint C.gap),
        smoothedRemainder x = ∑ ρ ∈ s, nontrivialZeroResidueTerm x ρ) :=
  no_finite_family_accomplishes_demand C.gap s

/-- **B7 bis.** La queue des zéros omis n'est jamais identiquement nulle au voisinage de la rencontre du porteur :
les contributions ultérieures ne sont jamais collectivement nulles sur l'événement. -/
theorem carrier_tail_not_eventually_zero (s : Finset ExplicitIndex) :
    ¬ (∀ᶠ x in 𝓝 (meetingPoint C.gap),
        ∑' ρ : ((s : Set ExplicitIndex)ᶜ : Set ExplicitIndex), nontrivialZeroResidueTerm x ρ.1 = 0) :=
  tail_not_eventually_zero C.gap s

/-- **B7 ter.** En particulier, le reste hors couple (tout sauf le zéro OFF et son miroir) n'est jamais
identiquement nul au voisinage de la rencontre du porteur : la paire n'est jamais « dernier contributeur ». -/
theorem carrier_rest_not_eventually_zero :
    ¬ (∀ᶠ x in 𝓝 (meetingPoint C.gap),
        ∑' ρ : ((pairIndices C.zero : Set ExplicitIndex)ᶜ : Set ExplicitIndex),
          nontrivialZeroResidueTerm x ρ.1 = 0) :=
  tail_not_eventually_zero C.gap (pairIndices C.zero)

/-! ## B8. La part d'un membre quelconque égale cible moins les autres -/

/-- **B8.** La part du zéro OFF sur l'écart du porteur égale l'incrément de la courbe des premiers moins
l'incrément des autres : identité du complément, vraie pour tout membre, qui ne détermine rien de radial. -/
theorem carrier_share_eq_target_sub_others :
    imposedShare C.zero C.gap =
      (smoothedRemainder (meetingPoint C.gap) - smoothedRemainder C.gap.lower) -
        (othersSum C.zero (meetingPoint C.gap) - othersSum C.zero C.gap.lower) :=
  imposedShare_eq C.zero C.gap

/-- **B8 bis.** La même identité pour le miroir, sur le même écart. -/
theorem carrier_mirror_share_eq_target_sub_others :
    imposedShare (mirrorMember C.zero) C.gap =
      (smoothedRemainder (meetingPoint C.gap) - smoothedRemainder C.gap.lower) -
        (othersSum (mirrorMember C.zero) (meetingPoint C.gap) -
          othersSum (mirrorMember C.zero) C.gap.lower) :=
  imposedShare_eq (mirrorMember C.zero) C.gap

end OffCarrier

end RHV6Fresh
