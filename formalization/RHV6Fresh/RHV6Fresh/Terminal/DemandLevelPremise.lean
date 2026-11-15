/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RemainderRegime

/-!
# La prémisse unique lue en niveau (module isolé, non importé par la chaîne)

Solution 3 du maître §16.7 (auteur, validée le 2026-10-29). Objet : relier, par le seul compilé,
l'hypothèse de clôture nommée (« le niveau de la demande des premiers est borné aux rencontres ») à la
prémisse unique de la chaîne (`ExpectedFrequencyRises` : la fréquence attendue monte à chaque passage),
sans modifier la chaîne et sans remplacement conditionnel.

Ce qui est compilé ici :

1. **Lecture en niveau, en tout point.** La prémisse unique de la chaîne équivaut à « le niveau relatif de
   la demande est borné en tout point au-delà de un » (`expectedFrequencyRises_iff_demandBoundedEverywhere`).
   Les deux lectures de l'inconnue — en fréquence (chaîne) et en niveau (premiers seuls) — sont le même
   énoncé.
2. **Lecture aux rencontres, avec le Reste 1.** La prémisse unique équivaut à la conjonction de l'hypothèse
   de clôture (demande bornée aux rencontres) et de « le reste n'est jamais à droite » : pour tout membre,
   aucun zéro hors de son couple n'est strictement à droite de un demi
   (`expectedFrequencyRises_iff_meetings_and_restNeverRight`). La seconde moitié est exactement ce que le
   maître appelle le Reste 1 : ce qu'une infinité de zéros à droite paie aux rencontres.
3. **Le pont des rencontres, nommé.** Si la demande bornée aux rencontres entraîne la demande bornée en tout
   point (`MeetingsBridge`, hypothèse nommée, objet de la Solution 1), alors l'hypothèse de clôture seule
   équivaut à la prémisse unique (`expectedFrequencyRises_iff_meetings_of_bridge`).

Aucune hypothèse n'est posée comme démontrée : `DemandBoundedAtMeetings`, `RestNeverRight`,
`MeetingsBridge` sont des `def ... : Prop`, jamais des théorèmes. Aucun axiome, aucun `sorry`.
-/

namespace RHV6Fresh

open Complex RHV3Lean

/-! ## 1. Les énoncés nommés -/

/-- **Hypothèse de clôture (nommée, jamais posée)** : le niveau relatif de la demande des premiers est
borné aux rencontres. -/
def DemandBoundedAtMeetings : Prop :=
  ∃ C : ℝ, ∀ I : PrimeGapInterval, demandRelativeLevel (meetingPoint I) ≤ C

/-- Le niveau relatif de la demande est borné en tout point au-delà de un. -/
def DemandBoundedEverywhere : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 1 < x → demandRelativeLevel x ≤ C

/-- **Reste 1, nommé** : pour tout membre, aucun zéro hors de son couple n'est strictement à droite de un
demi. -/
def RestNeverRight : Prop := ∀ l : TrueZero, RestNotRight l

/-- **Le pont des rencontres (nommé, objet de la Solution 1)** : la demande bornée aux rencontres entraîne
la demande bornée en tout point. -/
def MeetingsBridge : Prop := DemandBoundedAtMeetings → DemandBoundedEverywhere

/-! ## 2. Niveau borné en tout point = croissance en racine -/

theorem demandRelativeLevel_le_iff {x C : ℝ} (hx : 0 < x) :
    demandRelativeLevel x ≤ C ↔ ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ) := by
  unfold demandRelativeLevel
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hx _)]

theorem demandBoundedEverywhere_iff_sqrt_growth :
    DemandBoundedEverywhere ↔
      ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun x hx => (demandRelativeLevel_le_iff (by linarith)).mp (hC x hx)⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun x hx => (demandRelativeLevel_le_iff (by linarith)).mpr (hC x hx)⟩

/-- Le niveau borné en tout point donne RH (`riemannHypothesis_of_remainder_sqrt_growth`). -/
theorem riemannHypothesis_of_demandBoundedEverywhere (h : DemandBoundedEverywhere) :
    RiemannHypothesis :=
  riemannHypothesis_of_remainder_sqrt_growth (demandBoundedEverywhere_iff_sqrt_growth.mp h)

/-- Sous RH, le niveau est borné en tout point (`remainder_sqrt_growth_of_riemannHypothesis`). -/
theorem demandBoundedEverywhere_of_riemannHypothesis (h : RiemannHypothesis) :
    DemandBoundedEverywhere :=
  demandBoundedEverywhere_iff_sqrt_growth.mpr (remainder_sqrt_growth_of_riemannHypothesis h)

/-! ## 3. La prémisse unique de la chaîne, lue en niveau -/

/-- **Le niveau borné en tout point entraîne la prémisse unique de la chaîne.** -/
theorem expectedFrequencyRises_of_demandBoundedEverywhere (h : DemandBoundedEverywhere) :
    ExpectedFrequencyRises :=
  expectedFrequencyRises_iff_riemannHypothesis.mpr (riemannHypothesis_of_demandBoundedEverywhere h)

/-- **La prémisse unique de la chaîne entraîne le niveau borné en tout point.** -/
theorem demandBoundedEverywhere_of_expectedFrequencyRises (h : ExpectedFrequencyRises) :
    DemandBoundedEverywhere :=
  demandBoundedEverywhere_of_riemannHypothesis (riemannHypothesis_terminal h)

/-- **Unicité du blocage, compilée** : la prémisse unique (fréquence) et le niveau borné (premiers seuls)
sont le même énoncé. -/
theorem expectedFrequencyRises_iff_demandBoundedEverywhere :
    ExpectedFrequencyRises ↔ DemandBoundedEverywhere :=
  ⟨demandBoundedEverywhere_of_expectedFrequencyRises, expectedFrequencyRises_of_demandBoundedEverywhere⟩

/-! ## 4. Aux rencontres -/

/-- Borné en tout point donne borné aux rencontres (les rencontres sont des points au-delà de un). -/
theorem demandBoundedAtMeetings_of_everywhere (h : DemandBoundedEverywhere) :
    DemandBoundedAtMeetings := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun I => hC _ (one_lt_meetingPoint I)⟩

/-- La prémisse unique entraîne l'hypothèse de clôture : celle-ci n'est pas plus forte que la cible. -/
theorem demandBoundedAtMeetings_of_expectedFrequencyRises (h : ExpectedFrequencyRises) :
    DemandBoundedAtMeetings :=
  demandBoundedAtMeetings_of_everywhere (demandBoundedEverywhere_of_expectedFrequencyRises h)

/-- Sous RH, l'hypothèse de clôture est vraie. -/
theorem demandBoundedAtMeetings_of_riemannHypothesis (h : RiemannHypothesis) :
    DemandBoundedAtMeetings :=
  demandBoundedAtMeetings_of_everywhere (demandBoundedEverywhere_of_riemannHypothesis h)

/-- Sous RH, le reste n'est jamais à droite (tout indice est sur la ligne). -/
theorem restNeverRight_of_riemannHypothesis (h : RiemannHypothesis) : RestNeverRight := by
  intro l ρ _
  have hre : (ρ : ℂ).re = 1 / 2 := h (ρ : ℂ) ρ.property.1 ρ.property.2.1 ρ.property.2.2
  exact hre.le

/-- **Hypothèse de clôture + Reste 1 donnent RH** : par `not_low_of_bounded_demand_and_restNotRight`
(RemainderRegime) et `riemannHypothesis_of_noLowerSide`. -/
theorem riemannHypothesis_of_meetings_and_restNeverRight (hdem : DemandBoundedAtMeetings)
    (hrest : RestNeverRight) : RiemannHypothesis :=
  riemannHypothesis_of_noLowerSide fun l => not_low_of_bounded_demand_and_restNotRight l hdem (hrest l)

/-- **Hypothèse de clôture + Reste 1 donnent la prémisse unique de la chaîne.** -/
theorem expectedFrequencyRises_of_meetings_and_restNeverRight (hdem : DemandBoundedAtMeetings)
    (hrest : RestNeverRight) : ExpectedFrequencyRises :=
  expectedFrequencyRises_iff_riemannHypothesis.mpr
    (riemannHypothesis_of_meetings_and_restNeverRight hdem hrest)

/-- **Lecture aux rencontres, exacte** : la prémisse unique équivaut à « hypothèse de clôture et Reste 1 ».
Ce qui sépare l'hypothèse de clôture seule de la cible est exactement le Reste 1. -/
theorem expectedFrequencyRises_iff_meetings_and_restNeverRight :
    ExpectedFrequencyRises ↔ (DemandBoundedAtMeetings ∧ RestNeverRight) :=
  ⟨fun h => ⟨demandBoundedAtMeetings_of_expectedFrequencyRises h,
      restNeverRight_of_riemannHypothesis (riemannHypothesis_terminal h)⟩,
    fun ⟨hdem, hrest⟩ => expectedFrequencyRises_of_meetings_and_restNeverRight hdem hrest⟩

/-- Variante avec le reste lu en amplitude (TotalityPays) : reste borné aux rencontres pour tout membre. -/
def RestBoundedAtMeetings : Prop :=
  ∀ l : TrueZero, ∃ C' : ℝ, ∀ I : PrimeGapInterval, restRelativeAmplitude l (meetingPoint I) ≤ C'

theorem riemannHypothesis_of_meetings_and_restBounded (hdem : DemandBoundedAtMeetings)
    (hrest : RestBoundedAtMeetings) : RiemannHypothesis :=
  riemannHypothesis_of_noLowerSide fun l => not_low_of_bounded_demand_and_rest l hdem (hrest l)

theorem restBoundedAtMeetings_of_restNeverRight (h : RestNeverRight) : RestBoundedAtMeetings :=
  fun l => ⟨totalLineWeight, fun I => restRelativeAmplitude_le_total l (h l) (one_lt_meetingPoint I)⟩

/-! ## 5. Sous le pont des rencontres, l'hypothèse de clôture seule est la prémisse -/

/-- **Sous le pont nommé**, l'hypothèse de clôture équivaut à la prémisse unique de la chaîne. -/
theorem expectedFrequencyRises_iff_meetings_of_bridge (hB : MeetingsBridge) :
    ExpectedFrequencyRises ↔ DemandBoundedAtMeetings :=
  ⟨demandBoundedAtMeetings_of_expectedFrequencyRises,
    fun h => expectedFrequencyRises_of_demandBoundedEverywhere (hB h)⟩

/-- Sous le pont nommé, l'hypothèse de clôture donne RH. -/
theorem riemannHypothesis_of_meetings_of_bridge (hB : MeetingsBridge) (h : DemandBoundedAtMeetings) :
    RiemannHypothesis :=
  riemannHypothesis_of_demandBoundedEverywhere (hB h)

/-- Le pont est vrai sous RH (les deux côtés le sont) : il n'est pas plus fort que la cible. -/
theorem meetingsBridge_of_riemannHypothesis (h : RiemannHypothesis) : MeetingsBridge :=
  fun _ => demandBoundedEverywhere_of_riemannHypothesis h

/-- **Le pont équivaut au Reste 1 sous l'hypothèse de clôture** : si la demande est bornée aux rencontres,
alors « borné en tout point » et « le reste n'est jamais à droite » se valent. -/
theorem everywhere_iff_restNeverRight_of_meetings (hdem : DemandBoundedAtMeetings) :
    DemandBoundedEverywhere ↔ RestNeverRight :=
  ⟨fun h => restNeverRight_of_riemannHypothesis (riemannHypothesis_of_demandBoundedEverywhere h),
    fun h => demandBoundedEverywhere_of_riemannHypothesis
      (riemannHypothesis_of_meetings_and_restNeverRight hdem h)⟩

end RHV6Fresh
