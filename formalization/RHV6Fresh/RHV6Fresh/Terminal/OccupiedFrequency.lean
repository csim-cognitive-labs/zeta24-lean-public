/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CoupleLock

/-!
# La fréquence est déjà occupée : le signal ON prend la place (auteur, 2026-10-16)

Point méthodologique de l'auteur, mot pour mot : « Tu dois raisonner dans le sens : premiers et signaux déjà définis par des
signaux immuables. Point de rencontre avec `β = 1/2` et hauteur `T` attendue du zéro : DÉJÀ PRIS par les zéros ON. Impossible de
définir des zéros OFF avec exactement ces fréquences (donc ces hauteurs) puisque, lorsque ces hauteurs sont rencontrées par les
signaux des écarts des premiers, ils SONT sur l'axe critique ; donc cette fréquence ou hauteur EST DÉJÀ OCCUPÉE. On ne peut
définir qu'en dessous, avec `β < 1/2`, puisque `β > 1/2` est déjà exclu. »

Sens unique : écarts exacts ⟶ fréquences engendrées ⟶ point de rencontre de chacune ⟶ position du zéro. Rien ne part d'un
zéro supposé vers ses effets.

Ce module écrit ce point sur la Tour normalisée projetée sur l'axe algébrique, avec le verrou du couple (`Terminal/CoupleLock.lean`) :

1. **fréquence occupée** (`FrequencyOccupied T`) : un signal ON existe à la hauteur `T` ; ses rencontres sont exactement les
   positions de la ligne à cette hauteur (`occupied_signal_meeting_points`) ;
2. **un seul signal par fréquence** (`OneSignalPerFrequency`) : à fréquence égale, deux signaux partagent leur point de
   rencontre d'indice `0` (les écarts des premiers imposent, à chaque fréquence, les points de passage obligés) ; avec le verrou
   du couple, tout zéro d'une fréquence occupée est alors sur la ligne (`onLine_of_occupied`) et aucun OFF ne se définit à une
   fréquence occupée (`no_off_at_occupied_frequency`) ; la fréquence d'un OFF est donc non occupée
   (`off_frequency_unoccupied`) ;
3. **le côté haut est exclu par son miroir** : tout zéro au-dessus d'une demi a, à sa fréquence, un zéro en dessous
   (`upper_has_lower_at_same_frequency`) ; le seul candidat OFF est en dessous d'une demi (`only_low_candidate`) ;
4. **fréquence prise** (`FrequencyTaken w`) : la fréquence de `w` est occupée par un signal ON dont `w` partage le point de
   rencontre ; ⟺ `w` sur la ligne (`frequencyTaken_iff_onLine`) ; un signal d'amplitude strictement décroissante est exclu dès
   que sa fréquence est prise (`frequencyTaken_closes`) ;
5. force des lois : un seul signal par fréquence ⟺ RH (`oneSignalPerFrequency_iff_riemannHypothesis`) ; toute fréquence prise
   ⟺ RH (`frequencyTaken_law_iff_riemannHypothesis`) ; fréquences des zéros toutes occupées ∧ un seul signal par fréquence ⟹ RH
   (`riemannHypothesis_of_occupied_and_one_signal`).

Portée : (1), (3) et les caractérisations de (2), (4) sont vraies pour toute position radiale ; (5) montre que les lois
quantifiées ont la force de RH. Ce qui reste à écrire, du côté des premiers : que les signaux des écarts exacts n'engendrent
aucune fréquence dont le point de rencontre serait en dessous d'une demi, c'est-à-dire que la fréquence du zéro suivant est
prise par le signal ON de la courbe des premiers (but de la chaîne, `off_signal_amplitude_incompatible`).
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Fréquence occupée -/

/-- **Fréquence occupée** : un signal sur la ligne existe à la hauteur `T`. -/
def FrequencyOccupied (T : ℝ) : Prop :=
  ∃ z : TrueZero, rZeroHeight z.1 = T ∧ rZeroRadialPosition z.1 = 1 / 2

theorem frequencyOccupied_of_onLine (z : TrueZero) (hz : rZeroRadialPosition z.1 = 1 / 2) :
    FrequencyOccupied (rZeroHeight z.1) :=
  ⟨z, rfl, hz⟩

/-- Le signal ON d'une fréquence occupée a ses rencontres exactement aux positions de la ligne à cette hauteur. -/
theorem occupied_signal_meeting_points (T : ℝ) (h : FrequencyOccupied T) :
    ∃ z : TrueZero, rZeroHeight z.1 = T ∧ rZeroRadialPosition z.1 = 1 / 2 ∧
      ∀ k : ℤ, contactMinusAt z k = lineContact T k := by
  obtain ⟨z, hT, hz⟩ := h
  refine ⟨z, hT, hz, fun k => ?_⟩
  rw [contact_eq_line_mul_radial, (radialFactor_eq_one_iff z).mpr hz, mul_one, hT]

/-! ## 2. Un seul signal par fréquence -/

/-- **Un seul signal par fréquence** : à fréquence égale, deux signaux partagent leur point de rencontre d'indice `0`
(les écarts des premiers imposent, à chaque fréquence, les points de passage obligés). -/
def OneSignalPerFrequency : Prop :=
  ∀ z w : TrueZero, rZeroHeight z.1 = rZeroHeight w.1 → contactMinusAt w 0 = contactMinusAt z 0

/-- **Fréquence occupée ⟹ sur la ligne**, sous un seul signal par fréquence (verrou du couple : une rencontre commune à
fréquence égale fixe `β`). -/
theorem onLine_of_occupied (hOne : OneSignalPerFrequency) (w : TrueZero)
    (h : FrequencyOccupied (rZeroHeight w.1)) : rZeroRadialPosition w.1 = 1 / 2 := by
  obtain ⟨z, hT, hz⟩ := h
  rw [radial_of_meeting_point z w hT 0 (hOne z w hT), hz]

/-- **Aucun OFF à une fréquence occupée.** -/
theorem no_off_at_occupied_frequency (hOne : OneSignalPerFrequency) (w : TrueZero)
    (h : FrequencyOccupied (rZeroHeight w.1)) (hBelow : rZeroRadialPosition w.1 < 1 / 2) : False := by
  have := onLine_of_occupied hOne w h
  linarith

/-- **La fréquence d'un OFF n'est pas occupée** (sous un seul signal par fréquence). -/
theorem off_frequency_unoccupied (hOne : OneSignalPerFrequency) (w : TrueZero)
    (hBelow : rZeroRadialPosition w.1 < 1 / 2) : ¬ FrequencyOccupied (rZeroHeight w.1) :=
  fun h => no_off_at_occupied_frequency hOne w h hBelow

/-! ## 3. Le côté haut est exclu par son miroir : seul candidat en dessous -/

/-- Tout zéro au-dessus d'une demi a, à sa fréquence, un zéro en dessous (son miroir). -/
theorem upper_has_lower_at_same_frequency (w : TrueZero) (h : 1 / 2 < rZeroRadialPosition w.1) :
    ∃ v : TrueZero, rZeroHeight v.1 = rZeroHeight w.1 ∧ rZeroRadialPosition v.1 < 1 / 2 :=
  ⟨mirrorMember w, mirrorMember_ordinate w, by rw [mirrorMember_radial]; linarith⟩

/-- **Seul candidat OFF : en dessous d'une demi.** Si aucun zéro n'est en dessous, tout zéro est sur la ligne. -/
theorem only_low_candidate (h : ∀ v : TrueZero, ¬ rZeroRadialPosition v.1 < 1 / 2) (w : TrueZero) :
    rZeroRadialPosition w.1 = 1 / 2 := by
  rcases lt_trichotomy (rZeroRadialPosition w.1) (1 / 2) with hlt | heq | hgt
  · exact absurd hlt (h w)
  · exact heq
  · obtain ⟨v, _, hv⟩ := upper_has_lower_at_same_frequency w hgt
    exact absurd hv (h v)

/-! ## 4. Fréquence prise -/

/-- **Fréquence prise** : la fréquence de `w` est occupée par un signal ON dont `w` partage le point de rencontre. -/
def FrequencyTaken (w : TrueZero) : Prop :=
  ∃ z : TrueZero, rZeroHeight z.1 = rZeroHeight w.1 ∧ rZeroRadialPosition z.1 = 1 / 2 ∧
    contactMinusAt w 0 = contactMinusAt z 0

theorem onLine_of_frequencyTaken (w : TrueZero) (h : FrequencyTaken w) :
    rZeroRadialPosition w.1 = 1 / 2 := by
  obtain ⟨z, hT, hz, hC⟩ := h
  rw [radial_of_meeting_point z w hT 0 hC, hz]

/-- **Fréquence prise ⟺ sur la ligne** (caractérisation). -/
theorem frequencyTaken_iff_onLine (w : TrueZero) :
    FrequencyTaken w ↔ rZeroRadialPosition w.1 = 1 / 2 :=
  ⟨onLine_of_frequencyTaken w, fun h => ⟨w, rfl, h, rfl⟩⟩

/-- **Fermeture par la fréquence prise** : un signal d'amplitude strictement décroissante le long des premiers est exclu dès
que sa fréquence est prise par un signal ON dont il partage le point de rencontre. -/
theorem frequencyTaken_closes (w : TrueZero)
    (hDecr : ∀ x y : ℝ, 1 ≤ x → x < y → pairAmplitude w y < pairAmplitude w x)
    (hTaken : ∃ z : TrueZero, rZeroHeight z.1 = rZeroHeight w.1 ∧ rZeroRadialPosition z.1 = 1 / 2 ∧
      contactMinusAt w 0 = contactMinusAt z 0) : False :=
  decreasing_breaks_constantNeed w hDecr (constantNeed_of_onLine w (onLine_of_frequencyTaken w hTaken))

/-! ## 5. Force des lois -/

/-- **Un seul signal par fréquence ⟺ RH.** -/
theorem oneSignalPerFrequency_iff_riemannHypothesis : OneSignalPerFrequency ↔ RiemannHypothesis := by
  constructor
  · intro hOne
    refine riemannHypothesis_iff_noLowerSide.mpr (fun w hlt => ?_)
    -- le miroir de `w` est à la même fréquence ; une rencontre commune fixe `β_w = 1 − β_w`
    have h := radial_of_meeting_point (mirrorMember w) w (mirrorMember_ordinate w) 0
      (hOne (mirrorMember w) w (mirrorMember_ordinate w))
    rw [mirrorMember_radial] at h
    linarith
  · intro hRH z w hT
    have hz := thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1
    have hw := thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1
    rw [contact_eq_line_mul_radial, contact_eq_line_mul_radial, (radialFactor_eq_one_iff z).mpr hz,
      (radialFactor_eq_one_iff w).mpr hw, hT]

/-- **Toute fréquence prise ⟺ RH.** -/
theorem frequencyTaken_law_iff_riemannHypothesis : (∀ w : TrueZero, FrequencyTaken w) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_iff_noLowerSide.mpr
      (fun w hlt => by rw [onLine_of_frequencyTaken w (h w)] at hlt; linarith)
  · intro hRH w
    exact (frequencyTaken_iff_onLine w).mpr (thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1)

/-- **Fréquences des zéros toutes occupées ∧ un seul signal par fréquence ⟹ RH.** -/
theorem riemannHypothesis_of_occupied_and_one_signal (hOne : OneSignalPerFrequency)
    (hOcc : ∀ w : TrueZero, FrequencyOccupied (rZeroHeight w.1)) : RiemannHypothesis :=
  riemannHypothesis_iff_noLowerSide.mpr (fun w hlt => no_off_at_occupied_frequency hOne w (hOcc w) hlt)

#print axioms occupied_signal_meeting_points
#print axioms onLine_of_occupied
#print axioms only_low_candidate
#print axioms frequencyTaken_closes
#print axioms oneSignalPerFrequency_iff_riemannHypothesis
#print axioms riemannHypothesis_of_occupied_and_one_signal

end RHV6Fresh
