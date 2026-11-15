/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.AmplitudeStableSynchronization
import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Terminal.ReadingArithmetic

/-!
# Besoin de synchronisation constant aux points de rencontre (généralisation, auteur, 2026-10-15)

Énoncé de l'auteur, mot pour mot : « L'amplitude attendue ne change pas, seule la fréquence change entre deux zéros. Le besoin de
synchronisation reste constant à cause des points de rencontre. »

Sens unique (auteur) : les écarts immuables des premiers imposent aux zéros fréquence et amplitude ; les zéros sont les signaux qui
composent ces écarts. Ce module écrit la contrainte généralisée SANS présupposer l'amplitude recherchée : le **besoin** d'un signal est
son amplitude à l'échelle de la ligne lue à un point de rencontre (`pairAmplitude`), et la contrainte est que ce besoin soit le même
à tous les points de rencontre (`ConstantNeed`). Rien n'y fixe la valeur du besoin.

Ce qui est démontré (axiomes standard) :
1. besoin constant ⟺ le signal est celui d'un zéro sur la ligne (`constantNeed_iff_onLine`) ; à deux rencontres consécutives
   (contacts) la même caractérisation (`constantNeed_meeting_points`) ;
2. entre deux signaux à besoin constant seule la fréquence change : pas `π/T` plus court, amplitude attendue plus faible, rapport
   des amplitudes fixé par les deux hauteurs (`frequency_only_between_constant_needs`) ;
3. un signal d'amplitude strictement décroissante n'a pas un besoin constant (`decreasing_breaks_constantNeed`) ; deux points de
   rencontre où le besoin n'a pas diminué suffisent à l'exclure (`constantNeed_closes`) ;
4. la loi « tout signal a un besoin constant » ⟺ RH (`constantNeed_law_iff_riemannHypothesis`) ; forme au passage avec historique
   sur la ligne, sous l'ancre (`constantNeed_history_law_iff_riemannHypothesis`).

Portée : (1), (2), (3) sont des identités et caractérisations vraies pour toute position radiale ; (4) montre que la contrainte
généralisée, quantifiée sur tous les signaux, a la force de RH. Mesuré, non démontré (E312 T4–T5, E313 T4c, T6, T7, premiers seuls,
douze fréquences) : sur la courbe des premiers de zêta le besoin est constant à chaque fréquence (rapport 1 à deux rencontres
consécutives, pente nulle), une seule fois par fréquence, et seule la fréquence change d'un signal au suivant ; le monde témoin
(poids différents) a un besoin croissant. Ce que la chaîne demande encore : deux points de rencontre de la courbe des premiers où le
besoin du signal placé à la hauteur du zéro suivant n'a pas diminué (`off_signal_amplitude_incompatible`).
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Le besoin et sa constance -/

/-- **Besoin de synchronisation constant** : l'amplitude attendue (échelle de la ligne) est la même à tous les points de rencontre
`x ≥ 1`. Aucune valeur n'est présupposée. -/
def ConstantNeed (z : TrueZero) : Prop :=
  ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → pairAmplitude z x = pairAmplitude z y

theorem constantNeed_of_onLine (z : TrueZero) (hz : rZeroRadialPosition z.1 = 1 / 2) :
    ConstantNeed z := by
  intro x y hx hy
  rw [pairAmplitude_onLine z hz (by linarith), pairAmplitude_onLine z hz (by linarith)]

/-- Deux points de rencontre (`1` et `2`) à besoin égal placent le signal sur la ligne. -/
theorem onLine_of_need_eq_one_two (z : TrueZero)
    (h : pairAmplitude z 1 = pairAmplitude z 2) : rZeroRadialPosition z.1 = 1 / 2 := by
  rw [pairAmplitude_eq z one_pos, pairAmplitude_eq z (by norm_num : (0 : ℝ) < 2)] at h
  have hs : 0 < Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) := by
    apply Real.sqrt_pos.mpr
    have := z.2
    positivity
  have h2 : (2 : ℝ) ^ (rZeroRadialPosition z.1 - 1 / 2) = 1 := by
    rw [Real.one_rpow] at h
    have := (div_left_inj' hs.ne').mp h
    linarith
  rcases lt_trichotomy (rZeroRadialPosition z.1 - 1 / 2) 0 with hlt | heq | hgt
  · exact absurd h2 (ne_of_lt (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hlt))
  · linarith
  · exact absurd h2 (ne_of_gt (Real.one_lt_rpow (by norm_num) hgt))

theorem onLine_of_constantNeed (z : TrueZero) (h : ConstantNeed z) :
    rZeroRadialPosition z.1 = 1 / 2 :=
  onLine_of_need_eq_one_two z (h 1 2 le_rfl (by norm_num))

/-- **Besoin constant ⟺ signal de la ligne** (caractérisation ; aucune valeur d'amplitude n'est présupposée). -/
theorem constantNeed_iff_onLine (z : TrueZero) :
    ConstantNeed z ↔ rZeroRadialPosition z.1 = 1 / 2 :=
  ⟨onLine_of_constantNeed z, constantNeed_of_onLine z⟩

/-- **Points de rencontre consécutifs** (contacts `C_k`, `C_{k+1}`) : besoin égal ⟺ signal de la ligne. -/
theorem constantNeed_meeting_points (z : TrueZero) (k : ℤ) :
    pairAmplitude z (contactMinusAt z (k + 1)) = pairAmplitude z (contactMinusAt z k) ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  unfold pairAmplitude
  constructor
  · intro h
    exact (own_contact_amplitude_flat_iff z k).mp (by linarith)
  · intro h
    rw [(own_contact_amplitude_flat_iff z k).mpr h]

/-- Le rapport des besoins à deux rencontres consécutives : `e^{(β − 1/2)π/T}`, `1` ⟺ ligne. -/
theorem need_ratio_meeting_points (z : TrueZero) (k : ℤ) :
    pairAmplitude z (contactMinusAt z (k + 1)) / pairAmplitude z (contactMinusAt z k) =
      Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * (Real.pi / rZeroHeight z.1)) :=
  pairAmplitude_own_contact_step z k

/-! ## 2. Entre deux signaux à besoin constant, seule la fréquence change -/

/-- **Seule la fréquence change entre deux zéros** : deux signaux à besoin constant de hauteurs `T_z < T_w` ont un pas (écart
logarithmique entre rencontres) plus court pour le plus haut, un besoin attendu plus faible, et un rapport de besoins fixé par les
deux hauteurs seules. -/
theorem frequency_only_between_constant_needs {z w : TrueZero} (hz : ConstantNeed z) (hw : ConstantNeed w)
    (hT : rZeroHeight z.1 < rZeroHeight w.1) :
    towerPitch w < towerPitch z ∧
    (∀ x : ℝ, 0 < x → pairAmplitude w x < pairAmplitude z x) ∧
    (∀ x : ℝ, 0 < x → pairAmplitude w x / pairAmplitude z x =
      Real.sqrt (1 / 4 + rZeroHeight z.1 ^ 2) / Real.sqrt (1 / 4 + rZeroHeight w.1 ^ 2)) := by
  have hz' := onLine_of_constantNeed z hz
  have hw' := onLine_of_constantNeed w hw
  exact ⟨(towerPitch_lt_iff z w).mpr hT,
    fun x hx => pairAmplitude_onLine_lt_of_height hz' hw' hT hx,
    fun x hx => (onLine_coupling_ratios hz' hw' hx).2.2⟩

/-! ## 3. Un signal d'amplitude décroissante n'a pas un besoin constant -/

theorem decreasing_breaks_constantNeed (w : TrueZero)
    (hDecr : ∀ x y : ℝ, 1 ≤ x → x < y → pairAmplitude w y < pairAmplitude w x) : ¬ ConstantNeed w := by
  intro h
  have := h 1 2 le_rfl (by norm_num)
  linarith [hDecr 1 2 le_rfl (by norm_num)]

/-- **Fermeture par deux points de rencontre** : si le besoin n'a pas diminué entre deux rencontres `x < y`, un signal
d'amplitude strictement décroissante est exclu. -/
theorem constantNeed_closes (w : TrueZero)
    (hDecr : ∀ x y : ℝ, 1 ≤ x → x < y → pairAmplitude w y < pairAmplitude w x)
    (hTwo : ∃ x y : ℝ, 1 ≤ x ∧ x < y ∧ pairAmplitude w x ≤ pairAmplitude w y) : False := by
  obtain ⟨x, y, hx, hxy, hle⟩ := hTwo
  exact absurd hle (not_le.mpr (hDecr x y hx hxy))

/-! ## 4. La loi généralisée a la force de RH -/

/-- **Tout signal a un besoin constant ⟺ RH.** -/
theorem constantNeed_law_iff_riemannHypothesis :
    (∀ z : TrueZero, ConstantNeed z) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_iff_noLowerSide.mpr
      (fun z hlt => by rw [onLine_of_constantNeed z (h z)] at hlt; linarith)
  · intro hRH z
    exact constantNeed_of_onLine z (thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1)

/-- Forme au passage (celle de la chaîne) : sous l'ancre, « le signal atteint depuis un historique sur la ligne a un besoin
constant » sur tout passage qui monte ⟺ RH. -/
theorem constantNeed_history_law_iff_riemannHypothesis
    (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    (∀ p : TZeroPassage, ∀ hE : 0 < rZeroHeight p.zEarlierMember, VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ConstantNeed ⟨p.zLaterMember, lt_of_lt_of_le hE (passage_height_le p)⟩) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_anchor_and_history_conservation h₁
      (fun p hE hV hOn hHist => by
        rw [hOn]
        exact onLine_of_constantNeed _ (h p hE hV hOn hHist))
  · intro hRH p hE hV hOn hHist
    exact constantNeed_of_onLine _ (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _)

#print axioms constantNeed_iff_onLine
#print axioms constantNeed_meeting_points
#print axioms frequency_only_between_constant_needs
#print axioms constantNeed_closes
#print axioms constantNeed_law_iff_riemannHypothesis
#print axioms constantNeed_history_law_iff_riemannHypothesis

end RHV6Fresh
