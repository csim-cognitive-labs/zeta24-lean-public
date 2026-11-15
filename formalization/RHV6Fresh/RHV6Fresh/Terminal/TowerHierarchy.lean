/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.EscapeFinancing
import RHV6Fresh.Terminal.EngagedProgression
import RHV6Fresh.Terminal.RegimeTower
import RHV6Fresh.Terminal.RaccordDetector

/-!
# RHV6Fresh — hiérarchie de Tour à Tour, raccord par raccord (auteur, 2026-10-03)

Correction de l'auteur : l'objet n'est pas « le reste entier contre la première Tour » mais la dynamique
relative de deux Tours successives, au raccord premier qui les relie ; la Tour suivante est plus faible et
plus serrée, la fuite ne se fait qu'en hauteur, et la première Tour fournit ensuite l'enveloppe.

* **§1 Deux Tours en ligne** : la plus haute est strictement plus faible en tout point de l'axe des premiers,
  d'un rapport constant `‖ρ_z‖/‖ρ_w‖ < 1` ; son pas est strictement plus petit ; sa phase avance strictement
  plus vite (la vitesse de rotation AUGMENTE avec la hauteur) ; son décalage de phase est plus grand
  (`onLine_tower_hierarchy`).
* **§2 La hiérarchie au raccord** : `RaccordHierarchy` = au premier partagé, la Tour d'arrivée ne lit pas plus
  d'énergie que la Tour de départ, et son pas est strictement plus petit. Elle tient sur tout passage où la
  hauteur avance, quelles que soient les positions radiales (`raccordHierarchy_of_height_advance`) ; elle
  force la hauteur à avancer (`raccordHierarchy_forces_height`) ; le passage de même hauteur la viole sur
  les deux lectures à la fois : pas conservé, énergie renversée (`sameHeight_breaks_hierarchy`).
* **§3 Propagation de raccord en raccord** : au raccord qui quitte un membre engagé, la hauteur avance et la
  hiérarchie tient, par théorème (`raccordHierarchy_of_engaged_departure`) ; la hiérarchie au raccord suivant met
  l'arrivée en ligne (`engaged_step_of_next_hierarchy`) ; la hiérarchie à tous les raccords donne l'hypothèse
  de Riemann et l'enveloppe de la première Tour (`riemannHypothesis_of_raccordHierarchy`,
  `first_tower_envelope_of_raccordHierarchy`) ; elle lui est équivalente
  (`raccordHierarchy_iff_riemannHypothesis`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse `def P… : Prop`.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Deux Tours en ligne -/

/-- **Hiérarchie de deux Tours en ligne** : amplitude strictement plus faible partout, rapport constant
`< 1`, pas strictement plus petit, phase strictement plus rapide, décalage de phase plus grand. -/
theorem onLine_tower_hierarchy {z w : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2)
    (hw : rZeroRadialPosition w.1 = 1 / 2) (hT : rZeroHeight z.1 < rZeroHeight w.1) :
    (∀ x : ℝ, 0 < x → ‖zeroTerm w x‖ < ‖zeroTerm z x‖) ∧
    (∀ x : ℝ, 0 < x → energyRatio z w x = ‖zeroPoint z‖ / ‖zeroPoint w‖) ∧
    ‖zeroPoint z‖ / ‖zeroPoint w‖ < 1 ∧
    towerPitch w < towerPitch z ∧
    (∀ x y : ℝ, 0 < x → x < y →
      rZeroHeight z.1 * Real.log (y / x) < rZeroHeight w.1 * Real.log (y / x)) ∧
    Real.arctan (2 * rZeroHeight z.1) < Real.arctan (2 * rZeroHeight w.1) := by
  have hβ : rZeroRadialPosition z.1 = rZeroRadialPosition w.1 := hz.trans hw.symm
  refine ⟨fun x hx => amplitude_lt_of_height_lt z w hβ hT hx, fun x hx => ?_, ?_,
    (towerPitch_lt_iff z w).mpr hT, fun x y hx hxy => ?_, Real.arctan_strictMono (by linarith)⟩
  · rw [energyRatio_eq z w hx, hβ, sub_self, Real.rpow_zero, one_mul]
  · exact (div_lt_one (zeroPoint_norm_pos w)).mpr (zeroPoint_norm_lt_of_height_lt z w hβ hT)
  · exact mul_lt_mul_of_pos_right hT (Real.log_pos ((one_lt_div hx).mpr hxy))

/-! ## 2. La hiérarchie au raccord -/

/-- **Hiérarchie au raccord d'un passage** : au premier partagé, la Tour d'arrivée ne lit pas plus d'énergie
que la Tour de départ, et son pas est strictement plus petit. -/
def RaccordHierarchy (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) : Prop :=
  (towerRaccordOf p hE hL).Oriented ∧
    towerPitch ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩

/-- **La hiérarchie tient sur tout passage où la hauteur avance**, quelles que soient les positions
radiales des deux membres. -/
theorem raccordHierarchy_of_height_advance (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p)
    (hT2 : 2 ≤ rZeroHeight p.zLaterMember) : RaccordHierarchy p hE hL :=
  ⟨towerRaccord_oriented_of_height_lt p hE hL hV hT2, (vertical_iff_pitch_contracts p hE hL).mp hV⟩

/-- **La hiérarchie force la hauteur à avancer.** -/
theorem raccordHierarchy_forces_height {p : TZeroPassage} {hE : 0 < rZeroHeight p.zEarlierMember}
    {hL : 0 < rZeroHeight p.zLaterMember} (h : RaccordHierarchy p hE hL) : VerticalPassage p :=
  (vertical_iff_pitch_contracts p hE hL).mpr h.2

/-- **Le passage de même hauteur viole la hiérarchie sur ses deux lectures** : le pas est conservé, et dès
la hauteur 2 l'énergie au premier partagé est strictement renversée. -/
theorem sameHeight_breaks_hierarchy (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hH : HorizontalPassage p) :
    towerPitch ⟨p.zLaterMember, hL⟩ = towerPitch ⟨p.zEarlierMember, hE⟩ ∧
    (2 ≤ rZeroHeight p.zEarlierMember →
      ‖zeroTerm ⟨p.zEarlierMember, hE⟩ (towerRaccordOf p hE hL).M‖ <
        ‖zeroTerm ⟨p.zLaterMember, hL⟩ (towerRaccordOf p hE hL).M‖) ∧
    ¬ RaccordHierarchy p hE hL :=
  ⟨(horizontal_iff_pitch_kept p hE hL).mp hH,
    fun hT2 => towerRaccord_reverses_of_sameHeight (towerRaccordOf p hE hL) hH hT2
      (horizontalPassage_radial_lt hH),
    fun h => absurd hH (ne_of_lt (raccordHierarchy_forces_height h))⟩

/-! ## 3. Propagation de raccord en raccord -/

/-- **Pas de propagation** : depuis l'état engagé, si la hiérarchie tient au raccord qui suit l'arrivée,
l'arrivée est en ligne et le passage est vertical. -/
theorem engaged_step_of_next_hierarchy {o p q : TZeroPassage}
    (hJ : o.zLaterMember = p.zEarlierMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hJ' : p.zLaterMember = q.zEarlierMember)
    {hqE : 0 < rZeroHeight q.zEarlierMember} {hqL : 0 < rZeroHeight q.zLaterMember}
    (hq : RaccordHierarchy q hqE hqL) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ∧ VerticalPassage p := by
  obtain ⟨⟨hV, -⟩, -, -, -, -, -, -, -, -, -, hQ⟩ := engaged_progression hJ ho hOn hE hL
  exact ⟨(hQ q hJ').mp (raccordHierarchy_forces_height hq), hV⟩

/-- **Progression obligatoire de la hauteur depuis l'état engagé, lue au raccord** : un membre en ligne
atteint par un passage vertical est quitté par un passage où la hauteur avance, et la hiérarchie tient à ce
raccord, quelle que soit la position radiale de l'arrivée. -/
theorem raccordHierarchy_of_engaged_departure {o p : TZeroPassage}
    (hJ : o.zLaterMember = p.zEarlierMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hT2 : 2 ≤ rZeroHeight p.zLaterMember) :
    VerticalPassage p ∧ RaccordHierarchy p hE hL := by
  have hV : VerticalPassage p := (engaged_regime_kept hJ ho (by rw [hJ]; exact hOn)).1
  exact ⟨hV, raccordHierarchy_of_height_advance p hE hL hV hT2⟩

/-- **La hiérarchie à tous les raccords donne l'hypothèse de Riemann.** -/
theorem riemannHypothesis_of_raccordHierarchy
    (h : ∀ (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
      (hL : 0 < rZeroHeight p.zLaterMember), RaccordHierarchy p hE hL) : RiemannHypothesis :=
  riemannHypothesis_of_height_always_advances fun p hE =>
    raccordHierarchy_forces_height (h p hE (hE.trans_le (passage_height_le p)))

/-- **Sous l'hypothèse de Riemann, la hiérarchie tient à tous les raccords.** -/
theorem raccordHierarchy_of_riemannHypothesis (hRH : RiemannHypothesis) (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    RaccordHierarchy p hE hL :=
  ⟨towerRaccord_oriented_of_riemannHypothesis hRH p hE hL,
    (vertical_iff_pitch_contracts p hE hL).mp (passage_height_lt_of_riemannHypothesis hRH p)⟩

/-- **La hiérarchie à tous les raccords équivaut à l'hypothèse de Riemann.** -/
theorem raccordHierarchy_iff_riemannHypothesis :
    (∀ (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
      (hL : 0 < rZeroHeight p.zLaterMember), RaccordHierarchy p hE hL) ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_raccordHierarchy, fun hRH p hE hL => raccordHierarchy_of_riemannHypothesis hRH p hE hL⟩

/-- **L'enveloppe de la première Tour** : si la hiérarchie tient à tous les raccords, toute Tour au moins
aussi haute qu'une Tour donnée est dans son champ, en tout point de l'axe des premiers. -/
theorem first_tower_envelope_of_raccordHierarchy
    (h : ∀ (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
      (hL : 0 < rZeroHeight p.zLaterMember), RaccordHierarchy p hE hL)
    {z₁ w : TrueZero} (hT : rZeroHeight z₁.1 ≤ rZeroHeight w.1) : InsideField z₁ w :=
  have hRH := riemannHypothesis_of_raccordHierarchy h
  inside_field_of_onLine (thm_zeroRadialPosition_half_of_riemannHypothesis hRH z₁.1)
    (thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1) hT

#print axioms onLine_tower_hierarchy
#print axioms raccordHierarchy_of_height_advance
#print axioms raccordHierarchy_forces_height
#print axioms sameHeight_breaks_hierarchy
#print axioms engaged_step_of_next_hierarchy
#print axioms raccordHierarchy_of_engaged_departure
#print axioms riemannHypothesis_of_raccordHierarchy
#print axioms raccordHierarchy_of_riemannHypothesis
#print axioms raccordHierarchy_iff_riemannHypothesis
#print axioms first_tower_envelope_of_raccordHierarchy

end RHV6Fresh
