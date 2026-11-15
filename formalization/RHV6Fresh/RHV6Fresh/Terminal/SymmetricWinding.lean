/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FirstTowerHorizon
import RHV6Fresh.Terminal.EngagedClosureVerdict
import RHV6Fresh.Terminal.PersistentCapture
import RHV6Fresh.Terminal.DoubleRigidity

/-!
# RHV6Fresh — enroulement symétrique dans la Tour précédente (auteur, 2026-10-04)

Énoncé de l'auteur : « la Tour du zéro suivant doit symétriquement s'enrouler à l'intérieur de la Tour du
zéro précédent ; l'amplitude est bloquée ; le zéro suivant : β = 1/2, pas de choix ».

Implémentation fidèle, sur un passage parti d'un zéro en ligne :

* **Enroulement symétrique** = la Tour du zéro suivant ET la Tour de son miroir restent, en tout point de
  l'axe des premiers, sous la Tour du zéro précédent.
* `symmetric_winding_iff_onLine` : enroulement symétrique ⟺ `β_l = 1/2`. L'amplitude bloquée des deux
  côtés ne laisse aucun choix.
* `inside_iff_support` : la moitié « Tour du zéro suivant » se lit sur les supports seuls dès que
  `β_l ≤ 1/2`.
* `symmetric_winding_keeps_regime` : sous l'enroulement symétrique, le passage suivant est vertical.

Borne : la moitié « Tour du miroir » n'est pas dérivée ici ; c'est elle qui porte `β_l ≥ 1/2`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Enroulement symétrique ⟺ en ligne.** Depuis un zéro en ligne, la Tour du zéro suivant et celle de son
miroir restent toutes deux sous la Tour du zéro précédent si et seulement si le zéro suivant est en ligne. -/
theorem symmetric_winding_iff_onLine (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    (InsideField ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ ∧
        InsideField ⟨p.zEarlierMember, hE⟩ (mirrorMember ⟨p.zLaterMember, hL⟩)) ↔
      rZeroRadialPosition p.zLaterMember = 1 / 2 := by
  constructor
  · rintro ⟨hw, hm⟩
    exact inside_field_forces_line (z₁ := ⟨p.zEarlierMember, hE⟩) (w := ⟨p.zLaterMember, hL⟩) hOn hw hm
  · intro hl
    have hin : InsideField ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ :=
      inside_field_of_onLine (z₁ := ⟨p.zEarlierMember, hE⟩) (w := ⟨p.zLaterMember, hL⟩) hOn hl
        (passage_height_le p)
    refine ⟨hin, ?_⟩
    rw [mirrorMember_eq_self_of_onLine (z := ⟨p.zLaterMember, hL⟩) hl]
    exact hin

/-- **La Tour du zéro suivant sous la précédente, lue sur les supports.** Si `β_w ≤ β_z`, la Tour de `w`
reste sous celle de `z` en tout point si et seulement si le support de `z` ne dépasse pas celui de `w`. -/
theorem inside_iff_support {z w : TrueZero}
    (hβ : rZeroRadialPosition w.1 ≤ rZeroRadialPosition z.1) :
    InsideField z w ↔ ‖zeroPoint z‖ ≤ ‖zeroPoint w‖ := by
  constructor
  · intro h
    have h1 := h 1 le_rfl
    unfold firstField at h1
    rw [norm_zeroTerm_eq w one_pos, norm_zeroTerm_eq z one_pos, Real.one_rpow, Real.one_rpow] at h1
    exact (one_div_le_one_div (norm_zeroPoint_pos w) (norm_zeroPoint_pos z)).mp h1
  · exact inside_field_of_parameters hβ

/-- **Sous l'enroulement symétrique, le régime est gardé** : le passage suivant est vertical. -/
theorem symmetric_winding_keeps_regime {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) (hV : VerticalPassage p)
    (hw : InsideField ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩)
    (hm : InsideField ⟨p.zEarlierMember, hE⟩ (mirrorMember ⟨p.zLaterMember, hL⟩)) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ∧ VerticalPassage q ∧ ¬ HorizontalPassage q := by
  have hl := (symmetric_winding_iff_onLine p hE hL hOn).mp ⟨hw, hm⟩
  exact ⟨hl, engaged_regime_kept hJ hV hl⟩

/-! ## Enroulement de la Tour entière (auteur, 2026-10-04)

Énoncé de l'auteur : « aucune Tour hors ligne ne peut s'enrouler à l'intérieur d'une Tour sur la ligne
critique ». La Tour est la trace du terme sur tout l'axe des réels positifs, pas seulement sur `x ≥ 1`. -/

/-- **Une Tour reste sous une autre sur tout l'axe positif ⟺ même partie réelle et supports ordonnés.** -/
theorem whole_tower_inside_iff (z w : TrueZero) :
    (∀ x : ℝ, 0 < x → ‖zeroTerm w x‖ ≤ ‖zeroTerm z x‖) ↔
      rZeroRadialPosition w.1 = rZeroRadialPosition z.1 ∧ ‖zeroPoint z‖ ≤ ‖zeroPoint w‖ := by
  constructor
  · intro h
    have hup : rZeroRadialPosition w.1 ≤ rZeroRadialPosition z.1 :=
      exponent_le_of_inside (norm_zeroPoint_pos w) (norm_zeroPoint_pos z) (fun x hx => by
        have hx0 : 0 < x := by linarith
        have := h x hx0
        rwa [norm_zeroTerm_eq w hx0, norm_zeroTerm_eq z hx0] at this)
    have hdown : -rZeroRadialPosition w.1 ≤ -rZeroRadialPosition z.1 :=
      exponent_le_of_inside (norm_zeroPoint_pos w) (norm_zeroPoint_pos z) (fun y hy => by
        have hy0 : 0 < y := by linarith
        have := h y⁻¹ (inv_pos.mpr hy0)
        rwa [norm_zeroTerm_eq w (inv_pos.mpr hy0), norm_zeroTerm_eq z (inv_pos.mpr hy0),
          Real.inv_rpow hy0.le, Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le,
          ← Real.rpow_neg hy0.le] at this)
    have h1 := h 1 one_pos
    rw [norm_zeroTerm_eq w one_pos, norm_zeroTerm_eq z one_pos, Real.one_rpow, Real.one_rpow] at h1
    exact ⟨le_antisymm hup (by linarith),
      (one_div_le_one_div (norm_zeroPoint_pos w) (norm_zeroPoint_pos z)).mp h1⟩
  · rintro ⟨hβ, hρ⟩ x hx
    rw [norm_zeroTerm_eq w hx, norm_zeroTerm_eq z hx, hβ]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (norm_zeroPoint_pos z) hρ

/-- **Aucune Tour hors ligne ne s'enroule tout entière dans une Tour en ligne** : il existe un point de
l'axe positif où elle la dépasse strictement. -/
theorem off_tower_not_inside_line_tower {z w : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2)
    (hw : rZeroRadialPosition w.1 ≠ 1 / 2) :
    ∃ x : ℝ, 0 < x ∧ ‖zeroTerm z x‖ < ‖zeroTerm w x‖ := by
  by_contra hno
  push Not at hno
  exact hw (((whole_tower_inside_iff z w).mp hno).1.trans hz)

/-- **Depuis un zéro en ligne, la Tour du zéro suivant s'enroule tout entière dans la précédente ⟺ le
zéro suivant est en ligne.** -/
theorem whole_winding_iff_onLine (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    (∀ x : ℝ, 0 < x →
        ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖) ↔
      rZeroRadialPosition p.zLaterMember = 1 / 2 := by
  refine (whole_tower_inside_iff ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩).trans ?_
  constructor
  · rintro ⟨h, _⟩
    exact h.trans hOn
  · intro hl
    refine ⟨hl.trans hOn.symm, ?_⟩
    have hin : InsideField ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ :=
      inside_field_of_onLine (z₁ := ⟨p.zEarlierMember, hE⟩) (w := ⟨p.zLaterMember, hL⟩) hOn hl
        (passage_height_le p)
    exact (inside_iff_support (z := ⟨p.zEarlierMember, hE⟩) (w := ⟨p.zLaterMember, hL⟩)
      (by rw [hOn]; exact hl.le)).mp hin

/-! ## Un seul but : toute Tour s'enroule tout entière dans la Tour du premier zéro (auteur, 2026-10-04) -/

/-- **Si toute Tour s'enroule tout entière dans la Tour d'un même zéro, l'hypothèse de Riemann suit**, sans
rien supposer sur ce zéro : son miroir s'enroule aussi en lui, donc sa partie réelle vaut un demi. -/
theorem riemannHypothesis_of_whole_winding {z₁ : TrueZero}
    (h : ∀ w : TrueZero, ∀ x : ℝ, 0 < x → ‖zeroTerm w x‖ ≤ ‖zeroTerm z₁ x‖) : RiemannHypothesis := by
  have hEq : ∀ w : TrueZero, rZeroRadialPosition w.1 = rZeroRadialPosition z₁.1 :=
    fun w => ((whole_tower_inside_iff z₁ w).mp (h w)).1
  have h₁ : rZeroRadialPosition z₁.1 = 1 / 2 := by
    have hm := hEq (mirrorMember z₁)
    rw [mirrorMember_radial] at hm
    linarith
  exact thm_riemannHypothesis_of_allUpperOnCriticalLine fun w => (hEq w).trans h₁

/-- **Pour le premier zéro, « toute Tour s'enroule tout entière dans la sienne » équivaut à l'hypothèse de
Riemann.** Un seul énoncé : ni amorce séparée, ni transmission séparée. -/
theorem whole_winding_in_first_iff_riemannHypothesis {z₁ : TrueZero}
    (hFirst : sUpperZerosBelow z₁.1 = ∅) :
    (∀ w : TrueZero, ∀ x : ℝ, 0 < x → ‖zeroTerm w x‖ ≤ ‖zeroTerm z₁ x‖) ↔ RiemannHypothesis := by
  refine ⟨riemannHypothesis_of_whole_winding, fun hRH w => ?_⟩
  have h₁ := thm_zeroRadialPosition_half_of_riemannHypothesis hRH z₁.1
  have hw := thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1
  have hin : InsideField z₁ w := (first_field_iff_riemannHypothesis hFirst h₁).mpr hRH w
  exact (whole_tower_inside_iff z₁ w).mpr
    ⟨hw.trans h₁.symm, (inside_iff_support (by rw [hw, h₁])).mp hin⟩

#print axioms riemannHypothesis_of_whole_winding
#print axioms whole_winding_in_first_iff_riemannHypothesis

#print axioms whole_tower_inside_iff
#print axioms off_tower_not_inside_line_tower
#print axioms whole_winding_iff_onLine

#print axioms symmetric_winding_iff_onLine
#print axioms inside_iff_support
#print axioms symmetric_winding_keeps_regime

/-! ## Tour prisonnière par les zéros : la précédente au-dessus, la suivante en dessous -/

/-- **Une Tour prisonnière de la Tour du zéro précédent, et qui tient prisonnière la Tour du zéro suivant, est
celle d'un zéro en ligne.** Les deux côtés sont des zéros (le précédent et le suivant), lus sur `x ≥ 1`
seulement ; rien n'est supposé sur le zéro de départ. -/
theorem prisoner_between_zeros_onLine {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (he : 0 < rZeroHeight p.zEarlierMember) (hPrev : TowerPrisoner p) (hNext : TowerPrisoner q) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 := by
  have hl : 0 < rZeroHeight p.zLaterMember := lt_of_lt_of_le he (passage_height_le p)
  have hqe : 0 < rZeroHeight q.zEarlierMember := hJ ▸ hl
  have hql : 0 < rZeroHeight q.zLaterMember := lt_of_lt_of_le hqe (passage_height_le q)
  have hp : VerticalPassage p := prisoner_forces_height hPrev he hl
  have hq : VerticalPassage q := prisoner_forces_height hNext hqe hql
  exact le_antisymm (passage_entry_radial_le_half p hp)
    ((arrival_radial_floor_iff_next_vertical hJ hp).mpr hq)

#print axioms prisoner_between_zeros_onLine

/-- **Une seule demande** : sur tout passage, la Tour du zéro suivant reste sous la Tour du zéro
précédent en tout point de l'axe positif. Aucune amorce séparée : l'enroulement entier donne la
même partie réelle aux deux zéros, ce qui exclut tout passage de même hauteur. Équivalence, non
dérivée. -/
theorem riemannHypothesis_iff_passage_whole_winding :
    (∀ p : TZeroPassage, ∀ (hE : 0 < rZeroHeight p.zEarlierMember)
        (hL : 0 < rZeroHeight p.zLaterMember), ∀ x : ℝ, 0 < x →
        ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    refine no_sameHeight_iff_riemannHypothesis.mp fun p hE hH => ?_
    have hL : 0 < rZeroHeight p.zLaterMember := lt_of_lt_of_le hE (passage_height_le p)
    have hEq := ((whole_tower_inside_iff ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩).mp
      (h p hE hL)).1
    have hlt := horizontalPassage_radial_lt hH
    simp only at hEq
    linarith
  · intro hRH p hE hL
    exact (whole_winding_iff_onLine p hE hL
      (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _)).mpr
      (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _)

#print axioms riemannHypothesis_iff_passage_whole_winding

end RHV6Fresh
