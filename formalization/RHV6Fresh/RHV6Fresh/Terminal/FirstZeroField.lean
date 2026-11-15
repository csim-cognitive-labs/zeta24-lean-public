/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TowerWinding

/-!
# RHV6Fresh — le champ du premier zéro en ligne (auteur, 2026-10-03)

Énoncé de l'auteur : « tous les zéros suivants s'enroulent à l'intérieur du premier zéro sur la ligne ; le
champ du zéro sur la ligne détermine un champ qui ne peut être dépassé par aucun autre zéro ».

* **§1 Le champ** : `firstField z₁ x = ‖x^{ρ₁}/ρ₁‖ = x^{β₁}/‖ρ₁‖`, amplitude de la Tour du premier zéro le long
  de l'axe des premiers (`norm_zeroTerm_eq`). Un zéro `w` est dans le champ de `z₁` si sa Tour ne le dépasse
  jamais : `‖x^{ρ_w}/ρ_w‖ ≤ ‖x^{ρ₁}/ρ₁‖` pour tout `x ≥ 1` (`InsideField`).
* **§2 Tout zéro en ligne plus haut est dans le champ** (`inside_field_of_onLine`).
* **§3 Le champ force la ligne** : un zéro et son miroir dans le champ d'un zéro en ligne sont en ligne
  (`exponent_le_of_inside`, `inside_field_forces_line`) ; si aucun zéro ne dépasse le champ du premier zéro en
  ligne, l'hypothèse de Riemann suit (`riemannHypothesis_of_first_field`).
* **§4 Statut de l'énoncé du champ** : pour le premier zéro, en ligne, « aucun zéro ne dépasse son champ »
  équivaut à l'hypothèse de Riemann (`first_field_iff_riemannHypothesis`).
* **§5 Enroulement sur l'axe des premiers** (sens de `TowerWinding`) : dès que l'écart de hauteur dépasse
  `T(π/2)/(kπ)`, le contact `k` de toute Tour plus haute est en deçà du contact `k` de la Tour plus basse, pour
  toutes positions radiales des deux (`prime_axis_nesting_any_depth`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse `def P… : Prop`.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Le champ -/

/-- Amplitude de la Tour d'un zéro le long de l'axe des premiers. -/
theorem norm_zeroTerm_eq (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm z x‖ = x ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖ := by
  unfold zeroTerm
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, zeroPoint_re]

/-- **Le champ du zéro `z₁`** : l'amplitude de sa Tour en chaque point de l'axe des premiers. -/
noncomputable def firstField (z₁ : TrueZero) (x : ℝ) : ℝ := ‖zeroTerm z₁ x‖

/-- **`w` est dans le champ de `z₁`** : sa Tour ne dépasse jamais celle de `z₁`, en aucun `x ≥ 1`. -/
def InsideField (z₁ w : TrueZero) : Prop := ∀ x : ℝ, 1 ≤ x → ‖zeroTerm w x‖ ≤ firstField z₁ x

theorem norm_zeroPoint_pos (z : TrueZero) : 0 < ‖zeroPoint z‖ := norm_pos_iff.mpr (zeroPoint_ne_zero z)

/-! ## 2. Les zéros en ligne plus hauts sont dans le champ -/

/-- **Tout zéro en ligne au moins aussi haut que `z₁` en ligne est dans son champ.** -/
theorem inside_field_of_onLine {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hw : rZeroRadialPosition w.1 = 1 / 2) (hT : rZeroHeight z₁.1 ≤ rZeroHeight w.1) :
    InsideField z₁ w := by
  intro x hx
  have hx0 : 0 < x := by linarith
  unfold firstField
  rw [norm_zeroTerm_eq w hx0, norm_zeroTerm_eq z₁ hx0, hw, h₁]
  have hn : ‖zeroPoint z₁‖ ≤ ‖zeroPoint w‖ := by
    have h1 := Complex.sq_norm (zeroPoint z₁)
    have h2 := Complex.sq_norm (zeroPoint w)
    rw [Complex.normSq_apply, zeroPoint_re, zeroPoint_im] at h1 h2
    have hz1 : 0 < rZeroHeight z₁.1 := z₁.2
    have hsq : ‖zeroPoint z₁‖ ^ 2 ≤ ‖zeroPoint w‖ ^ 2 := by
      rw [h1, h2, h₁, hw]; nlinarith
    nlinarith [norm_nonneg (zeroPoint z₁), norm_nonneg (zeroPoint w)]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) (norm_zeroPoint_pos z₁) hn

/-! ## 3. Le champ force la ligne -/

/-- **Un exposant borné par le champ** : si `x^β/A ≤ x^γ/B` pour tout `x ≥ 1` (`A, B > 0`), alors `β ≤ γ`. -/
theorem exponent_le_of_inside {β γ A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : ∀ x : ℝ, 1 ≤ x → x ^ β / A ≤ x ^ γ / B) : β ≤ γ := by
  by_contra hlt
  push Not at hlt
  set c := β - γ with hc
  have hcpos : 0 < c := by linarith
  set u : ℝ := A / (B * c) + 1 with hu
  have hu0 : 0 < u := by positivity
  have hx := h (Real.exp u) (Real.one_le_exp hu0.le)
  rw [← Real.exp_mul, ← Real.exp_mul, div_le_div_iff₀ hA hB] at hx
  -- `exp(uβ)·B ≤ exp(uγ)·A` ⟹ `exp(u c) ≤ A/B`
  have hsplit : Real.exp (u * β) = Real.exp (u * γ) * Real.exp (u * c) := by
    rw [← Real.exp_add]; congr 1; rw [hc]; ring
  rw [hsplit] at hx
  have hpos := Real.exp_pos (u * γ)
  have hle : Real.exp (u * c) * B ≤ A := by nlinarith
  have hexp : u * c + 1 ≤ Real.exp (u * c) := Real.add_one_le_exp _
  have hkey : A < (u * c + 1) * B := by
    rw [hu]
    have : (A / (B * c) + 1) * c = A / B + c := by field_simp
    rw [this]
    have : (A / B + c + 1) * B = A + (c + 1) * B := by field_simp; ring
    rw [this]; nlinarith
  nlinarith

/-- **Un zéro et son miroir dans le champ d'un zéro en ligne sont en ligne.** -/
theorem inside_field_forces_line {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hw : InsideField z₁ w) (hm : InsideField z₁ (mirrorMember w)) :
    rZeroRadialPosition w.1 = 1 / 2 := by
  have key : ∀ v : TrueZero, InsideField z₁ v → rZeroRadialPosition v.1 ≤ 1 / 2 := by
    intro v hv
    have := exponent_le_of_inside (norm_zeroPoint_pos v) (norm_zeroPoint_pos z₁)
      (fun x hx => by
        have := hv x hx
        unfold firstField at this
        rwa [norm_zeroTerm_eq v (by linarith), norm_zeroTerm_eq z₁ (by linarith)] at this)
    rwa [h₁] at this
  have h1 := key w hw
  have h2 := key _ hm
  rw [mirrorMember_radial] at h2
  linarith

/-- **Si aucun zéro ne dépasse le champ d'un zéro en ligne, l'hypothèse de Riemann suit.** -/
theorem riemannHypothesis_of_first_field {z₁ : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hField : ∀ w : TrueZero, InsideField z₁ w) : RiemannHypothesis :=
  thm_riemannHypothesis_of_allUpperOnCriticalLine fun w =>
    inside_field_forces_line h₁ (hField w) (hField (mirrorMember w))

/-! ## 4. Statut de l'énoncé du champ -/

/-- **Pour le premier zéro, en ligne, « aucun zéro ne dépasse son champ » équivaut à l'hypothèse de
Riemann.** « Premier » : aucun zéro de la moitié supérieure ne le précède. -/
theorem first_field_iff_riemannHypothesis {z₁ : TrueZero} (hFirst : sUpperZerosBelow z₁.1 = ∅)
    (h₁ : rZeroRadialPosition z₁.1 = 1 / 2) :
    (∀ w : TrueZero, InsideField z₁ w) ↔ RiemannHypothesis := by
  refine ⟨riemannHypothesis_of_first_field h₁, fun hRH w => ?_⟩
  have hT : rZeroHeight z₁.1 ≤ rZeroHeight w.1 := by
    by_contra hlt
    push Not at hlt
    have hmem : w.1 ∈ sUpperZerosBelow z₁.1 :=
      ⟨w.2, (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mpr (Or.inl hlt)⟩
    rw [hFirst] at hmem
    exact hmem
  exact inside_field_of_onLine h₁ (thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1) hT

/-! ## 5. L'enroulement sur l'axe des premiers -/

/-- **Enroulement à indice fixé, toutes positions radiales.** Si `T·(π/2 + kπ) ≤ T'·kπ`, le contact `k`
de la Tour `(β', T')` est strictement en deçà du contact `k` de la Tour `(β, T)`, quels que soient `β, β' > 0`. -/
theorem prime_axis_nesting_any_depth {β β' T T' k : ℝ} (hβ : 0 < β) (hT : 0 < T) (hT' : 0 < T')
    (hgap : T * (Real.pi / 2 + k * Real.pi) ≤ T' * (k * Real.pi)) :
    windingContact β' T' k < windingContact β T k := by
  unfold windingContact
  apply Real.exp_lt_exp.mpr
  have hφ := phase_pos hβ hT
  have hφ' := Real.arctan_lt_pi_div_two (T' / β')
  rw [div_lt_div_iff₀ hT' hT]
  nlinarith

#print axioms norm_zeroTerm_eq
#print axioms inside_field_of_onLine
#print axioms exponent_le_of_inside
#print axioms inside_field_forces_line
#print axioms riemannHypothesis_of_first_field
#print axioms first_field_iff_riemannHypothesis
#print axioms prime_axis_nesting_any_depth

end RHV6Fresh
