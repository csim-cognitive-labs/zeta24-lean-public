/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.BoxAnchor

/-!
# Comptage d'une bande de hauteur quelconque par deux rectangles (consolidation des coupures 22 et 28)

Généralise `upperWindowOpen_count_of_boxes` (BoxAnchor, valeur `1`) à une valeur entière `K` quelconque : si `ξ₁` ne
s'annule pas sur les bords de `B₁ = [σ₀, 2] × [−t₁, T]` et `B₂ = [1 − σ₀, 2] × [−t₁, T]`, si `(2πi)⁻¹∮_{B₁} ξ₁′/ξ₁ = K`,
`∮_{B₂} ξ₁′/ξ₁ = 0`, et si aucun zéro n'a sa hauteur dans `]−t₁, 0[` (fourni par les rectangles de la première bande,
`box_no_lower_zero`), alors `Σ_{upperWindowOpen T} m(ρ) = K`. Le bord supérieur de `B₁` exclut tout zéro à la hauteur `T`
(miroir compris), donc la fenêtre fermée a la même valeur. Logique seule, aucune valeur numérique.
-/

namespace RHV6Fresh

open Complex Set RHV3Lean

/-- Rectangle `B₂` sans zéro ⟹ tout zéro de hauteur `]−t₁, T[` est dans `B₁` (miroir). -/
theorem box_strip_mem {σ₀ t₁ T : ℝ} (hσ₀ : 0 < σ₀) (hσ₀' : σ₀ < 1 / 2) (ht₁ : 0 < t₁) (ht₁T : t₁ < T)
    (hB₂ : ∀ s ∈ rectBoundary (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) ((2 : ℝ) + T * I), completedEntire s ≠ 0)
    (hI₂ : rectBoundaryIntegral (logDeriv completedEntire) (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I)
      ((2 : ℝ) + T * I) = 0) :
    ∀ ρ, completedEntire ρ = 0 → ρ.im ∈ Ioo (-t₁) T → ρ ∈ boxZeros σ₀ 2 (-t₁) T := by
  have hS₂ := box_order_sum (σa := 1 - σ₀) (σb := 2) (ta := -t₁) (tb := T) (by linarith) (by linarith) hB₂
  rw [hI₂, mul_zero] at hS₂
  have hsum₂ : ∑ ρ ∈ boxZeros (1 - σ₀) 2 (-t₁) T, analyticOrderNatAt completedEntire ρ = 0 := by
    exact_mod_cast hS₂.symm
  have hZ₂ : boxZeros (1 - σ₀) 2 (-t₁) T = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ρ hρ
    have h1 := completedEntire_order_pos (mem_boxZeros.mp hρ).1
    have := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hρ (f := fun ρ => analyticOrderNatAt completedEntire ρ)
    rw [hsum₂] at this; omega
  have hc1 : ∀ ρ, completedEntire ρ = 0 → ρ.im ∈ Ioo (-t₁) T → ρ.re < 1 - σ₀ := by
    intro ρ hρ him
    have hnt := (completedEntire_eq_zero_iff_nontrivial ρ).mp hρ
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt | heq
    · have : ρ ∈ boxZeros (1 - σ₀) 2 (-t₁) T :=
        mem_boxZeros.mpr ⟨hρ, ⟨hlt, by linarith [hnt.2.2]⟩, him⟩
      rw [hZ₂] at this; exact Finset.notMem_empty _ this
    · apply hB₂ ρ _ hρ
      right
      refine ⟨Or.inl (by simp [heq]), ?_⟩
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      exact ⟨by simpa using him.1.le, by simpa using him.2.le⟩
  intro ρ hρ him
  have hnt := (completedEntire_eq_zero_iff_nontrivial ρ).mp hρ
  have hm := mirrorPoint_nontrivial hnt
  have hmz : completedEntire (1 - (starRingEnd ℂ) ρ) = 0 :=
    (completedEntire_eq_zero_iff_nontrivial _).mpr hm
  have hmim : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by simp
  have := hc1 _ hmz (by rw [hmim]; exact him)
  simp at this
  exact mem_boxZeros.mpr ⟨hρ, ⟨by linarith, by linarith [hnt.2.2]⟩, him⟩

/-- **Aucun zéro de hauteur dans `]−t₁, 0[`**, depuis deux rectangles de valeur `1` et `0` (la première bande) : un tel
zéro et son conjugué seraient deux points distincts de `B₁`, d'ordres `≥ 1`, contre une somme d'ordres égale à `1`. -/
theorem box_no_lower_zero {σ₀ t₁ T : ℝ} (hσ₀ : 0 < σ₀) (hσ₀' : σ₀ < 1 / 2) (ht₁ : 0 < t₁) (ht₁T : t₁ < T)
    (hB₁ : ∀ s ∈ rectBoundary ((σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T : ℂ) * I), completedEntire s ≠ 0)
    (hB₂ : ∀ s ∈ rectBoundary (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) ((2 : ℝ) + T * I), completedEntire s ≠ 0)
    (hI₁ : (2 * (Real.pi : ℂ) * I)⁻¹ *
      rectBoundaryIntegral (logDeriv completedEntire) ((σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) ((2 : ℝ) + T * I) = 1)
    (hI₂ : rectBoundaryIntegral (logDeriv completedEntire) (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I)
      ((2 : ℝ) + T * I) = 0) :
    ∀ ρ, completedEntire ρ = 0 → ρ.im ∈ Ioo (-t₁) 0 → False := by
  have hS₁ := box_order_sum (σa := σ₀) (σb := 2) (ta := -t₁) (tb := T) (by linarith) (by linarith) hB₁
  rw [hI₁] at hS₁
  have hsum₁ : ∑ ρ ∈ boxZeros σ₀ 2 (-t₁) T, analyticOrderNatAt completedEntire ρ = 1 := by exact_mod_cast hS₁.symm
  have hmem := box_strip_mem hσ₀ hσ₀' ht₁ ht₁T hB₂ hI₂
  intro ρ hρ him
  have hnt := (completedEntire_eq_zero_iff_nontrivial ρ).mp hρ
  have hcz : completedEntire ((starRingEnd ℂ) ρ) = 0 := by
    rw [completedEntire_eq_zero_iff_nontrivial]
    exact ⟨riemannZeta_conj_eq_zero_of_zero hnt.1, by simpa using hnt.2.1, by simpa using hnt.2.2⟩
  have h1 := hmem ρ hρ ⟨him.1, by linarith [him.2]⟩
  have h2 := hmem _ hcz ⟨by simp; linarith [him.2], by simp; linarith [him.1]⟩
  have hne : ρ ≠ (starRingEnd ℂ) ρ := by
    intro h; have := congrArg Complex.im h; simp at this; linarith [him.2]
  have hsub : ({ρ, (starRingEnd ℂ) ρ} : Finset ℂ) ⊆ boxZeros σ₀ 2 (-t₁) T := by
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset (f := fun ρ => analyticOrderNatAt completedEntire ρ) hsub
  rw [Finset.sum_pair hne, hsum₁] at hle
  have := completedEntire_order_pos hρ
  have := completedEntire_order_pos hcz
  omega

/-- **Comptage d'une bande de hauteur `T` à valeur `K`** (logique, sans numérique). -/
theorem upperWindowOpen_count_of_boxes_K {σ₀ t₁ T : ℝ} {K : ℕ} (hσ₀ : 0 < σ₀) (hσ₀' : σ₀ < 1 / 2) (ht₁ : 0 < t₁)
    (ht₁T : t₁ < T)
    (hB₁ : ∀ s ∈ rectBoundary ((σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T : ℂ) * I), completedEntire s ≠ 0)
    (hB₂ : ∀ s ∈ rectBoundary (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) ((2 : ℝ) + T * I), completedEntire s ≠ 0)
    (hI₁ : (2 * (Real.pi : ℂ) * I)⁻¹ *
      rectBoundaryIntegral (logDeriv completedEntire) ((σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) ((2 : ℝ) + T * I) = K)
    (hI₂ : rectBoundaryIntegral (logDeriv completedEntire) (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I)
      ((2 : ℝ) + T * I) = 0)
    (hlow : ∀ ρ, completedEntire ρ = 0 → ρ.im ∈ Ioo (-t₁) 0 → False) :
    ∑ ρ ∈ upperWindowOpen T, zetaZeroMultiplicity ρ = K := by
  have hS₁ := box_order_sum (σa := σ₀) (σb := 2) (ta := -t₁) (tb := T) (by linarith) (by linarith) hB₁
  rw [hI₁] at hS₁
  have hsum₁ : ∑ ρ ∈ boxZeros σ₀ 2 (-t₁) T, analyticOrderNatAt completedEntire ρ = K := by exact_mod_cast hS₁.symm
  have hmem := box_strip_mem hσ₀ hσ₀' ht₁ ht₁T hB₂ hI₂
  have hwin : upperWindowOpen T = boxZeros σ₀ 2 (-t₁) T := by
    ext ρ
    constructor
    · intro hρ
      obtain ⟨hnt, h0, hT'⟩ := mem_upperWindowOpen.mp hρ
      exact hmem ρ ((completedEntire_eq_zero_iff_nontrivial ρ).mpr hnt) ⟨by linarith, hT'⟩
    · intro hρ
      obtain ⟨hz, -, him⟩ := mem_boxZeros.mp hρ
      have hnt := (completedEntire_eq_zero_iff_nontrivial ρ).mp hz
      refine mem_upperWindowOpen.mpr ⟨hnt, ?_, him.2⟩
      rcases lt_trichotomy ρ.im 0 with hi | hi | hi
      · exact (hlow ρ hz ⟨him.1, hi⟩).elim
      · exfalso
        have hs : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [hi])
        rw [hs] at hz; exact completedEntire_real_ne_zero _ hz
      · exact hi
  rw [hwin, ← hsum₁]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  obtain ⟨hz, -, -⟩ := mem_boxZeros.mp hρ
  have hnt := (completedEntire_eq_zero_iff_nontrivial ρ).mp hz
  have hi : ρ.im ≠ 0 := by
    intro h0
    have hs : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [h0])
    rw [hs] at hz; exact completedEntire_real_ne_zero _ hz
  exact (completedEntire_multiplicity hnt.1 hi).symm

/-- **Aucun zéro à la hauteur `T`**, depuis le bord supérieur de `B₁` : un zéro de partie réelle `≥ σ₀` est sur ce bord ;
sinon son miroir (partie réelle `> 1 − σ₀ > σ₀`, même hauteur) y est. -/
theorem no_zero_at_height_of_top {σ₀ t₁ T : ℝ} (hσ₀ : 0 < σ₀) (hσ₀' : σ₀ < 1 / 2) (ht₁T : -t₁ < T)
    (hZ₁ : ∀ s ∈ rectBoundary ((σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T : ℂ) * I), riemannZeta s ≠ 0) :
    ∀ ρ : ℂ, PIsNonTrivialZetaZero ρ → ρ.im ≠ T := by
  have htop : ∀ ρ : ℂ, riemannZeta ρ = 0 → σ₀ ≤ ρ.re → ρ.re ≤ 2 → ρ.im = T → False := by
    intro ρ hz h1 h2 hT
    apply hZ₁ ρ _ hz
    left
    refine ⟨Or.inr (by simp [hT]), ?_⟩
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self, add_zero]
    exact ⟨h1, h2⟩
  intro ρ hnt hT
  by_cases h : σ₀ ≤ ρ.re
  · exact htop ρ hnt.1 h (by linarith [hnt.2.2]) hT
  · have hm := mirrorPoint_nontrivial hnt
    exact htop _ hm.1 (by simp; linarith [hnt.2.2]) (by simp; linarith [hnt.2.1]) (by simp [hT])

/-- **Comptage fermé d'une bande de hauteur `T` depuis les rectangles de `ζ`** : `N(T) = K` dès que les bords de `B₁(T)`,
`B₂(T)` sont sans zéro de `ζ`, que l'enroulement de `(1 − s)ζ(s)` vaut `K` autour de `B₁(T)` et zéro autour de `B₂(T)`, et
que les rectangles de la première bande (`T₀`) donnent `1` et `0`. Aucune valeur de `Γ`. -/
theorem upperCount_of_zeta_boxes {σ₀ t₁ T₀ T : ℝ} {K : ℕ} (hσ₀ : 0 < σ₀) (hσ₀' : σ₀ < 1 / 2) (ht₁ : 0 < t₁)
    (ht₁T₀ : t₁ < T₀) (ht₁T : t₁ < T)
    (hZ₁₀ : ∀ s ∈ rectBoundary ((σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T₀ : ℂ) * I), riemannZeta s ≠ 0)
    (hZ₂₀ : ∀ s ∈ rectBoundary (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T₀ : ℂ) * I),
      riemannZeta s ≠ 0)
    (hW₁₀ : (2 * (Real.pi : ℂ) * I)⁻¹ * rectBoundaryIntegral (logDeriv (fun s => (1 - s) * riemannZeta s))
      ((σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T₀ : ℂ) * I) = 1)
    (hW₂₀ : rectBoundaryIntegral (logDeriv (fun s => (1 - s) * riemannZeta s))
      (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T₀ : ℂ) * I) = 0)
    (hZ₁ : ∀ s ∈ rectBoundary ((σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T : ℂ) * I), riemannZeta s ≠ 0)
    (hZ₂ : ∀ s ∈ rectBoundary (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T : ℂ) * I),
      riemannZeta s ≠ 0)
    (hW₁ : (2 * (Real.pi : ℂ) * I)⁻¹ * rectBoundaryIntegral (logDeriv (fun s => (1 - s) * riemannZeta s))
      ((σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T : ℂ) * I) = K)
    (hW₂ : rectBoundaryIntegral (logDeriv (fun s => (1 - s) * riemannZeta s))
      (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T : ℂ) * I) = 0) :
    upperCountWithMultiplicity T = K := by
  have hT₀ : 0 < T₀ := by linarith
  have hT : 0 < T := by linarith
  have e₁₀ := rectBoundaryIntegral_completedEntire_eq_zetaFactor
    (z := (σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (w := ((2 : ℝ) : ℂ) + (T₀ : ℂ) * I)
    (by simp; linarith) (by simp; linarith) (by simpa using hσ₀)
    (one_not_mem_rectBoundary (by linarith) ht₁ hT₀) hZ₁₀
  have e₂₀ := rectBoundaryIntegral_completedEntire_eq_zetaFactor
    (z := ((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (w := ((2 : ℝ) : ℂ) + (T₀ : ℂ) * I)
    (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (one_not_mem_rectBoundary (by linarith) ht₁ hT₀) hZ₂₀
  have e₁ := rectBoundaryIntegral_completedEntire_eq_zetaFactor
    (z := (σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (w := ((2 : ℝ) : ℂ) + (T : ℂ) * I)
    (by simp; linarith) (by simp; linarith) (by simpa using hσ₀)
    (one_not_mem_rectBoundary (by linarith) ht₁ hT) hZ₁
  have e₂ := rectBoundaryIntegral_completedEntire_eq_zetaFactor
    (z := ((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (w := ((2 : ℝ) : ℂ) + (T : ℂ) * I)
    (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (one_not_mem_rectBoundary (by linarith) ht₁ hT) hZ₂
  have hlow := box_no_lower_zero hσ₀ hσ₀' ht₁ ht₁T₀
    (fun s hs => completedEntire_ne_zero_of_zeta_ne_zero (hZ₁₀ s hs))
    (fun s hs => completedEntire_ne_zero_of_zeta_ne_zero (hZ₂₀ s hs))
    (by rw [e₁₀]; exact hW₁₀) (by rw [e₂₀]; exact hW₂₀)
  rw [upperCount_closed_eq_open_of_no_boundary (no_zero_at_height_of_top hσ₀ hσ₀' (by linarith) hZ₁)]
  exact upperWindowOpen_count_of_boxes_K hσ₀ hσ₀' ht₁ ht₁T
    (fun s hs => completedEntire_ne_zero_of_zeta_ne_zero (hZ₁ s hs))
    (fun s hs => completedEntire_ne_zero_of_zeta_ne_zero (hZ₂ s hs))
    (by rw [e₁]; exact hW₁) (by rw [e₂]; exact hW₂) hlow

#print axioms upperCount_of_zeta_boxes

end RHV6Fresh
