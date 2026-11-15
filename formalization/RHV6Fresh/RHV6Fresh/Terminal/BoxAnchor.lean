/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.BoxCount
import RHV6Fresh.Terminal.CountingDeficit

/-!
# Comptage de la première bande par deux rectangles (vérification (V2) sans Γ)

Deux rectangles du demi-plan `Re > 0` : `B₁ = [σ₀, 2] × [−t₁, 15]` et `B₂ = [1 − σ₀, 2] × [−t₁, 15]`, `0 < σ₀ < 1/2`,
`0 < t₁ < 15`. Si `ξ₁` ne s'annule pas sur leurs bords et si `(2πi)⁻¹∮_{B₁} ξ₁′/ξ₁ = 1`, `∮_{B₂} ξ₁′/ξ₁ = 0`, alors, par le
miroir `ρ ↦ 1 − ρ̄`, la conjugaison et les multiplicités, la fenêtre ouverte `0 < Im ρ < 15` contient exactement un zéro,
simple : `Σ_{upperWindowOpen 15} m(ρ) = 1`. Par `rectBoundaryIntegral_completedEntire_eq_zetaFactor` (BoxCount), les deux
intégrales ne lisent que `(1 − s)ζ(s)`, aucune valeur de `Γ`.
-/

namespace RHV6Fresh

open Complex Set RHV3Lean

/-- Les zéros de `ξ₁` sont exactement les zéros non triviaux de `ζ`. -/
theorem completedEntire_eq_zero_iff_nontrivial (s : ℂ) :
    completedEntire s = 0 ↔ PIsNonTrivialZetaZero s := by
  constructor
  · intro h
    rcases lt_trichotomy s.im 0 with hi | hi | hi
    · have hz := (completedEntire_eq_zero_iff hi.ne).mp h
      have hc : riemannZeta ((starRingEnd ℂ) s) = 0 := riemannZeta_conj_eq_zero_of_zero hz
      have hnt := nontrivial_of_zero_im_pos hc (by simp; linarith)
      exact ⟨hz, by simpa using hnt.2.1, by simpa using hnt.2.2⟩
    · exfalso
      have hs : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [hi])
      rw [hs] at h; exact completedEntire_real_ne_zero _ h
    · exact nontrivial_of_zero_im_pos ((completedEntire_eq_zero_iff hi.ne').mp h) hi
  · intro h
    have hi : s.im ≠ 0 := by
      intro h0
      have hs : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [h0])
      have := h.1; rw [hs] at this
      exact riemannZeta_real_ne_zero_of_mem_Ioo s.re h.2.1 h.2.2 this
    exact (completedEntire_eq_zero_iff hi).mpr h.1

/-- Les zéros de `ξ₁` dans un rectangle ouvert borné, en ensemble fini. -/
noncomputable def boxZeros (σa σb ta tb : ℝ) : Finset ℂ :=
  (finsetSymmetricZeroWindow (|ta| + |tb|)).filter fun ρ => ρ.re ∈ Ioo σa σb ∧ ρ.im ∈ Ioo ta tb

theorem mem_boxZeros {σa σb ta tb : ℝ} {ρ : ℂ} :
    ρ ∈ boxZeros σa σb ta tb ↔ completedEntire ρ = 0 ∧ ρ.re ∈ Ioo σa σb ∧ ρ.im ∈ Ioo ta tb := by
  unfold boxZeros
  rw [Finset.mem_filter, thm_mem_finsetSymmetricZeroWindow, completedEntire_eq_zero_iff_nontrivial]
  constructor
  · rintro ⟨⟨h, -⟩, h2⟩; exact ⟨h, h2⟩
  · rintro ⟨h, h2, h3⟩
    refine ⟨⟨h, ?_⟩, h2, h3⟩
    rcases abs_cases ρ.im with ⟨h4, -⟩ | ⟨h4, -⟩ <;>
      cases abs_cases ta <;> cases abs_cases tb <;> linarith [h3.1, h3.2]

theorem completedEntire_order_pos {ρ : ℂ} (h : completedEntire ρ = 0) : 1 ≤ analyticOrderNatAt completedEntire ρ := by
  have hnt := (completedEntire_eq_zero_iff_nontrivial ρ).mp h
  have hi : ρ.im ≠ 0 := by
    intro h0
    have hs : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [h0])
    rw [hs] at h; exact completedEntire_real_ne_zero _ h
  rw [completedEntire_multiplicity hnt.1 hi]
  exact zetaZeroMultiplicity_pos hnt.1

/-- Principe de l'argument sur un rectangle sans zéro au bord, en somme d'ordres (forme normalisée). -/
theorem box_order_sum {σa σb ta tb : ℝ} (hre : σa < σb) (him : ta < tb)
    (hB : ∀ s ∈ rectBoundary ((σa : ℂ) + ta * I) ((σb : ℂ) + tb * I), completedEntire s ≠ 0) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
        rectBoundaryIntegral (logDeriv completedEntire) ((σa : ℂ) + ta * I) ((σb : ℂ) + tb * I) =
      ((∑ ρ ∈ boxZeros σa σb ta tb, analyticOrderNatAt completedEntire ρ : ℕ) : ℂ) := by
  have hre' : ((σa : ℂ) + ta * I).re < ((σb : ℂ) + tb * I).re := by simpa using hre
  have him' : ((σa : ℂ) + ta * I).im < ((σb : ℂ) + tb * I).im := by simpa using him
  have hZ : ∀ s, s ∈ boxZeros σa σb ta tb ↔ (completedEntire s = 0 ∧
      s.re ∈ Ioo ((σa : ℂ) + ta * I).re ((σb : ℂ) + tb * I).re ∧
      s.im ∈ Ioo ((σa : ℂ) + ta * I).im ((σb : ℂ) + tb * I).im) := by
    intro s; rw [mem_boxZeros]; simp
  have h := argument_principle_rect completedEntire differentiable_completedEntire hre' him'
    (boxZeros σa σb ta tb) hZ (fun ρ _ => completedEntire_analyticOrderAt_ne_top ρ) hB
  rw [h]
  have h2π : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ h2π, one_mul]
  push_cast; rfl

/-- **Comptage de la première bande par deux rectangles** (logique, sans numérique). -/
theorem upperWindowOpen_count_of_boxes {σ₀ t₁ T : ℝ} (hσ₀ : 0 < σ₀) (hσ₀' : σ₀ < 1 / 2) (ht₁ : 0 < t₁)
    (ht₁T : t₁ < T)
    (hB₁ : ∀ s ∈ rectBoundary ((σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T : ℂ) * I), completedEntire s ≠ 0)
    (hB₂ : ∀ s ∈ rectBoundary (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) ((2 : ℝ) + T * I), completedEntire s ≠ 0)
    (hI₁ : (2 * (Real.pi : ℂ) * I)⁻¹ *
      rectBoundaryIntegral (logDeriv completedEntire) ((σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) ((2 : ℝ) + T * I) = 1)
    (hI₂ : rectBoundaryIntegral (logDeriv completedEntire) (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) ((2 : ℝ) + T * I) = 0) :
    ∑ ρ ∈ upperWindowOpen T, zetaZeroMultiplicity ρ = 1 := by
  have hS₁ := box_order_sum (σa := σ₀) (σb := 2) (ta := -t₁) (tb := T) (by linarith) (by linarith) hB₁
  rw [hI₁] at hS₁
  have hsum₁ : ∑ ρ ∈ boxZeros σ₀ 2 (-t₁) T, analyticOrderNatAt completedEntire ρ = 1 := by exact_mod_cast hS₁.symm
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
  -- (c1) tout zéro de hauteur dans `]−t₁, T[` a une partie réelle `< 1 − σ₀`
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
  -- (c2) tout zéro de hauteur dans `]−t₁, T[` est dans `B₁`
  have hc2 : ∀ ρ, completedEntire ρ = 0 → ρ.im ∈ Ioo (-t₁) T → ρ ∈ boxZeros σ₀ 2 (-t₁) T := by
    intro ρ hρ him
    have hnt := (completedEntire_eq_zero_iff_nontrivial ρ).mp hρ
    have hm := mirrorPoint_nontrivial hnt
    have hmz : completedEntire (1 - (starRingEnd ℂ) ρ) = 0 :=
      (completedEntire_eq_zero_iff_nontrivial _).mpr hm
    have hmim : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by simp
    have := hc1 _ hmz (by rw [hmim]; exact him)
    simp at this
    exact mem_boxZeros.mpr ⟨hρ, ⟨by linarith, by linarith [hnt.2.2]⟩, him⟩
  -- `B₁` contient exactement un zéro, d'ordre un
  have hpos : ∀ ρ ∈ boxZeros σ₀ 2 (-t₁) T, 1 ≤ analyticOrderNatAt completedEntire ρ :=
    fun ρ hρ => completedEntire_order_pos (mem_boxZeros.mp hρ).1
  have hcard : (boxZeros σ₀ 2 (-t₁) T).card ≤ 1 := by
    have := Finset.card_nsmul_le_sum (boxZeros σ₀ 2 (-t₁) T)
      (fun ρ => analyticOrderNatAt completedEntire ρ) 1 hpos
    rw [hsum₁] at this; simpa using this
  have hne : (boxZeros σ₀ 2 (-t₁) T).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; rw [h, Finset.sum_empty] at hsum₁; exact zero_ne_one hsum₁
  obtain ⟨ρ₀, hρ₀⟩ := Finset.card_eq_one.mp (le_antisymm hcard (Finset.card_pos.mpr hne))
  rw [hρ₀, Finset.sum_singleton] at hsum₁
  have hρ₀mem : ρ₀ ∈ boxZeros σ₀ 2 (-t₁) T := by rw [hρ₀]; exact Finset.mem_singleton_self _
  obtain ⟨hz₀, hre₀, him₀⟩ := mem_boxZeros.mp hρ₀mem
  have hnt₀ := (completedEntire_eq_zero_iff_nontrivial ρ₀).mp hz₀
  -- `ρ₀` est au-dessus de l'axe réel (sinon son conjugué serait un second zéro dans `B₁`)
  have himpos : 0 < ρ₀.im := by
    rcases lt_trichotomy ρ₀.im 0 with hi | hi | hi
    · exfalso
      have hcz : completedEntire ((starRingEnd ℂ) ρ₀) = 0 := by
        rw [completedEntire_eq_zero_iff_nontrivial]
        exact ⟨riemannZeta_conj_eq_zero_of_zero hnt₀.1, by simpa using hnt₀.2.1, by simpa using hnt₀.2.2⟩
      have hcmem : (starRingEnd ℂ) ρ₀ ∈ boxZeros σ₀ 2 (-t₁) T :=
        mem_boxZeros.mpr ⟨hcz, by simpa using hre₀, ⟨by simp; linarith, by simp; linarith [him₀.1, ht₁T]⟩⟩
      rw [hρ₀, Finset.mem_singleton] at hcmem
      have := congrArg Complex.im hcmem
      simp at this; linarith
    · exfalso
      have hs : ρ₀ = (ρ₀.re : ℂ) := Complex.ext (by simp) (by simp [hi])
      rw [hs] at hz₀; exact completedEntire_real_ne_zero _ hz₀
    · exact hi
  -- la fenêtre ouverte est `{ρ₀}`
  have hwin : upperWindowOpen T = {ρ₀} := by
    ext ρ
    rw [Finset.mem_singleton]
    constructor
    · intro hρ
      obtain ⟨hnt, h0, hT'⟩ := mem_upperWindowOpen.mp hρ
      have hz : completedEntire ρ = 0 := (completedEntire_eq_zero_iff_nontrivial ρ).mpr hnt
      have := hc2 ρ hz ⟨by linarith, hT'⟩
      rw [hρ₀, Finset.mem_singleton] at this; exact this
    · rintro rfl
      exact mem_upperWindowOpen.mpr ⟨hnt₀, himpos, him₀.2⟩
  rw [hwin, Finset.sum_singleton, ← completedEntire_multiplicity hnt₀.1 himpos.ne', hsum₁]

#print axioms upperWindowOpen_count_of_boxes

/-- Sur le bord d'un rectangle, `ζ ≠ 0` entraîne `ξ₁ ≠ 0` (hors de l'axe réel par la factorisation, sur l'axe réel par
`completedEntire_real_ne_zero`). -/
theorem completedEntire_ne_zero_of_zeta_ne_zero {s : ℂ} (h : riemannZeta s ≠ 0) : completedEntire s ≠ 0 := by
  by_cases hi : s.im = 0
  · have hs : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [hi])
    rw [hs]; exact completedEntire_real_ne_zero _
  · exact fun h0 => h ((completedEntire_eq_zero_iff hi).mp h0)

theorem one_not_mem_rectBoundary {σa t₁ T : ℝ} (hσa : σa ≠ 1) (ht₁ : 0 < t₁) (hT : 0 < T) :
    (1 : ℂ) ∉ rectBoundary ((σa : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T : ℂ) * I) := by
  rintro (⟨h1, -⟩ | ⟨h1, -⟩)
  · rcases h1 with h | h <;> simp at h <;> linarith
  · rcases h1 with h | h
    · simp at h; exact hσa h.symm
    · simp at h

/-- **Comptage de la fenêtre ouverte par l'enroulement de `(1 − s)ζ(s)` seul** (aucune valeur de `Γ`) : fermé. -/
theorem upperWindowOpen_count_of_zeta_boxes {σ₀ t₁ T : ℝ} (hσ₀ : 0 < σ₀) (hσ₀' : σ₀ < 1 / 2) (ht₁ : 0 < t₁)
    (ht₁T : t₁ < T)
    (hZ₁ : ∀ s ∈ rectBoundary ((σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T : ℂ) * I), riemannZeta s ≠ 0)
    (hZ₂ : ∀ s ∈ rectBoundary (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T : ℂ) * I),
      riemannZeta s ≠ 0)
    (hW₁ : (2 * (Real.pi : ℂ) * I)⁻¹ * rectBoundaryIntegral (logDeriv (fun s => (1 - s) * riemannZeta s))
      ((σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T : ℂ) * I) = 1)
    (hW₂ : rectBoundaryIntegral (logDeriv (fun s => (1 - s) * riemannZeta s))
      (((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + (T : ℂ) * I) = 0) :
    ∑ ρ ∈ upperWindowOpen T, zetaZeroMultiplicity ρ = 1 := by
  have hT : 0 < T := by linarith
  have e₁ := rectBoundaryIntegral_completedEntire_eq_zetaFactor
    (z := (σ₀ : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (w := ((2 : ℝ) : ℂ) + (T : ℂ) * I)
    (by simp; linarith) (by simp; linarith) (by simpa using hσ₀)
    (one_not_mem_rectBoundary (by linarith) ht₁ hT) hZ₁
  have e₂ := rectBoundaryIntegral_completedEntire_eq_zetaFactor
    (z := ((1 - σ₀ : ℝ) : ℂ) + ((-t₁ : ℝ) : ℂ) * I) (w := ((2 : ℝ) : ℂ) + (T : ℂ) * I)
    (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (one_not_mem_rectBoundary (by linarith) ht₁ hT) hZ₂
  exact upperWindowOpen_count_of_boxes hσ₀ hσ₀' ht₁ ht₁T
    (fun s hs => completedEntire_ne_zero_of_zeta_ne_zero (hZ₁ s hs))
    (fun s hs => completedEntire_ne_zero_of_zeta_ne_zero (hZ₂ s hs))
    (by rw [e₁]; exact hW₁) (by rw [e₂]; exact hW₂)

#print axioms upperWindowOpen_count_of_zeta_boxes

end RHV6Fresh
