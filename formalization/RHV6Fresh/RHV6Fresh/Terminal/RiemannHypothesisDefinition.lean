/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.Universalization

/-!
# Définition de `RiemannHypothesis` (Mathlib) contre la définition classique

Mathlib (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`) :
`RiemannHypothesis := ∀ s, ζ s = 0 → (¬ ∃ n : ℕ, s = −2(n + 1)) → s ≠ 1 → s.re = 1/2`.
Définition classique : tout zéro de `ζ` dans la bande ouverte `0 < Re s < 1` est sur la ligne. Les deux sont équivalentes
(fermé ci-dessous, par `thm_inOpenStrip_of_mathlibHypotheses` de rhv3_lean : un zéro non trivial au sens de Mathlib est
dans la bande ouverte). Aucune définition nouvelle, aucune hypothèse : la définition de Mathlib est la définition usuelle,
ni plus faible ni plus forte.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **La définition de Mathlib est la définition classique** : `RiemannHypothesis` ⟺ tout zéro de `ζ` de la bande
ouverte a la partie réelle `1/2`. Fermé, axiomes standard. -/
theorem riemannHypothesis_iff_strip :
    RiemannHypothesis ↔ ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2 := by
  constructor
  · intro hRH ρ hz h0 h1
    refine hRH ρ hz ?_ ?_
    · rintro ⟨n, rfl⟩
      have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      rw [this] at h0
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · rintro rfl; simp at h1
  · intro h s hz hnt _
    obtain ⟨h0, h1⟩ := thm_inOpenStrip_of_mathlibHypotheses hz hnt
    exact h s hz h0 h1

#print axioms riemannHypothesis_iff_strip

end RHV6Fresh
