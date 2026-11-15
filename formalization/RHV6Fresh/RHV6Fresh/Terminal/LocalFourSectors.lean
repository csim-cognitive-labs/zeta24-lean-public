/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PairInteraction

/-!
# RHV6Fresh — les quatre secteurs autour d'un centre sur l'axe critique (auteur, 2026-10-03)

Énoncé de l'auteur : une Tour en ligne est centrée sur le point de l'axe critique à sa hauteur, et sa géométrie est
coupée en quatre secteurs symétriques par l'axe critique et l'axe arithmétique (l'horizontale à cette hauteur).

Deux plans sont à distinguer. Dans le plan des valeurs, toute Tour s'enroule autour de l'origine (E160). Dans le plan
des membres, le centre est le point de l'axe critique à la hauteur considérée, et les écarts sont lus en `w = s − c`.
La seule symétrie exacte qui conserve la hauteur est la réflexion `s ↦ 1 − s̄`, soit `w ↦ −w̄` : réflexion par l'axe
critique. La réflexion par l'horizontale (`w ↦ w̄`) n'est pas une symétrie de zêta : la conjugaison envoie la hauteur
`T` en `−T`.

* **Classement local** (§1) : toute configuration de deux membres invariante par la réflexion de l'axe critique est soit
  une paire miroir (`w₂ = −w̄₁`), soit deux membres sur l'axe critique ; recentrée en son milieu, elle vaut `±u` avec
  `u²` réel (`pair_offset_sq_real`) : `u² ≥ 0` pour la paire miroir (axe arithmétique, continuation radiale),
  `u² ≤ 0` pour deux membres sur l'axe critique (continuation verticale) (`mirror_pair_offset_sq_nonneg`,
  `axis_pair_offset_sq_nonpos`). Le facteur local `w² − u²` est donc réel en `w` et sa configuration est invariante par
  les deux réflexions et par la symétrie centrale (`local_four_sector_symmetry`) : la symétrie à quatre secteurs est
  automatique pour toute paire, en ligne ou non.
* **Le centre ne choisit pas l'axe** (§2) : les deux continuations du double ont le même centre, la même symétrie à
  quatre secteurs, et ne diffèrent que par l'axe qui porte la paire (`continuations_same_center`).

Borne : la symétrie à quatre secteurs est vraie dans tout monde qui a la réflexion par l'axe critique, monde décalé
compris ; elle classe la configuration, elle ne sélectionne pas l'axe. Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Complex

/-! ## 1. Classement local d'une paire invariante par la réflexion de l'axe critique -/

/-- **Une paire invariante par la réflexion de l'axe critique a un écart dont le carré est réel.** -/
theorem pair_offset_sq_real (w₁ w₂ : ℂ)
    (h : w₂ = -(starRingEnd ℂ) w₁ ∨ (w₁.re = 0 ∧ w₂.re = 0)) : (((w₁ - w₂) / 2) ^ 2).im = 0 := by
  rcases h with h | ⟨h1, h2⟩
  · subst h; simp [sq, Complex.mul_im]
  · simp [sq, Complex.mul_im, h1, h2]

/-- **Paire miroir** (`w₂ = −w̄₁`) : écart sur l'axe arithmétique, carré `≥ 0`. -/
theorem mirror_pair_offset_sq_nonneg (w₁ : ℂ) :
    0 ≤ (((w₁ - -(starRingEnd ℂ) w₁) / 2) ^ 2).re := by
  have : (w₁ - -(starRingEnd ℂ) w₁) / 2 = ((w₁.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [this, ← Complex.ofReal_pow, Complex.ofReal_re]; positivity

/-- **Deux membres sur l'axe critique** : écart sur l'axe critique, carré `≤ 0`. -/
theorem axis_pair_offset_sq_nonpos (w₁ w₂ : ℂ) (h1 : w₁.re = 0) (h2 : w₂.re = 0) :
    (((w₁ - w₂) / 2) ^ 2).re ≤ 0 := by
  simp [sq, Complex.mul_re, h1, h2]
  nlinarith [sq_nonneg (w₁.im - w₂.im)]

/-- **Symétrie à quatre secteurs** : si `u²` est réel, la paire recentrée `{u, −u}` est invariante par la réflexion
de l'axe critique (`w ↦ −w̄`), par celle de l'axe arithmétique (`w ↦ w̄`) et par la symétrie centrale. -/
theorem local_four_sector_symmetry (u : ℂ) (hu : (u ^ 2).im = 0) :
    ((starRingEnd ℂ) u = u ∨ (starRingEnd ℂ) u = -u) ∧
      (-(starRingEnd ℂ) u = u ∨ -(starRingEnd ℂ) u = -u) := by
  have h : u.re * u.im = 0 := by
    have : (u ^ 2).im = 2 * (u.re * u.im) := by simp [sq, Complex.mul_im]; ring
    linarith
  rcases mul_eq_zero.1 h with hr | hi
  · have hc : (starRingEnd ℂ) u = -u := by apply Complex.ext <;> simp [hr]
    exact ⟨Or.inr hc, Or.inl (by rw [hc, neg_neg])⟩
  · have hc : (starRingEnd ℂ) u = u := by apply Complex.ext <;> simp [hi]
    exact ⟨Or.inl hc, Or.inr (by rw [hc])⟩

#print axioms pair_offset_sq_real
#print axioms mirror_pair_offset_sq_nonneg
#print axioms axis_pair_offset_sq_nonpos
#print axioms local_four_sector_symmetry

/-! ## 2. Le centre ne choisit pas l'axe -/

/-- **Les deux continuations du double ont le même centre** `1/2 + iT` : la paire radiale est `c ± d`, la paire
verticale `c ± ih` ; elles ne diffèrent que par l'axe, c'est-à-dire par le signe du carré de l'écart. -/
theorem continuations_same_center (T d h : ℝ) :
    (mirrorPoint T d + mirrorPoint T (-d)) / 2 = mirrorPoint T 0 ∧
      (mirrorPoint (T + h) 0 + mirrorPoint (T - h) 0) / 2 = mirrorPoint T 0 ∧
      ((mirrorPoint T d - mirrorPoint T (-d)) / 2) ^ 2 = ((d ^ 2 : ℝ) : ℂ) ∧
      ((mirrorPoint (T + h) 0 - mirrorPoint (T - h) 0) / 2) ^ 2 = ((-h ^ 2 : ℝ) : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · unfold mirrorPoint; push_cast; ring_nf; try simp [Complex.I_sq]; try ring

#print axioms continuations_same_center

end RHV6Fresh
