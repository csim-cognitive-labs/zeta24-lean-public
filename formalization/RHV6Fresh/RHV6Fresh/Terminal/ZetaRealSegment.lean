/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.AnchorContour
import RHV3Lean.Objects.ZetaRealSegment

/-!
# Lemme (1) de la certification de l'ancre : non-annulation de `ζ` sur le segment réel `(0, 1)`

Réutilisation de `RHV3Lean.thm_noRealZetaZeroInOpenUnitSegment` (base `rhv3_lean`, borne de Mellin
explicite du noyau thêta : `‖Λ₀(σ)‖ < 4 ≤ 1/σ + 1/(1−σ)`). Aucune hypothèse, axiomes standard.
Conséquence : `ξ₁` ne s'annule en aucun point réel (`completedEntire_real_ne_zero`), ce qui ferme le
segment réel du contour `[−1, 2] × [0, T]`.
-/

namespace RHV6Fresh

open RHV3Lean Complex

/-- **Lemme (1)** : `ζ(σ) ≠ 0` pour `0 < σ < 1`. -/
theorem riemannZeta_real_ne_zero_of_mem_Ioo (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta σ ≠ 0 := fun h =>
  thm_noRealZetaZeroInOpenUnitSegment (σ : ℂ) h (by simpa using h0) (by simpa using h1)
    (by simp)

/-- `ξ₁(σ) ≠ 0` pour tout réel `σ` : le segment réel du contour est sans zéro. -/
theorem completedEntire_real_ne_zero (σ : ℝ) : completedEntire σ ≠ 0 :=
  completedEntire_real_ne_zero_of_zeta_ne_zero riemannZeta_real_ne_zero_of_mem_Ioo σ

#print axioms riemannZeta_real_ne_zero_of_mem_Ioo
#print axioms completedEntire_real_ne_zero

end RHV6Fresh
