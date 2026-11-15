/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox.Side_b1bottom
import RHV6Fresh.Terminal.ZetaBox.Side_right
import RHV6Fresh.Terminal.ZetaBox.Side_b1top
import RHV6Fresh.Terminal.ZetaBox.Side_b1left
import RHV6Fresh.Terminal.ZetaBox.Side_b2bottom
import RHV6Fresh.Terminal.ZetaBox.Side_b2top
import RHV6Fresh.Terminal.ZetaBox.Side_b2left
/-!
# Certificat (V2), assemblage des deux rectangles

Fichier GENERE par `experiments/e192_zeta_box_certificate_generator.py` : constantes rationnelles calculees en
arithmetique exacte puis verifiees par Lean (`norm_num`, `linarith`, `decide`). Aucune preuve admise, aucun axiome ajoute.
-/

set_option maxHeartbeats 4000000
set_option linter.style.longLine false

namespace RHV6Fresh
namespace ZB
namespace Cert

open Complex Set

theorem box_b1_integral :
    rectBoundaryIntegral (logDeriv (fun s => (1 - s) * riemannZeta s)) (((1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I)
      (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I) = (((4):ℤ):ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  have hF : (fun s => (1 - s) * riemannZeta s) = zetaFactor := rfl
  rw [hF]
  unfold rectBoundaryIntegral
  have r1 : (((1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I).re = (1/4:ℝ) := by simp
  have r2 : (((1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I).im = (-1:ℝ) := by simp
  have r3 : (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I).re = (2:ℝ) := by simp
  have r4 : (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I).im = (15:ℝ) := by simp
  rw [r1, r2, r3, r4, side_b1bottom, side_b1top, side_right, side_b1left]
  have J1 := point_junction (-1) (-2) ((0):ℤ) ((0):ℤ) (((2:ℝ):ℂ) + ((-1:ℝ):ℂ) * I) (by decide) (by decide) (u1_bottom 2)
    (pc_b1bottom_3 2 ⟨by norm_num, by norm_num⟩) (u1_right (-1)) (pc_right_0 (-1) ⟨by norm_num, by norm_num⟩)
  have J2 := point_junction (-2) (-3) ((0):ℤ) ((0):ℤ) (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I) (by decide) (by decide) (u1_right 15)
    (pc_right_28 15 ⟨by norm_num, by norm_num⟩) (u1_top 2) (pc_b1top_6 2 ⟨by norm_num, by norm_num⟩)
  have J3 := point_junction (-3) (-4) ((-1):ℤ) ((-1):ℤ) (((1/4:ℝ):ℂ) + ((15:ℝ):ℂ) * I) (by decide) (by decide) (u1_top _)
    (pc_b1top_0 _ ⟨by norm_num, by norm_num⟩) (u1_left _ 15 (by norm_num)) (pc_b1left_76 15 ⟨by norm_num, by norm_num⟩)
  have hz4 : I ^ ((-1):ℤ) = I ^ ((-1):ℤ) := I_zpow_congr _ _ (0) (by norm_num)
  have J4 := point_junction (-4) (-5) ((-1):ℤ) ((-1):ℤ) (((1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I) (by decide) (by decide) (u1_left _ (-1) (by norm_num))
    (pc_b1left_0 (-1) ⟨by norm_num, by norm_num⟩) (u1_bottom' _)
    (by rw [hz4]; exact pc_b1bottom_0 _ ⟨by norm_num, by norm_num⟩)
  have e4 : I ^ (-5:ℤ) * I ^ ((-1):ℤ) = I ^ (-1:ℤ) * I ^ ((-1):ℤ) := by
    rw [hz4, I_zpow_congr (-5) (-1) (-1) (by norm_num)]
  rw [e4] at J4
  push_cast at J1 J2 J3 J4 ⊢
  linear_combination J1 + J2 + J3 + J4

theorem box_b1_nonvanishing :
    ∀ s ∈ rectBoundary (((1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I) (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I), riemannZeta s ≠ 0 := by
  intro s hs
  have r1 : (((1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I).re = (1/4:ℝ) := by simp
  have r2 : (((1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I).im = (-1:ℝ) := by simp
  have r3 : (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I).re = (2:ℝ) := by simp
  have r4 : (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I).im = (15:ℝ) := by simp
  unfold rectBoundary at hs
  rw [r1, r2, r3, r4] at hs
  rcases hs with ⟨h | h, hre⟩ | ⟨h | h, him⟩
  · have e : s = ((s.re:ℝ):ℂ) + ((-1:ℝ):ℂ) * I := by apply Complex.ext <;> simp [h]
    rw [e]; exact nz_b1bottom s.re hre
  · have e : s = ((s.re:ℝ):ℂ) + ((15:ℝ):ℂ) * I := by apply Complex.ext <;> simp [h]
    rw [e]; exact nz_b1top s.re hre
  · have e : s = (((1/4:ℝ)):ℂ) + ((s.im:ℝ):ℂ) * I := by apply Complex.ext <;> simp [h]
    rw [e]; exact nz_b1left s.im him
  · have e : s = ((2:ℝ):ℂ) + ((s.im:ℝ):ℂ) * I := by apply Complex.ext <;> simp [h]
    rw [e]; exact nz_right s.im him

theorem box_b2_integral :
    rectBoundaryIntegral (logDeriv (fun s => (1 - s) * riemannZeta s)) (((1 - 1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I)
      (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I) = (((0):ℤ):ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  have hF : (fun s => (1 - s) * riemannZeta s) = zetaFactor := rfl
  rw [hF]
  unfold rectBoundaryIntegral
  have r1 : (((1 - 1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I).re = (1 - 1/4:ℝ) := by simp
  have r2 : (((1 - 1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I).im = (-1:ℝ) := by simp
  have r3 : (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I).re = (2:ℝ) := by simp
  have r4 : (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I).im = (15:ℝ) := by simp
  rw [r1, r2, r3, r4, side_b2bottom, side_b2top, side_right, side_b2left]
  have J1 := point_junction (-1) (-2) ((0):ℤ) ((0):ℤ) (((2:ℝ):ℂ) + ((-1:ℝ):ℂ) * I) (by decide) (by decide) (u1_bottom 2)
    (pc_b2bottom_2 2 ⟨by norm_num, by norm_num⟩) (u1_right (-1)) (pc_right_0 (-1) ⟨by norm_num, by norm_num⟩)
  have J2 := point_junction (-2) (-3) ((0):ℤ) ((0):ℤ) (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I) (by decide) (by decide) (u1_right 15)
    (pc_right_28 15 ⟨by norm_num, by norm_num⟩) (u1_top 2) (pc_b2top_2 2 ⟨by norm_num, by norm_num⟩)
  have J3 := point_junction (-3) (-4) ((-1):ℤ) ((-1):ℤ) (((1 - 1/4:ℝ):ℂ) + ((15:ℝ):ℂ) * I) (by decide) (by decide) (u1_top _)
    (pc_b2top_0 _ ⟨by norm_num, by norm_num⟩) (u1_left _ 15 (by norm_num)) (pc_b2left_40 15 ⟨by norm_num, by norm_num⟩)
  have hz4 : I ^ ((3):ℤ) = I ^ ((-1):ℤ) := I_zpow_congr _ _ (1) (by norm_num)
  have J4 := point_junction (-4) (-5) ((3):ℤ) ((3):ℤ) (((1 - 1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I) (by decide) (by decide) (u1_left _ (-1) (by norm_num))
    (pc_b2left_0 (-1) ⟨by norm_num, by norm_num⟩) (u1_bottom' _)
    (by rw [hz4]; exact pc_b2bottom_0 _ ⟨by norm_num, by norm_num⟩)
  have e4 : I ^ (-5:ℤ) * I ^ ((3):ℤ) = I ^ (-1:ℤ) * I ^ ((-1):ℤ) := by
    rw [hz4, I_zpow_congr (-5) (-1) (-1) (by norm_num)]
  rw [e4] at J4
  push_cast at J1 J2 J3 J4 ⊢
  linear_combination J1 + J2 + J3 + J4

theorem box_b2_nonvanishing :
    ∀ s ∈ rectBoundary (((1 - 1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I) (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I), riemannZeta s ≠ 0 := by
  intro s hs
  have r1 : (((1 - 1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I).re = (1 - 1/4:ℝ) := by simp
  have r2 : (((1 - 1/4:ℝ):ℂ) + ((-1:ℝ):ℂ) * I).im = (-1:ℝ) := by simp
  have r3 : (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I).re = (2:ℝ) := by simp
  have r4 : (((2:ℝ):ℂ) + ((15:ℝ):ℂ) * I).im = (15:ℝ) := by simp
  unfold rectBoundary at hs
  rw [r1, r2, r3, r4] at hs
  rcases hs with ⟨h | h, hre⟩ | ⟨h | h, him⟩
  · have e : s = ((s.re:ℝ):ℂ) + ((-1:ℝ):ℂ) * I := by apply Complex.ext <;> simp [h]
    rw [e]; exact nz_b2bottom s.re hre
  · have e : s = ((s.re:ℝ):ℂ) + ((15:ℝ):ℂ) * I := by apply Complex.ext <;> simp [h]
    rw [e]; exact nz_b2top s.re hre
  · have e : s = (((1 - 1/4:ℝ)):ℂ) + ((s.im:ℝ):ℂ) * I := by apply Complex.ext <;> simp [h]
    rw [e]; exact nz_b2left s.im him
  · have e : s = ((2:ℝ):ℂ) + ((s.im:ℝ):ℂ) * I := by apply Complex.ext <;> simp [h]
    rw [e]; exact nz_right s.im him

/-- **Certificat (V2)** : non-annulation de `ζ` sur les bords de `B₁ = [1/4, 2] × [−1, 15]` et `B₂ = [3/4, 2] × [−1, 15]`,
enroulement un de `(1 − s)ζ(s)` autour de `B₁`, zéro autour de `B₂`. -/
theorem zeta_box_certificate :
    (∀ s ∈ rectBoundary (((1 / 4 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + ((15 : ℝ) : ℂ) * I),
        riemannZeta s ≠ 0) ∧
    (∀ s ∈ rectBoundary (((1 - 1 / 4 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + ((15 : ℝ) : ℂ) * I),
        riemannZeta s ≠ 0) ∧
    (2 * (Real.pi : ℂ) * I)⁻¹ * rectBoundaryIntegral (logDeriv (fun s => (1 - s) * riemannZeta s))
        (((1 / 4 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + ((15 : ℝ) : ℂ) * I) = 1 ∧
    rectBoundaryIntegral (logDeriv (fun s => (1 - s) * riemannZeta s))
        (((1 - 1 / 4 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + ((15 : ℝ) : ℂ) * I) = 0 := by
  refine ⟨box_b1_nonvanishing, box_b2_nonvanishing, ?_, ?_⟩
  · rw [box_b1_integral]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    push_cast
    ring
  · rw [box_b2_integral]; simp

end Cert
end ZB
end RHV6Fresh

#print axioms RHV6Fresh.ZB.Cert.zeta_box_certificate
