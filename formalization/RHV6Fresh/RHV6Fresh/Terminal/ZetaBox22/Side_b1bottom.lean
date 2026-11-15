/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Side_b1bottom_c0
/-!
# Certificat (V2), côté b1bottom (b1)

Fichier GENERE par `experiments/e192_zeta_box_certificate_generator.py` : constantes rationnelles calculees en
arithmetique exacte puis verifiees par Lean (`norm_num`, `linarith`, `decide`). Aucune preuve admise, aucun axiome ajoute.
-/

set_option maxHeartbeats 4000000
set_option linter.style.longLine false

namespace RHV6Fresh
namespace ZB
namespace Cert
namespace H22

open Complex Set

def xL_b1bottom : List ℤ := [8, 17, 30, 48, 64]
def zL_b1bottom : List ℤ := [-1, -1, -1, 0]
noncomputable def xF_b1bottom (k : ℕ) : ℝ := ((xL_b1bottom.getD k 0 : ℤ) : ℝ) / 32
def zF_b1bottom (k : ℕ) : ℤ := zL_b1bottom.getD k 0

set_option maxRecDepth 100000 in
theorem side_b1bottom : ∫ t in (1/4:ℝ)..(2:ℝ), logDeriv zetaFactor ((t:ℂ) + ((-1:ℝ):ℂ) * I) =
    log (I ^ ((-1):ℤ) * I ^ ((0):ℤ) * zetaFactor ((((2:ℝ)):ℂ) + ((-1:ℝ):ℂ) * I)) -
      log (I ^ ((-1):ℤ) * I ^ ((-1):ℤ) * zetaFactor ((((1/4:ℝ)):ℂ) + ((-1:ℝ):ℂ) * I)) -
      ((((0) - (-1) : ℤ)) : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  have h := horizontal_side (-1:ℝ) (by norm_num) xF_b1bottom zF_b1bottom (-1) 3 (list_mono xL_b1bottom 32 (by norm_num) 4 (by decide)) (by decide) (fun t _ => u1_bottom t)
    (fun k hk => by interval_cases k; exacts [pc_b1bottom_0, pc_b1bottom_1, pc_b1bottom_2, pc_b1bottom_3])
  have e0 : xF_b1bottom 0 = 1/4 := by norm_num [xF_b1bottom, xL_b1bottom]
  have e1 : xF_b1bottom (3 + 1) = 2 := by norm_num [xF_b1bottom, xL_b1bottom]
  have f0 : zF_b1bottom 0 = -1 := rfl
  have f1 : zF_b1bottom 3 = 0 := rfl
  rw [e0, e1, f0, f1] at h
  exact h

set_option maxRecDepth 100000 in
theorem nz_b1bottom : ∀ t ∈ Set.Icc (1/4:ℝ) (2:ℝ), riemannZeta ((t:ℂ) + ((-1:ℝ):ℂ) * I) ≠ 0 := by
  have h := cover xF_b1bottom (fun t => riemannZeta ((t:ℂ) + ((-1:ℝ):ℂ) * I) ≠ 0) 3 (list_mono xL_b1bottom 32 (by norm_num) 4 (by decide))
    (fun k hk t ht => by interval_cases k; exacts [zeta_ne_of_re_pos (pc_b1bottom_0 t ht), zeta_ne_of_re_pos (pc_b1bottom_1 t ht), zeta_ne_of_re_pos (pc_b1bottom_2 t ht), zeta_ne_of_re_pos (pc_b1bottom_3 t ht)])
  have e0 : xF_b1bottom 0 = 1/4 := by norm_num [xF_b1bottom, xL_b1bottom]
  have e1 : xF_b1bottom (3 + 1) = 2 := by norm_num [xF_b1bottom, xL_b1bottom]
  rw [e0, e1] at h
  exact h

end H22
end Cert
end ZB
end RHV6Fresh
