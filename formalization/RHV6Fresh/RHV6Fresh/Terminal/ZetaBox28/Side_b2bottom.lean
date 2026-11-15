/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Side_b2bottom_c0
/-!
# Certificat (V2), côté b2bottom (b2)

Fichier GENERE par `experiments/e192_zeta_box_certificate_generator.py` : constantes rationnelles calculees en
arithmetique exacte puis verifiees par Lean (`norm_num`, `linarith`, `decide`). Aucune preuve admise, aucun axiome ajoute.
-/

set_option maxHeartbeats 4000000
set_option linter.style.longLine false

namespace RHV6Fresh
namespace ZB
namespace Cert
namespace H28

open Complex Set

def xL_b2bottom : List ℤ := [24, 37, 52, 64]
def zL_b2bottom : List ℤ := [-1, 0, 0]
noncomputable def xF_b2bottom (k : ℕ) : ℝ := ((xL_b2bottom.getD k 0 : ℤ) : ℝ) / 32
def zF_b2bottom (k : ℕ) : ℤ := zL_b2bottom.getD k 0

set_option maxRecDepth 100000 in
theorem side_b2bottom : ∫ t in (1 - 1/4:ℝ)..(2:ℝ), logDeriv zetaFactor ((t:ℂ) + ((-1:ℝ):ℂ) * I) =
    log (I ^ ((-1):ℤ) * I ^ ((0):ℤ) * zetaFactor ((((2:ℝ)):ℂ) + ((-1:ℝ):ℂ) * I)) -
      log (I ^ ((-1):ℤ) * I ^ ((-1):ℤ) * zetaFactor ((((1 - 1/4:ℝ)):ℂ) + ((-1:ℝ):ℂ) * I)) -
      ((((0) - (-1) : ℤ)) : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  have h := horizontal_side (-1:ℝ) (by norm_num) xF_b2bottom zF_b2bottom (-1) 2 (list_mono xL_b2bottom 32 (by norm_num) 3 (by decide)) (by decide) (fun t _ => u1_bottom t)
    (fun k hk => by interval_cases k; exacts [pc_b2bottom_0, pc_b2bottom_1, pc_b2bottom_2])
  have e0 : xF_b2bottom 0 = 1 - 1/4 := by norm_num [xF_b2bottom, xL_b2bottom]
  have e1 : xF_b2bottom (2 + 1) = 2 := by norm_num [xF_b2bottom, xL_b2bottom]
  have f0 : zF_b2bottom 0 = -1 := rfl
  have f1 : zF_b2bottom 2 = 0 := rfl
  rw [e0, e1, f0, f1] at h
  exact h

set_option maxRecDepth 100000 in
theorem nz_b2bottom : ∀ t ∈ Set.Icc (1 - 1/4:ℝ) (2:ℝ), riemannZeta ((t:ℂ) + ((-1:ℝ):ℂ) * I) ≠ 0 := by
  have h := cover xF_b2bottom (fun t => riemannZeta ((t:ℂ) + ((-1:ℝ):ℂ) * I) ≠ 0) 2 (list_mono xL_b2bottom 32 (by norm_num) 3 (by decide))
    (fun k hk t ht => by interval_cases k; exacts [zeta_ne_of_re_pos (pc_b2bottom_0 t ht), zeta_ne_of_re_pos (pc_b2bottom_1 t ht), zeta_ne_of_re_pos (pc_b2bottom_2 t ht)])
  have e0 : xF_b2bottom 0 = 1 - 1/4 := by norm_num [xF_b2bottom, xL_b2bottom]
  have e1 : xF_b2bottom (2 + 1) = 2 := by norm_num [xF_b2bottom, xL_b2bottom]
  rw [e0, e1] at h
  exact h

end H28
end Cert
end ZB
end RHV6Fresh
