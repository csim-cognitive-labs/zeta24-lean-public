/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Side_right_c0
import RHV6Fresh.Terminal.ZetaBox28.Side_right_c1
import RHV6Fresh.Terminal.ZetaBox28.Side_right_c2
/-!
# Certificat (V2), côté right (b1)

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

def yL_right : List ℤ := [-1000, -438, 124, 686, 1248, 1810, 2372, 2934, 3496, 4058, 4620, 5182, 5744, 6306, 6868, 7430, 7992, 8554, 9116, 9678, 10240, 10802, 11364, 11926, 12488, 13050, 13612, 14174, 14736, 15298, 15860, 16422, 16984, 17546, 18108, 18670, 19232, 19794, 20356, 20918, 21480, 22042, 22604, 23166, 23728, 24290, 24852, 25414, 25976, 26538, 27100, 27606, 28000]
def zL_right : List ℤ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
noncomputable def yF_right (k : ℕ) : ℝ := ((yL_right.getD k 0 : ℤ) : ℝ) / 1000
def zF_right (k : ℕ) : ℤ := zL_right.getD k 0

set_option maxRecDepth 100000 in
theorem side_right : I * ∫ t in (-1:ℝ)..(28:ℝ), logDeriv zetaFactor (((2:ℝ):ℂ) + (t:ℂ) * I) =
    log (I ^ ((-2):ℤ) * I ^ ((0):ℤ) * zetaFactor (((2:ℝ):ℂ) + (((28:ℝ)):ℂ) * I)) -
      log (I ^ ((-2):ℤ) * I ^ ((0):ℤ) * zetaFactor (((2:ℝ):ℂ) + (((-1:ℝ)):ℂ) * I)) -
      ((((0) - (0) : ℤ)) : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  have h := vertical_side (2:ℝ) (by norm_num) yF_right zF_right (-2) 51 (list_mono yL_right 1000 (by norm_num) 52 (by decide)) (by decide) (fun t _ => u1_right t)
    (fun k hk => by interval_cases k; exacts [pc_right_0, pc_right_1, pc_right_2, pc_right_3, pc_right_4, pc_right_5, pc_right_6, pc_right_7, pc_right_8, pc_right_9, pc_right_10, pc_right_11, pc_right_12, pc_right_13, pc_right_14, pc_right_15, pc_right_16, pc_right_17, pc_right_18, pc_right_19, pc_right_20, pc_right_21, pc_right_22, pc_right_23, pc_right_24, pc_right_25, pc_right_26, pc_right_27, pc_right_28, pc_right_29, pc_right_30, pc_right_31, pc_right_32, pc_right_33, pc_right_34, pc_right_35, pc_right_36, pc_right_37, pc_right_38, pc_right_39, pc_right_40, pc_right_41, pc_right_42, pc_right_43, pc_right_44, pc_right_45, pc_right_46, pc_right_47, pc_right_48, pc_right_49, pc_right_50, pc_right_51])
  have e0 : yF_right 0 = -1 := by norm_num [yF_right, yL_right]
  have e1 : yF_right (51 + 1) = 28 := by norm_num [yF_right, yL_right]
  have f0 : zF_right 0 = 0 := rfl
  have f1 : zF_right 51 = 0 := rfl
  rw [e0, e1, f0, f1] at h
  exact h

set_option maxRecDepth 100000 in
theorem nz_right : ∀ t ∈ Set.Icc (-1:ℝ) (28:ℝ), riemannZeta (((2:ℝ):ℂ) + (t:ℂ) * I) ≠ 0 := by
  have h := cover yF_right (fun t => riemannZeta (((2:ℝ):ℂ) + (t:ℂ) * I) ≠ 0) 51 (list_mono yL_right 1000 (by norm_num) 52 (by decide))
    (fun k hk t ht => by interval_cases k; exacts [zeta_ne_of_re_pos (pc_right_0 t ht), zeta_ne_of_re_pos (pc_right_1 t ht), zeta_ne_of_re_pos (pc_right_2 t ht), zeta_ne_of_re_pos (pc_right_3 t ht), zeta_ne_of_re_pos (pc_right_4 t ht), zeta_ne_of_re_pos (pc_right_5 t ht), zeta_ne_of_re_pos (pc_right_6 t ht), zeta_ne_of_re_pos (pc_right_7 t ht), zeta_ne_of_re_pos (pc_right_8 t ht), zeta_ne_of_re_pos (pc_right_9 t ht), zeta_ne_of_re_pos (pc_right_10 t ht), zeta_ne_of_re_pos (pc_right_11 t ht), zeta_ne_of_re_pos (pc_right_12 t ht), zeta_ne_of_re_pos (pc_right_13 t ht), zeta_ne_of_re_pos (pc_right_14 t ht), zeta_ne_of_re_pos (pc_right_15 t ht), zeta_ne_of_re_pos (pc_right_16 t ht), zeta_ne_of_re_pos (pc_right_17 t ht), zeta_ne_of_re_pos (pc_right_18 t ht), zeta_ne_of_re_pos (pc_right_19 t ht), zeta_ne_of_re_pos (pc_right_20 t ht), zeta_ne_of_re_pos (pc_right_21 t ht), zeta_ne_of_re_pos (pc_right_22 t ht), zeta_ne_of_re_pos (pc_right_23 t ht), zeta_ne_of_re_pos (pc_right_24 t ht), zeta_ne_of_re_pos (pc_right_25 t ht), zeta_ne_of_re_pos (pc_right_26 t ht), zeta_ne_of_re_pos (pc_right_27 t ht), zeta_ne_of_re_pos (pc_right_28 t ht), zeta_ne_of_re_pos (pc_right_29 t ht), zeta_ne_of_re_pos (pc_right_30 t ht), zeta_ne_of_re_pos (pc_right_31 t ht), zeta_ne_of_re_pos (pc_right_32 t ht), zeta_ne_of_re_pos (pc_right_33 t ht), zeta_ne_of_re_pos (pc_right_34 t ht), zeta_ne_of_re_pos (pc_right_35 t ht), zeta_ne_of_re_pos (pc_right_36 t ht), zeta_ne_of_re_pos (pc_right_37 t ht), zeta_ne_of_re_pos (pc_right_38 t ht), zeta_ne_of_re_pos (pc_right_39 t ht), zeta_ne_of_re_pos (pc_right_40 t ht), zeta_ne_of_re_pos (pc_right_41 t ht), zeta_ne_of_re_pos (pc_right_42 t ht), zeta_ne_of_re_pos (pc_right_43 t ht), zeta_ne_of_re_pos (pc_right_44 t ht), zeta_ne_of_re_pos (pc_right_45 t ht), zeta_ne_of_re_pos (pc_right_46 t ht), zeta_ne_of_re_pos (pc_right_47 t ht), zeta_ne_of_re_pos (pc_right_48 t ht), zeta_ne_of_re_pos (pc_right_49 t ht), zeta_ne_of_re_pos (pc_right_50 t ht), zeta_ne_of_re_pos (pc_right_51 t ht)])
  have e0 : yF_right 0 = -1 := by norm_num [yF_right, yL_right]
  have e1 : yF_right (51 + 1) = 28 := by norm_num [yF_right, yL_right]
  rw [e0, e1] at h
  exact h

end H28
end Cert
end ZB
end RHV6Fresh
