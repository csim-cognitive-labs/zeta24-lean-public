/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Side_b2left_c0
import RHV6Fresh.Terminal.ZetaBox28.Side_b2left_c1
import RHV6Fresh.Terminal.ZetaBox28.Side_b2left_c2
import RHV6Fresh.Terminal.ZetaBox28.Side_b2left_c3
import RHV6Fresh.Terminal.ZetaBox28.Side_b2left_c4
/-!
# Certificat (V2), côté b2left (b2)

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

def yL_b2left : List ℤ := [-1000, -872, -489, -254, -95, 141, 318, 633, 948, 1369, 1790, 2352, 2914, 3476, 4038, 4600, 5162, 5724, 6286, 6848, 7410, 7972, 8534, 9096, 9658, 10220, 10782, 11344, 11906, 12327, 12748, 13063, 13378, 13614, 13791, 13968, 14100, 14232, 14364, 14496, 14673, 14909, 15224, 15645, 16066, 16487, 16908, 17470, 18032, 18594, 19015, 19436, 19857, 20172, 20487, 20664, 20796, 20928, 21060, 21192, 21324, 21501, 21678, 21914, 22229, 22650, 23071, 23492, 23913, 24228, 24464, 24700, 24877, 25009, 25141, 25273, 25450, 25686, 26001, 26316, 26737, 27158, 27579, 28000]
def zL_b2left : List ℤ := [3, 3, 3, 2, 2, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, 0, 0, 0, 0]
noncomputable def yF_b2left (k : ℕ) : ℝ := ((yL_b2left.getD k 0 : ℤ) : ℝ) / 1000
def zF_b2left (k : ℕ) : ℤ := zL_b2left.getD k 0

set_option maxRecDepth 100000 in
theorem side_b2left : I * ∫ t in (-1:ℝ)..(28:ℝ), logDeriv zetaFactor (((1 - 1/4:ℝ):ℂ) + (t:ℂ) * I) =
    log (I ^ ((-4):ℤ) * I ^ ((0):ℤ) * zetaFactor (((1 - 1/4:ℝ):ℂ) + (((28:ℝ)):ℂ) * I)) -
      log (I ^ ((-4):ℤ) * I ^ ((3):ℤ) * zetaFactor (((1 - 1/4:ℝ):ℂ) + (((-1:ℝ)):ℂ) * I)) -
      ((((0) - (3) : ℤ)) : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  have h := vertical_side (1 - 1/4:ℝ) (by norm_num) yF_b2left zF_b2left (-4) 82 (list_mono yL_b2left 1000 (by norm_num) 83 (by decide)) (by decide) (fun t _ => u1_left _ t (by norm_num))
    (fun k hk => by interval_cases k; exacts [pc_b2left_0, pc_b2left_1, pc_b2left_2, pc_b2left_3, pc_b2left_4, pc_b2left_5, pc_b2left_6, pc_b2left_7, pc_b2left_8, pc_b2left_9, pc_b2left_10, pc_b2left_11, pc_b2left_12, pc_b2left_13, pc_b2left_14, pc_b2left_15, pc_b2left_16, pc_b2left_17, pc_b2left_18, pc_b2left_19, pc_b2left_20, pc_b2left_21, pc_b2left_22, pc_b2left_23, pc_b2left_24, pc_b2left_25, pc_b2left_26, pc_b2left_27, pc_b2left_28, pc_b2left_29, pc_b2left_30, pc_b2left_31, pc_b2left_32, pc_b2left_33, pc_b2left_34, pc_b2left_35, pc_b2left_36, pc_b2left_37, pc_b2left_38, pc_b2left_39, pc_b2left_40, pc_b2left_41, pc_b2left_42, pc_b2left_43, pc_b2left_44, pc_b2left_45, pc_b2left_46, pc_b2left_47, pc_b2left_48, pc_b2left_49, pc_b2left_50, pc_b2left_51, pc_b2left_52, pc_b2left_53, pc_b2left_54, pc_b2left_55, pc_b2left_56, pc_b2left_57, pc_b2left_58, pc_b2left_59, pc_b2left_60, pc_b2left_61, pc_b2left_62, pc_b2left_63, pc_b2left_64, pc_b2left_65, pc_b2left_66, pc_b2left_67, pc_b2left_68, pc_b2left_69, pc_b2left_70, pc_b2left_71, pc_b2left_72, pc_b2left_73, pc_b2left_74, pc_b2left_75, pc_b2left_76, pc_b2left_77, pc_b2left_78, pc_b2left_79, pc_b2left_80, pc_b2left_81, pc_b2left_82])
  have e0 : yF_b2left 0 = -1 := by norm_num [yF_b2left, yL_b2left]
  have e1 : yF_b2left (82 + 1) = 28 := by norm_num [yF_b2left, yL_b2left]
  have f0 : zF_b2left 0 = 3 := rfl
  have f1 : zF_b2left 82 = 0 := rfl
  rw [e0, e1, f0, f1] at h
  exact h

set_option maxRecDepth 100000 in
theorem nz_b2left : ∀ t ∈ Set.Icc (-1:ℝ) (28:ℝ), riemannZeta (((1 - 1/4:ℝ):ℂ) + (t:ℂ) * I) ≠ 0 := by
  have h := cover yF_b2left (fun t => riemannZeta (((1 - 1/4:ℝ):ℂ) + (t:ℂ) * I) ≠ 0) 82 (list_mono yL_b2left 1000 (by norm_num) 83 (by decide))
    (fun k hk t ht => by interval_cases k; exacts [zeta_ne_of_re_pos (pc_b2left_0 t ht), zeta_ne_of_re_pos (pc_b2left_1 t ht), zeta_ne_of_re_pos (pc_b2left_2 t ht), zeta_ne_of_re_pos (pc_b2left_3 t ht), zeta_ne_of_re_pos (pc_b2left_4 t ht), zeta_ne_of_re_pos (pc_b2left_5 t ht), zeta_ne_of_re_pos (pc_b2left_6 t ht), zeta_ne_of_re_pos (pc_b2left_7 t ht), zeta_ne_of_re_pos (pc_b2left_8 t ht), zeta_ne_of_re_pos (pc_b2left_9 t ht), zeta_ne_of_re_pos (pc_b2left_10 t ht), zeta_ne_of_re_pos (pc_b2left_11 t ht), zeta_ne_of_re_pos (pc_b2left_12 t ht), zeta_ne_of_re_pos (pc_b2left_13 t ht), zeta_ne_of_re_pos (pc_b2left_14 t ht), zeta_ne_of_re_pos (pc_b2left_15 t ht), zeta_ne_of_re_pos (pc_b2left_16 t ht), zeta_ne_of_re_pos (pc_b2left_17 t ht), zeta_ne_of_re_pos (pc_b2left_18 t ht), zeta_ne_of_re_pos (pc_b2left_19 t ht), zeta_ne_of_re_pos (pc_b2left_20 t ht), zeta_ne_of_re_pos (pc_b2left_21 t ht), zeta_ne_of_re_pos (pc_b2left_22 t ht), zeta_ne_of_re_pos (pc_b2left_23 t ht), zeta_ne_of_re_pos (pc_b2left_24 t ht), zeta_ne_of_re_pos (pc_b2left_25 t ht), zeta_ne_of_re_pos (pc_b2left_26 t ht), zeta_ne_of_re_pos (pc_b2left_27 t ht), zeta_ne_of_re_pos (pc_b2left_28 t ht), zeta_ne_of_re_pos (pc_b2left_29 t ht), zeta_ne_of_re_pos (pc_b2left_30 t ht), zeta_ne_of_re_pos (pc_b2left_31 t ht), zeta_ne_of_re_pos (pc_b2left_32 t ht), zeta_ne_of_re_pos (pc_b2left_33 t ht), zeta_ne_of_re_pos (pc_b2left_34 t ht), zeta_ne_of_re_pos (pc_b2left_35 t ht), zeta_ne_of_re_pos (pc_b2left_36 t ht), zeta_ne_of_re_pos (pc_b2left_37 t ht), zeta_ne_of_re_pos (pc_b2left_38 t ht), zeta_ne_of_re_pos (pc_b2left_39 t ht), zeta_ne_of_re_pos (pc_b2left_40 t ht), zeta_ne_of_re_pos (pc_b2left_41 t ht), zeta_ne_of_re_pos (pc_b2left_42 t ht), zeta_ne_of_re_pos (pc_b2left_43 t ht), zeta_ne_of_re_pos (pc_b2left_44 t ht), zeta_ne_of_re_pos (pc_b2left_45 t ht), zeta_ne_of_re_pos (pc_b2left_46 t ht), zeta_ne_of_re_pos (pc_b2left_47 t ht), zeta_ne_of_re_pos (pc_b2left_48 t ht), zeta_ne_of_re_pos (pc_b2left_49 t ht), zeta_ne_of_re_pos (pc_b2left_50 t ht), zeta_ne_of_re_pos (pc_b2left_51 t ht), zeta_ne_of_re_pos (pc_b2left_52 t ht), zeta_ne_of_re_pos (pc_b2left_53 t ht), zeta_ne_of_re_pos (pc_b2left_54 t ht), zeta_ne_of_re_pos (pc_b2left_55 t ht), zeta_ne_of_re_pos (pc_b2left_56 t ht), zeta_ne_of_re_pos (pc_b2left_57 t ht), zeta_ne_of_re_pos (pc_b2left_58 t ht), zeta_ne_of_re_pos (pc_b2left_59 t ht), zeta_ne_of_re_pos (pc_b2left_60 t ht), zeta_ne_of_re_pos (pc_b2left_61 t ht), zeta_ne_of_re_pos (pc_b2left_62 t ht), zeta_ne_of_re_pos (pc_b2left_63 t ht), zeta_ne_of_re_pos (pc_b2left_64 t ht), zeta_ne_of_re_pos (pc_b2left_65 t ht), zeta_ne_of_re_pos (pc_b2left_66 t ht), zeta_ne_of_re_pos (pc_b2left_67 t ht), zeta_ne_of_re_pos (pc_b2left_68 t ht), zeta_ne_of_re_pos (pc_b2left_69 t ht), zeta_ne_of_re_pos (pc_b2left_70 t ht), zeta_ne_of_re_pos (pc_b2left_71 t ht), zeta_ne_of_re_pos (pc_b2left_72 t ht), zeta_ne_of_re_pos (pc_b2left_73 t ht), zeta_ne_of_re_pos (pc_b2left_74 t ht), zeta_ne_of_re_pos (pc_b2left_75 t ht), zeta_ne_of_re_pos (pc_b2left_76 t ht), zeta_ne_of_re_pos (pc_b2left_77 t ht), zeta_ne_of_re_pos (pc_b2left_78 t ht), zeta_ne_of_re_pos (pc_b2left_79 t ht), zeta_ne_of_re_pos (pc_b2left_80 t ht), zeta_ne_of_re_pos (pc_b2left_81 t ht), zeta_ne_of_re_pos (pc_b2left_82 t ht)])
  have e0 : yF_b2left 0 = -1 := by norm_num [yF_b2left, yL_b2left]
  have e1 : yF_b2left (82 + 1) = 28 := by norm_num [yF_b2left, yL_b2left]
  rw [e0, e1] at h
  exact h

end H28
end Cert
end ZB
end RHV6Fresh
