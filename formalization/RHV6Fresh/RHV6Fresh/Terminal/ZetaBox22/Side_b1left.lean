/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_c0
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_c1
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_c2
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_c3
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_c4
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_c5
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_c6
/-!
# Certificat (V2), côté b1left (b1)

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

def yL_b1left : List ℤ := [-1000, -806, -558, -354, -155, 81, 317, 494, 730, 966, 1281, 1517, 1753, 1989, 2304, 2619, 2934, 3249, 3670, 4091, 4406, 4721, 5036, 5351, 5666, 5981, 6402, 6823, 7244, 7665, 8086, 8507, 8928, 9349, 9770, 10191, 10612, 11033, 11348, 11663, 11899, 12135, 12312, 12489, 12666, 12843, 13020, 13152, 13284, 13416, 13515, 13614, 13688, 13762, 13817, 13872, 13913, 13954, 13984, 14014, 14044, 14074, 14115, 14156, 14197, 14238, 14279, 14320, 14361, 14402, 14443, 14498, 14553, 14627, 14701, 14775, 14874, 15006, 15138, 15315, 15492, 15728, 15964, 16200, 16436, 16672, 16987, 17302, 17723, 18144, 18565, 18880, 19116, 19352, 19588, 19765, 19942, 20119, 20251, 20383, 20482, 20556, 20630, 20685, 20726, 20767, 20808, 20849, 20890, 20931, 20972, 21013, 21043, 21073, 21103, 21133, 21155, 21171, 21201, 21231, 21272, 21327, 21382, 21456, 21530, 21604, 21703, 21802, 21901, 22000]
def zL_b1left : List ℤ := [-5, -5, -5, -6, -6, -6, -7, -7, -7, -7, -7, -7, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -8, -7, -7, -7, -7, -7, -7, -7, -7, -7, -7, -7, -7, -7, -7, -7, -7, -7, -6, -6, -6, -6, -6, -6, -6, -6, -6, -6, -6, -6, -5, -5, -5, -5, -5, -5, -5, -5, -5, -5, -5, -5, -5, -5, -4, -4, -4, -4, -4, -4, -4, -4, -3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]
noncomputable def yF_b1left (k : ℕ) : ℝ := ((yL_b1left.getD k 0 : ℤ) : ℝ) / 1000
def zF_b1left (k : ℕ) : ℤ := zL_b1left.getD k 0

set_option maxRecDepth 100000 in
theorem side_b1left : I * ∫ t in (-1:ℝ)..(22:ℝ), logDeriv zetaFactor (((1/4:ℝ):ℂ) + (t:ℂ) * I) =
    log (I ^ ((-4):ℤ) * I ^ ((-1):ℤ) * zetaFactor (((1/4:ℝ):ℂ) + (((22:ℝ)):ℂ) * I)) -
      log (I ^ ((-4):ℤ) * I ^ ((-5):ℤ) * zetaFactor (((1/4:ℝ):ℂ) + (((-1:ℝ)):ℂ) * I)) -
      ((((-1) - (-5) : ℤ)) : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  have h := vertical_side (1/4:ℝ) (by norm_num) yF_b1left zF_b1left (-4) 128 (list_mono yL_b1left 1000 (by norm_num) 129 (by decide)) (by decide) (fun t _ => u1_left _ t (by norm_num))
    (fun k hk => by interval_cases k; exacts [pc_b1left_0, pc_b1left_1, pc_b1left_2, pc_b1left_3, pc_b1left_4, pc_b1left_5, pc_b1left_6, pc_b1left_7, pc_b1left_8, pc_b1left_9, pc_b1left_10, pc_b1left_11, pc_b1left_12, pc_b1left_13, pc_b1left_14, pc_b1left_15, pc_b1left_16, pc_b1left_17, pc_b1left_18, pc_b1left_19, pc_b1left_20, pc_b1left_21, pc_b1left_22, pc_b1left_23, pc_b1left_24, pc_b1left_25, pc_b1left_26, pc_b1left_27, pc_b1left_28, pc_b1left_29, pc_b1left_30, pc_b1left_31, pc_b1left_32, pc_b1left_33, pc_b1left_34, pc_b1left_35, pc_b1left_36, pc_b1left_37, pc_b1left_38, pc_b1left_39, pc_b1left_40, pc_b1left_41, pc_b1left_42, pc_b1left_43, pc_b1left_44, pc_b1left_45, pc_b1left_46, pc_b1left_47, pc_b1left_48, pc_b1left_49, pc_b1left_50, pc_b1left_51, pc_b1left_52, pc_b1left_53, pc_b1left_54, pc_b1left_55, pc_b1left_56, pc_b1left_57, pc_b1left_58, pc_b1left_59, pc_b1left_60, pc_b1left_61, pc_b1left_62, pc_b1left_63, pc_b1left_64, pc_b1left_65, pc_b1left_66, pc_b1left_67, pc_b1left_68, pc_b1left_69, pc_b1left_70, pc_b1left_71, pc_b1left_72, pc_b1left_73, pc_b1left_74, pc_b1left_75, pc_b1left_76, pc_b1left_77, pc_b1left_78, pc_b1left_79, pc_b1left_80, pc_b1left_81, pc_b1left_82, pc_b1left_83, pc_b1left_84, pc_b1left_85, pc_b1left_86, pc_b1left_87, pc_b1left_88, pc_b1left_89, pc_b1left_90, pc_b1left_91, pc_b1left_92, pc_b1left_93, pc_b1left_94, pc_b1left_95, pc_b1left_96, pc_b1left_97, pc_b1left_98, pc_b1left_99, pc_b1left_100, pc_b1left_101, pc_b1left_102, pc_b1left_103, pc_b1left_104, pc_b1left_105, pc_b1left_106, pc_b1left_107, pc_b1left_108, pc_b1left_109, pc_b1left_110, pc_b1left_111, pc_b1left_112, pc_b1left_113, pc_b1left_114, pc_b1left_115, pc_b1left_116, pc_b1left_117, pc_b1left_118, pc_b1left_119, pc_b1left_120, pc_b1left_121, pc_b1left_122, pc_b1left_123, pc_b1left_124, pc_b1left_125, pc_b1left_126, pc_b1left_127, pc_b1left_128])
  have e0 : yF_b1left 0 = -1 := by norm_num [yF_b1left, yL_b1left]
  have e1 : yF_b1left (128 + 1) = 22 := by norm_num [yF_b1left, yL_b1left]
  have f0 : zF_b1left 0 = -5 := rfl
  have f1 : zF_b1left 128 = -1 := rfl
  rw [e0, e1, f0, f1] at h
  exact h

set_option maxRecDepth 100000 in
theorem nz_b1left : ∀ t ∈ Set.Icc (-1:ℝ) (22:ℝ), riemannZeta (((1/4:ℝ):ℂ) + (t:ℂ) * I) ≠ 0 := by
  have h := cover yF_b1left (fun t => riemannZeta (((1/4:ℝ):ℂ) + (t:ℂ) * I) ≠ 0) 128 (list_mono yL_b1left 1000 (by norm_num) 129 (by decide))
    (fun k hk t ht => by interval_cases k; exacts [zeta_ne_of_re_pos (pc_b1left_0 t ht), zeta_ne_of_re_pos (pc_b1left_1 t ht), zeta_ne_of_re_pos (pc_b1left_2 t ht), zeta_ne_of_re_pos (pc_b1left_3 t ht), zeta_ne_of_re_pos (pc_b1left_4 t ht), zeta_ne_of_re_pos (pc_b1left_5 t ht), zeta_ne_of_re_pos (pc_b1left_6 t ht), zeta_ne_of_re_pos (pc_b1left_7 t ht), zeta_ne_of_re_pos (pc_b1left_8 t ht), zeta_ne_of_re_pos (pc_b1left_9 t ht), zeta_ne_of_re_pos (pc_b1left_10 t ht), zeta_ne_of_re_pos (pc_b1left_11 t ht), zeta_ne_of_re_pos (pc_b1left_12 t ht), zeta_ne_of_re_pos (pc_b1left_13 t ht), zeta_ne_of_re_pos (pc_b1left_14 t ht), zeta_ne_of_re_pos (pc_b1left_15 t ht), zeta_ne_of_re_pos (pc_b1left_16 t ht), zeta_ne_of_re_pos (pc_b1left_17 t ht), zeta_ne_of_re_pos (pc_b1left_18 t ht), zeta_ne_of_re_pos (pc_b1left_19 t ht), zeta_ne_of_re_pos (pc_b1left_20 t ht), zeta_ne_of_re_pos (pc_b1left_21 t ht), zeta_ne_of_re_pos (pc_b1left_22 t ht), zeta_ne_of_re_pos (pc_b1left_23 t ht), zeta_ne_of_re_pos (pc_b1left_24 t ht), zeta_ne_of_re_pos (pc_b1left_25 t ht), zeta_ne_of_re_pos (pc_b1left_26 t ht), zeta_ne_of_re_pos (pc_b1left_27 t ht), zeta_ne_of_re_pos (pc_b1left_28 t ht), zeta_ne_of_re_pos (pc_b1left_29 t ht), zeta_ne_of_re_pos (pc_b1left_30 t ht), zeta_ne_of_re_pos (pc_b1left_31 t ht), zeta_ne_of_re_pos (pc_b1left_32 t ht), zeta_ne_of_re_pos (pc_b1left_33 t ht), zeta_ne_of_re_pos (pc_b1left_34 t ht), zeta_ne_of_re_pos (pc_b1left_35 t ht), zeta_ne_of_re_pos (pc_b1left_36 t ht), zeta_ne_of_re_pos (pc_b1left_37 t ht), zeta_ne_of_re_pos (pc_b1left_38 t ht), zeta_ne_of_re_pos (pc_b1left_39 t ht), zeta_ne_of_re_pos (pc_b1left_40 t ht), zeta_ne_of_re_pos (pc_b1left_41 t ht), zeta_ne_of_re_pos (pc_b1left_42 t ht), zeta_ne_of_re_pos (pc_b1left_43 t ht), zeta_ne_of_re_pos (pc_b1left_44 t ht), zeta_ne_of_re_pos (pc_b1left_45 t ht), zeta_ne_of_re_pos (pc_b1left_46 t ht), zeta_ne_of_re_pos (pc_b1left_47 t ht), zeta_ne_of_re_pos (pc_b1left_48 t ht), zeta_ne_of_re_pos (pc_b1left_49 t ht), zeta_ne_of_re_pos (pc_b1left_50 t ht), zeta_ne_of_re_pos (pc_b1left_51 t ht), zeta_ne_of_re_pos (pc_b1left_52 t ht), zeta_ne_of_re_pos (pc_b1left_53 t ht), zeta_ne_of_re_pos (pc_b1left_54 t ht), zeta_ne_of_re_pos (pc_b1left_55 t ht), zeta_ne_of_re_pos (pc_b1left_56 t ht), zeta_ne_of_re_pos (pc_b1left_57 t ht), zeta_ne_of_re_pos (pc_b1left_58 t ht), zeta_ne_of_re_pos (pc_b1left_59 t ht), zeta_ne_of_re_pos (pc_b1left_60 t ht), zeta_ne_of_re_pos (pc_b1left_61 t ht), zeta_ne_of_re_pos (pc_b1left_62 t ht), zeta_ne_of_re_pos (pc_b1left_63 t ht), zeta_ne_of_re_pos (pc_b1left_64 t ht), zeta_ne_of_re_pos (pc_b1left_65 t ht), zeta_ne_of_re_pos (pc_b1left_66 t ht), zeta_ne_of_re_pos (pc_b1left_67 t ht), zeta_ne_of_re_pos (pc_b1left_68 t ht), zeta_ne_of_re_pos (pc_b1left_69 t ht), zeta_ne_of_re_pos (pc_b1left_70 t ht), zeta_ne_of_re_pos (pc_b1left_71 t ht), zeta_ne_of_re_pos (pc_b1left_72 t ht), zeta_ne_of_re_pos (pc_b1left_73 t ht), zeta_ne_of_re_pos (pc_b1left_74 t ht), zeta_ne_of_re_pos (pc_b1left_75 t ht), zeta_ne_of_re_pos (pc_b1left_76 t ht), zeta_ne_of_re_pos (pc_b1left_77 t ht), zeta_ne_of_re_pos (pc_b1left_78 t ht), zeta_ne_of_re_pos (pc_b1left_79 t ht), zeta_ne_of_re_pos (pc_b1left_80 t ht), zeta_ne_of_re_pos (pc_b1left_81 t ht), zeta_ne_of_re_pos (pc_b1left_82 t ht), zeta_ne_of_re_pos (pc_b1left_83 t ht), zeta_ne_of_re_pos (pc_b1left_84 t ht), zeta_ne_of_re_pos (pc_b1left_85 t ht), zeta_ne_of_re_pos (pc_b1left_86 t ht), zeta_ne_of_re_pos (pc_b1left_87 t ht), zeta_ne_of_re_pos (pc_b1left_88 t ht), zeta_ne_of_re_pos (pc_b1left_89 t ht), zeta_ne_of_re_pos (pc_b1left_90 t ht), zeta_ne_of_re_pos (pc_b1left_91 t ht), zeta_ne_of_re_pos (pc_b1left_92 t ht), zeta_ne_of_re_pos (pc_b1left_93 t ht), zeta_ne_of_re_pos (pc_b1left_94 t ht), zeta_ne_of_re_pos (pc_b1left_95 t ht), zeta_ne_of_re_pos (pc_b1left_96 t ht), zeta_ne_of_re_pos (pc_b1left_97 t ht), zeta_ne_of_re_pos (pc_b1left_98 t ht), zeta_ne_of_re_pos (pc_b1left_99 t ht), zeta_ne_of_re_pos (pc_b1left_100 t ht), zeta_ne_of_re_pos (pc_b1left_101 t ht), zeta_ne_of_re_pos (pc_b1left_102 t ht), zeta_ne_of_re_pos (pc_b1left_103 t ht), zeta_ne_of_re_pos (pc_b1left_104 t ht), zeta_ne_of_re_pos (pc_b1left_105 t ht), zeta_ne_of_re_pos (pc_b1left_106 t ht), zeta_ne_of_re_pos (pc_b1left_107 t ht), zeta_ne_of_re_pos (pc_b1left_108 t ht), zeta_ne_of_re_pos (pc_b1left_109 t ht), zeta_ne_of_re_pos (pc_b1left_110 t ht), zeta_ne_of_re_pos (pc_b1left_111 t ht), zeta_ne_of_re_pos (pc_b1left_112 t ht), zeta_ne_of_re_pos (pc_b1left_113 t ht), zeta_ne_of_re_pos (pc_b1left_114 t ht), zeta_ne_of_re_pos (pc_b1left_115 t ht), zeta_ne_of_re_pos (pc_b1left_116 t ht), zeta_ne_of_re_pos (pc_b1left_117 t ht), zeta_ne_of_re_pos (pc_b1left_118 t ht), zeta_ne_of_re_pos (pc_b1left_119 t ht), zeta_ne_of_re_pos (pc_b1left_120 t ht), zeta_ne_of_re_pos (pc_b1left_121 t ht), zeta_ne_of_re_pos (pc_b1left_122 t ht), zeta_ne_of_re_pos (pc_b1left_123 t ht), zeta_ne_of_re_pos (pc_b1left_124 t ht), zeta_ne_of_re_pos (pc_b1left_125 t ht), zeta_ne_of_re_pos (pc_b1left_126 t ht), zeta_ne_of_re_pos (pc_b1left_127 t ht), zeta_ne_of_re_pos (pc_b1left_128 t ht)])
  have e0 : yF_b1left 0 = -1 := by norm_num [yF_b1left, yL_b1left]
  have e1 : yF_b1left (128 + 1) = 22 := by norm_num [yF_b1left, yL_b1left]
  rw [e0, e1] at h
  exact h

end H22
end Cert
end ZB
end RHV6Fresh
