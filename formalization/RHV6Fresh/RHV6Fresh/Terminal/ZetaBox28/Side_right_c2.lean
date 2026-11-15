/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Side_right_trig0
/-!
# Certificat (V2), côté right (b1), morceaux 2

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
lemma bv_right_21p48_0_5_c2 : (0.808792751305:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((21480:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((21480:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((21480:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((21480:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((21480:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.6828337748392) (-0.7305737717149) 0.00000012924 cs_right_v21p48_2 (-0.1707084760198) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((21480:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.036239090142 0.9993431484458 0.00000013704 cs_right_v21p48_3 0.00402655034466 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((21480:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.0674760647074) 0.9977208931817 0.00000015129 cs_right_v21p48_4 (-0.00421726349984) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((21480:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9999127864909) 0.0132067693487 0.00000012633 cs_right_v21p48_5 (-0.03999651651284) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((21480:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9999127864909) 0.0132067693487 0.00000012633 cs_right_v21p48_5 462.3904 (by norm_num) (by norm_num) (-0.49221142482161) (-0.01968845699286) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.78910429431218:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((21480:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_right_22p042_0_5_c2 : (0.875888173638:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((22042:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((22042:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((22042:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((22042:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((22042:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9091269465921) (-0.4165191410399) 0.00000014485 cs_right_v22p042_2 (-0.22728177286053) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((22042:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.6081016702075 0.7938591554494 0.00000014341 cs_right_v22p042_3 0.06756683631082 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((22042:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.6530236913519 0.7573374799475 0.00000013957 cs_right_v22p042_4 0.04081397198636 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((22042:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6076394986531) 0.794212968708 0.00000013339 cs_right_v22p042_5 (-0.02430558528173) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((22042:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6076394986531) 0.794212968708 0.00000013339 cs_right_v22p042_5 486.849764 (by norm_num) (by norm_num) (-0.47736808709186) (-0.01909472348367) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.85679345015492:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((22042:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_40 : mainRemConst 5 (2:ℝ) 21.503264 ≤ 0.5545577 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 21.503264 (by norm_num) _ 0.04 1.60943791291421 0.5545577 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_40 : ∀ y ∈ Set.Icc (((21480:ℤ):ℝ)/1000) (((22042:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((21480:ℤ):ℝ)/1000) (((22042:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 21.503264 21.48 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.5545577 rb_right_40 0.04 22.13255 22.245219 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.808792751305 0.875888173638 (by rw [hrot]; exact bv_right_21p48_0_5_c2) (by rw [hrot]; exact bv_right_22p042_0_5_c2) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_22p604_0_5_c2 : (0.932283892128:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((22604:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((22604:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((22604:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((22604:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((22604:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9991975308482) (-0.0400536359475) 0.00000015087 cs_right_v22p604_2 (-0.24979942042955) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((22604:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.9554224155309 0.2952422867767 0.00000014978 cs_right_v22p604_3 0.10615802952786 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((22604:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.9967914050219 0.0800430813657 0.00000011372 cs_right_v22p604_4 0.06229945570636 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((22604:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.2487786223906 0.9685603734623 0.00000014045 cs_right_v22p604_5 0.00995113927762 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((22604:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.2487786223906 0.9685603734623 0.00000014045 cs_right_v22p604_5 511.940816 (by norm_num) (by norm_num) (-0.09186720115555) (-0.00367468804622) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.92860920408229:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((22604:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_41 : mainRemConst 5 (2:ℝ) 22.064672 ≤ 0.55390823 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 22.064672 (by norm_num) _ 0.04 1.60943791291421 0.55390823 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_41 : ∀ y ∈ Set.Icc (((22042:ℤ):ℝ)/1000) (((22604:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((22042:ℤ):ℝ)/1000) (((22604:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 22.064672 22.042 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.55390823 rb_right_41 0.04 22.692308 22.802211 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.875888173638 0.932283892128 (by rw [hrot]; exact bv_right_22p042_0_5_c2) (by rw [hrot]; exact bv_right_22p604_0_5_c2) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_23p166_0_5_c2 : (0.940624218618:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((23166:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((23166:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((23166:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((23166:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((23166:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9395494019167) 0.3424133776294 0.00000014272 cs_right_v23p166_2 (-0.23488738615918) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((23166:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.9499529423032 (-0.3123930335481) 0.00000015547 cs_right_v23p166_3 0.10555030964812 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((23166:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.7655062264751 (-0.6434284864908) 0.00000014494 cs_right_v23p166_4 0.04784413009594 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((23166:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9151674376209 0.4030738903952 0.00000014751 cs_right_v23p166_5 0.03660669160443 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((23166:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9151674376209 0.4030738903952 0.00000014751 cs_right_v23p166_5 537.663556 (by norm_num) (by norm_num) 0.36223816425948 0.01448952657038 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.95511374518931:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((23166:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_42 : mainRemConst 5 (2:ℝ) 22.626109 ≤ 0.55329187 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 22.626109 (by norm_num) _ 0.04 1.60943791291421 0.55329187 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_42 : ∀ y ∈ Set.Icc (((22604:ℤ):ℝ)/1000) (((23166:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((22604:ℤ):ℝ)/1000) (((23166:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 22.626109 22.604 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.55329187 rb_right_42 0.04 23.252174 23.359443 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.932283892128 0.940624218618 (by rw [hrot]; exact bv_right_22p604_0_5_c2) (by rw [hrot]; exact bv_right_23p166_0_5_c2) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_23p728_0_5_c2 : (0.90098130984:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((23728:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((23728:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((23728:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((23728:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((23728:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.7391202136699) 0.6735735369752 0.0000001274 cs_right_v23p728_2 (-0.18478008526748) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((23728:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.5937128578645 (-0.8046769801643) 0.00000014938 cs_right_v23p728_3 0.06596807872049 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((23728:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.0925973876746 (-0.9957036325111) 0.0000001476 cs_right_v23p728_4 0.00578732750466 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((23728:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8825065065193 (-0.4703001870626) 0.00000015457 cs_right_v23p728_5 0.03530025407797 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((23728:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8825065065193 (-0.4703001870626) 0.00000015457 cs_right_v23p728_5 564.017984 (by norm_num) (by norm_num) 0.53235662987818 0.02129426519513 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.92227557503564:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((23728:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_43 : mainRemConst 5 (2:ℝ) 23.187573 ≤ 0.55270615 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 23.187573 (by norm_num) _ 0.04 1.60943791291421 0.55270615 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_43 : ∀ y ∈ Set.Icc (((23166:ℤ):ℝ)/1000) (((23728:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((23166:ℤ):ℝ)/1000) (((23728:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 23.187573 23.166 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.55270615 rb_right_43 0.04 23.81214 23.916898 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.940624218618 0.90098130984 (by rw [hrot]; exact bv_right_23p166_0_5_c2) (by rw [hrot]; exact bv_right_23p728_0_5_c2) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_24p29_0_5_c2 : (0.850915713084:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((24290:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((24290:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((24290:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((24290:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((24290:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.4279420577446) 0.903806171261 0.00000011207 cs_right_v24p29_2 (-0.10698554245365) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((24290:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.0182440145746 (-0.9998335641156) 0.0000001433 cs_right_v24p29_3 0.00202709680828 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((24290:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.6337311848716) (-0.7735533500064) 0.00000011694 cs_right_v24p29_4 (-0.03960820636323) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((24290:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.175743849156 (-0.9844359295982) 0.00000016162 cs_right_v24p29_5 0.00702974750144 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((24290:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.175743849156 (-0.9844359295982) 0.00000016162 cs_right_v24p29_5 591.0041 (by norm_num) (by norm_num) 0.28868456019866 0.01154738240795 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.86246309549284:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((24290:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_44 : mainRemConst 5 (2:ℝ) 23.749062 ≤ 0.55214884 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 23.749062 (by norm_num) _ 0.04 1.60943791291421 0.55214884 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_44 : ∀ y ∈ Set.Icc (((23728:ℤ):ℝ)/1000) (((24290:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((23728:ℤ):ℝ)/1000) (((24290:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 23.749062 23.728 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.55214884 rb_right_44 0.04 24.3722 24.474561 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.90098130984 0.850915713084 (by rw [hrot]; exact bv_right_23p728_0_5_c2) (by rw [hrot]; exact bv_right_24p29_0_5_c2) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_24p852_0_5_c2 : (0.842504525053:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((24852:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((24852:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((24852:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((24852:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((24852:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.0526415300769) 0.9986134734275 0.00000011572 cs_right_v24p852_2 (-0.01316041144923) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((24852:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.5639614398874) (-0.8258011227351) 0.00000013721 cs_right_v24p852_3 (-0.06266239745532) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((24852:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.9944577376563) (-0.1051370893128) 0.0000001386 cs_right_v24p852_4 (-0.06215361726602) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((24852:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6652606490411) (-0.7466111898564) 0.0000001562 cs_right_v24p852_5 (-0.02661043220965) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((24852:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6652606490411) (-0.7466111898564) 0.0000001562 cs_right_v24p852_5 618.621904 (by norm_num) (by norm_num) (-0.1772845858421) (-0.00709138343368) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.83541314161978:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((24852:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_45 : mainRemConst 5 (2:ℝ) 24.310575 ≤ 0.55161793 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 24.310575 (by norm_num) _ 0.04 1.60943791291421 0.55161793 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_45 : ∀ y ∈ Set.Icc (((24290:ℤ):ℝ)/1000) (((24852:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((24290:ℤ):ℝ)/1000) (((24852:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 24.310575 24.29 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.55161793 rb_right_45 0.04 24.932347 25.032418 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.850915713084 0.842504525053 (by rw [hrot]; exact bv_right_24p29_0_5_c2) (by rw [hrot]; exact bv_right_24p852_0_5_c2) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_25p414_0_5_c2 : (0.909793107889:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((25414:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((25414:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((25414:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((25414:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((25414:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.3305467471104 0.9437896206119 0.00000013133 cs_right_v25p414_2 0.0826366539451 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((25414:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.9379238608638) (-0.3468412187836) 0.00000013113 cs_right_v25p414_3 (-0.10421377688829) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((25414:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.7814776959413) 0.6239331780757 0.00000016264 cs_right_v25p414_4 (-0.04884236616134) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((25414:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9981063562115) 0.0615117967644 0.00000015688 cs_right_v25p414_5 (-0.03992426052366) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((25414:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9981063562115) 0.0615117967644 0.00000015688 cs_right_v25p414_5 646.871396 (by norm_num) (by norm_num) (-0.50342143794894) (-0.02013685751795) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.88965625037181:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((25414:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_46 : mainRemConst 5 (2:ℝ) 24.87211 ≤ 0.55111158 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 24.87211 (by norm_num) _ 0.04 1.60943791291421 0.55111158 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_46 : ∀ y ∈ Set.Icc (((24852:ℤ):ℝ)/1000) (((25414:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((24852:ℤ):ℝ)/1000) (((25414:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 24.87211 24.852 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.55111158 rb_right_46 0.04 25.492576 25.590456 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.842504525053 0.909793107889 (by rw [hrot]; exact bv_right_24p852_0_5_c2) (by rw [hrot]; exact bv_right_25p414_0_5_c2) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_25p976_0_5_c2 : (1.046198867206:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((25976:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((25976:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((25976:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((25976:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((25976:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.6642062598046 0.7475493591974 0.00000014694 cs_right_v25p976_2 0.16605152821615 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((25976:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.9655574424029) 0.2601899789909 0.00000013222 cs_right_v25p976_3 (-0.10728417495819) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((25976:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.1176599895675) 0.9930539395493 0.00000013215 cs_right_v25p976_4 (-0.00735375760735) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((25976:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.5685495006876) 0.8226490535205 0.00000015039 cs_right_v25p976_5 (-0.02274198604311) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((25976:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.5685495006876) 0.8226490535205 0.00000015039 cs_right_v25p976_5 675.752576 (by norm_num) (by norm_num) (-0.43818143996311) (-0.01752725759852) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.0286716096075:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((25976:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_47 : mainRemConst 5 (2:ℝ) 25.433666 ≤ 0.55062813 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 25.433666 (by norm_num) _ 0.04 1.60943791291421 0.55062813 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_47 : ∀ y ∈ Set.Icc (((25414:ℤ):ℝ)/1000) (((25976:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((25414:ℤ):ℝ)/1000) (((25976:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 25.433666 25.414 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.55062813 rb_right_47 0.04 26.052881 26.148663 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.909793107889 1.046198867206 (by rw [hrot]; exact bv_right_25p414_0_5_c2) (by rw [hrot]; exact bv_right_25p976_0_5_c2) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_26p538_0_5_c2 : (1.205402517767:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((26538:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((26538:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((26538:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((26538:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((26538:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.8983418740381 0.4392970263384 0.00000015075 cs_right_v26p538_2 0.22458543082202 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((26538:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.6366584706804) 0.7711458952076 0.00000012614 cs_right_v26p538_3 (-0.07073984409122) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((26538:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.6140361663727 0.789277889204 0.00000012508 cs_right_v26p538_4 0.03837725258079 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((26538:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.2952933315127 0.9554066403182 0.00000014389 cs_right_v26p538_5 0.0118117275049 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((26538:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.2952933315127 0.9554066403182 0.00000014389 cs_right_v26p538_5 705.265444 (by norm_num) (by norm_num) (-0.03419877377116) (-0.00136795095084) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.20403456681649:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((26538:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_48 : mainRemConst 5 (2:ℝ) 25.995241 ≤ 0.55016606 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 25.995241 (by norm_num) _ 0.04 1.60943791291421 0.55016606 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_48 : ∀ y ∈ Set.Icc (((25976:ℤ):ℝ)/1000) (((26538:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((25976:ℤ):ℝ)/1000) (((26538:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 25.995241 25.976 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.55016606 rb_right_48 0.04 26.613257 26.70703 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.046198867206 1.205402517767 (by rw [hrot]; exact bv_right_25p976_0_5_c2) (by rw [hrot]; exact bv_right_26p538_0_5_c2) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_27p1_0_5_c2 : (1.324927822924:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((27100:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((27100:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((27100:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((27100:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((27100:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.9978708457543 0.0652209720387 0.00000013542 cs_right_v27p1_2 0.24946767758357 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((27100:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.0726730517869) 0.9973558179224 0.00000012005 cs_right_v27p1_3 (-0.00807479687078) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((27100:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.9914924365962 0.1301643122075 0.0000001563 cs_right_v27p1_4 0.06196826751851 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((27100:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9335766431256 0.3583778054097 0.0000001374 cs_right_v27p1_5 0.03734306022902 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((27100:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9335766431256 0.3583778054097 0.0000001374 cs_right_v27p1_5 735.41 (by norm_num) (by norm_num) 0.3944096383857 0.01577638553543 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.34070420846032:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((27100:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_49 : mainRemConst 5 (2:ℝ) 26.556834 ≤ 0.54972398 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 26.556834 (by norm_num) _ 0.04 1.60943791291421 0.54972398 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_49 : ∀ y ∈ Set.Icc (((26538:ℤ):ℝ)/1000) (((27100:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((26538:ℤ):ℝ)/1000) (((27100:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 26.556834 26.538 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.54972398 rb_right_49 0.04 27.173701 27.265547 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.205402517767 1.324927822924 (by rw [hrot]; exact bv_right_26p538_0_5_c2) (by rw [hrot]; exact bv_right_27p1_0_5_c2) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_27p606_0_5_c2 : (1.359220891263:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((27606:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((27606:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((27606:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((27606:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((27606:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.9595307825355 (-0.2816037595041) 0.00000015164 cs_right_v27p606_2 0.23988265772387 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((27606:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.4645803243099 0.8855309832321 0.00000011172 cs_right_v27p606_3 0.05162002362109 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((27606:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.8413985912248 (-0.5404150355837) 0.00000012437 cs_right_v27p606_4 0.05258740417842 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((27606:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9013819717825 (-0.4330248733565) 0.00000015397 cs_right_v27p606_5 0.0360552727125 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((27606:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9013819717825 (-0.4330248733565) 0.00000015397 cs_right_v27p606_5 763.091236 (by norm_num) (by norm_num) 0.52311167431296 0.02092446697252 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.38014535823588:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((27606:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_50 : mainRemConst 5 (2:ℝ) 27.118443 ≤ 0.54930064 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 27.118443 (by norm_num) _ 0.04 1.60943791291421 0.54930064 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_50 : ∀ y ∈ Set.Icc (((27100:ℤ):ℝ)/1000) (((27606:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((27100:ℤ):ℝ)/1000) (((27606:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 27.118443 27.1 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.54930064 rb_right_50 0.04 27.678354 27.76853 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.324927822924 1.359220891263 (by rw [hrot]; exact bv_right_27p1_0_5_c2) (by rw [hrot]; exact bv_right_27p606_0_5_c2) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_28_0_5_c2 : (1.330739949495:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((28000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((28000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((28000:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.8480164376045 (-0.5299699251396) 0.00000014088 cs_right_v28_2 0.21200407418112 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.793180401478 0.6089867409979 0.00000015355 cs_right_v28_3 0.08813113865865 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.4382636670103 (-0.8988464597353) 0.00000014629 cs_right_v28_4 0.02739147004501 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.4695949379756 (-0.8828819820495) 0.00000011667 cs_right_v28_5 0.01878379285222 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.4695949379756 (-0.8828819820495) 0.00000011667 cs_right_v28_5 785 (by norm_num) (by norm_num) 0.38926315604574 0.01557052624183 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.346310475737:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((28000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_51 : mainRemConst 5 (2:ℝ) 27.624106 ≤ 0.54893452 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 27.624106 (by norm_num) _ 0.04 1.60943791291421 0.54893452 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_51 : ∀ y ∈ Set.Icc (((27606:ℤ):ℝ)/1000) (((28000:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((27606:ℤ):ℝ)/1000) (((28000:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 27.624106 27.606 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.54893452 rb_right_51 0.04 28.071338 28.160256 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.359220891263 1.330739949495 (by rw [hrot]; exact bv_right_27p606_0_5_c2) (by rw [hrot]; exact bv_right_28_0_5_c2) (by rw [lt_min_iff]; constructor <;> norm_num)

end H28
end Cert
end ZB
end RHV6Fresh
