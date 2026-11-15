/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Side_right_trig0
/-!
# Certificat (V2), côté right (b1), morceaux 0

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
lemma bv_right_m1_0_5_c0 : (1.149751453998:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((-1000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((-1000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((-1000:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_right_vm1_2 0.19230969230812 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_right_vm1_3 0.05053692234718 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_right_vm1_4 0.01146604981956 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_right_vm1_5 (-0.00154528281757) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_right_vm1_5 2 (by norm_num) (by norm_num) 2.57539819146265 0.10301592765851 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.25276738165729:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((-1000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_right_m0p438_0_5_c0 : (1.483806246535:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((-438:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((-438:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((-438:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.954266876541 0.2989560642247 0.00000013504 cs_right_vm0p438_2 0.23856668537525 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.8864437594156 0.4628363224652 0.00000011769 cs_right_vm0p438_3 0.0984937379695 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.8212506003834 0.5705676571362 0.0000001304 cs_right_vm0p438_4 0.05132815437396 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.7616544499327 0.6479834094309 0.00000010587 cs_right_vm0p438_5 0.0304661737625 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.7616544499327 0.6479834094309 0.00000010587 cs_right_vm0p438_5 1.191844 (by norm_num) (by norm_num) (-1.62378737635294) (-0.06495149505411) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.41885475148121:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((-438:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_0 : mainRemConst 5 (2:ℝ) 1.091716 ≤ 1.42806985 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 1.091716 (by norm_num) _ 0.04 1.60943791291421 1.42806985 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_0 : ∀ y ∈ Set.Icc (((-1000:ℤ):ℝ)/1000) (((-438:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (((-438:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.091716 0.438 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 1.42806985 rb_right_0 0.04 2.236068 3.162278 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.149751453998 1.483806246535 (by rw [hrot]; exact bv_right_m1_0_5_c0) (by rw [hrot]; exact bv_right_m0p438_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_0p124_0_5_c0 : (1.628560384538:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((124:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((124:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((124:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.9963085463416 (-0.0858445134333) 0.00000014966 cs_right_v0p124_2 0.2490770991704 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.9907353207933 (-0.1358069369827) 0.00000012384 cs_right_v0p124_3 0.11008168855035 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.9852614561323 (-0.1710551462541) 0.00000010085 cs_right_v0p124_4 0.06157883470514 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9801518555693 (-0.1982481778582) 0.00000010122 cs_right_v0p124_5 0.03920607017397 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9801518555693 (-0.1982481778582) 0.00000010122 cs_right_v0p124_5 1.015376 (by norm_num) (by norm_num) (-4.21541729847458) (-0.16861669193898) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.45994369259986:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((124:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_1 : mainRemConst 5 (2:ℝ) 1 ≤ 1.56969504 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 1 (by norm_num) _ 0.04 1.60943791291421 1.56969504 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_1 : ∀ y ∈ Set.Icc (((-438:ℤ):ℝ)/1000) (((124:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (((124:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1 0 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 1.56969504 rb_right_1 0.04 2.0474 3.031806 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.483806246535 1.628560384538 (by rw [hrot]; exact bv_right_m0p438_0_5_c0) (by rw [hrot]; exact bv_right_0p124_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_0p686_0_5_c0 : (1.326468646008:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((686:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((686:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((686:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.8890643990301 (-0.4577821472898) 0.00000013433 cs_right_v0p686_2 0.22226606617502 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.7291973875753 (-0.6843034195102) 0.00000013021 cs_right_v0p686_3 0.08102191748502 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.5808710926451 (-0.8139955612467) 0.00000013207 cs_right_v0p686_4 0.03630443503594 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.4499612311949 (-0.8930480896466) 0.00000010827 cs_right_v0p686_5 0.01799844491699 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.4499612311949 (-0.8930480896466) 0.00000010827 cs_right_v0p686_5 1.470596 (by norm_num) (by norm_num) 0.77805544010311 0.03112221760413 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.35759086361297:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((686:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_2 : mainRemConst 5 (2:ℝ) 1.007658 ≤ 1.55635861 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 1.007658 (by norm_num) _ 0.04 1.60943791291421 1.55635861 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_2 : ∀ y ∈ Set.Icc (((124:ℤ):ℝ)/1000) (((686:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (((686:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.007658 0.124 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 1.55635861 rb_right_2 0.04 2.114379 3.077434 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.628560384538 1.326468646008 (by rw [hrot]; exact bv_right_0p124_0_5_c0) (by rw [hrot]; exact bv_right_0p686_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_1p248_0_5_c0 : (1.044259522905:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((1248:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((1248:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((1248:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.6486038107046 (-0.761126202899) 0.000000119 cs_right_v1p248_2 0.16215092292615 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.1984029676263 (-0.9801205346472) 0.00000013657 cs_right_v1p248_3 0.02204475900625 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.158626193479) (-0.9873387112545) 0.00000013799 cs_right_v1p248_4 (-0.00991414571682) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.423931836684) (-0.9056940972767) 0.00000011533 cs_right_v1p248_5 (-0.01695727808056) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.423931836684) (-0.9056940972767) 0.00000011533 cs_right_v1p248_5 2.557504 (by norm_num) (by norm_num) 2.82661838074702 0.11306473522989 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.15732425813502:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((1248:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_3 : mainRemConst 5 (2:ℝ) 1.212681 ≤ 1.28798019 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 1.212681 (by norm_num) _ 0.04 1.60943791291421 1.28798019 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_3 : ∀ y ∈ Set.Icc (((686:ℤ):ℝ)/1000) (((1248:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (((1248:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.212681 0.686 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 1.28798019 rb_right_3 0.04 2.357436 3.249232 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.326468646008 1.044259522905 (by rw [hrot]; exact bv_right_0p686_0_5_c0) (by rw [hrot]; exact bv_right_1p248_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_1p81_0_5_c0 : (0.898040755349:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((1810:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((1810:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((1810:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.3109571339648 (-0.9504239374281) 0.00000010367 cs_right_v1p81_2 0.0777392575737 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.4056518437206) (-0.9140276700859) 0.00000014294 cs_right_v1p81_3 (-0.04507244296233) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.806611321662) (-0.5910822072393) 0.00000010733 cs_right_v1p81_4 (-0.050413214312) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9740049883168) (-0.2265265601283) 0.00000012239 cs_right_v1p81_5 (-0.03896020442828) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9740049883168) (-0.2265265601283) 0.00000012239 cs_right_v1p81_5 4.2761 (by norm_num) (by norm_num) 1.13131601304412 0.04525264052177 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.94329339587109:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((1810:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_4 : mainRemConst 5 (2:ℝ) 1.599219 ≤ 1.02845368 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 1.599219 (by norm_num) _ 0.04 1.60943791291421 1.02845368 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_4 : ∀ y ∈ Set.Icc (((1248:ℤ):ℝ)/1000) (((1810:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (((1810:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.599219 1.248 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 1.02845368 rb_right_4 0.04 2.697425 3.503727 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.044259522905 0.898040755349 (by rw [hrot]; exact bv_right_1p248_0_5_c0) (by rw [hrot]; exact bv_right_1p81_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_2p372_0_5_c0 : (0.829950884889:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((2372:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((2372:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((2372:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.0732830209752) (-0.9973111845539) 0.00000011287 cs_right_v2p372_2 (-0.0183207834613) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.8599195162869) (-0.5104296478737) 0.00000014931 cs_right_v2p372_3 (-0.09554662951085) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.9892591964509) 0.1461719598231 0.00000011855 cs_right_v2p372_4 (-0.06182870718756) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.7800853840809) 0.6256730723797 0.00000012227 cs_right_v2p372_5 (-0.03120342025404) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.7800853840809) 0.6256730723797 0.00000012227 cs_right_v2p372_5 6.626384 (by norm_num) (by norm_num) (-0.92126063257189) (-0.03685042530287) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.79310045958625:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((2372:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_5 : mainRemConst 5 (2:ℝ) 2.067873 ≤ 0.87817062 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 2.067873 (by norm_num) _ 0.04 1.60943791291421 0.87817062 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_5 : ∀ y ∈ Set.Icc (((1810:ℤ):ℝ)/1000) (((2372:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (((2372:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 2.067873 1.81 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.87817062 rb_right_5 0.04 3.102642 3.824446 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.898040755349 0.829950884889 (by rw [hrot]; exact bv_right_1p81_0_5_c0) (by rw [hrot]; exact bv_right_2p372_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_2p934_0_5_c0 : (0.801514103873:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((2934:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((2934:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((2934:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.4465425278859) (-0.8947624102435) 0.00000012848 cs_right_v2p934_2 (-0.11163566409148) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.9966614923173) 0.081644774618 0.00000014849 cs_right_v2p934_3 (-0.11074018231202) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.6011995358404) 0.7990989413665 0.00000014977 cs_right_v2p934_4 (-0.03757498035065) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.0097016745975 0.9999529376475 0.00000012933 cs_right_v2p934_5 0.0003880618107 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.0097016745975 0.9999529376475 0.00000012933 cs_right_v2p934_5 9.608356 (by norm_num) (by norm_num) (-1.52692172042908) (-0.06107686881716) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.74043723505655:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((2934:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_6 : mainRemConst 5 (2:ℝ) 2.574176 ≤ 0.79130312 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 2.574176 (by norm_num) _ 0.04 1.60943791291421 0.79130312 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_6 : ∀ y ∈ Set.Icc (((2372:ℤ):ℝ)/1000) (((2934:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (((2934:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 2.574176 2.372 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.79130312 rb_right_6 0.04 3.550825 4.196232 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.829950884889 0.801514103873 (by rw [hrot]; exact bv_right_2p372_0_5_c0) (by rw [hrot]; exact bv_right_2p934_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_3p496_0_5_c0 : (0.795192513036:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((3496:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((3496:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((3496:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.7528925888707) (-0.6581434111112) 0.00000014409 cs_right_v3p496_2 (-0.18822318324018) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.7653856643972) 0.6435718955155 0.00000014692 cs_right_v3p496_3 (-0.08504286792421) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.1336946069879 0.9910225789871 0.00000012254 cs_right_v3p496_4 0.00835590527799 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.792078118693 0.6104197358275 0.00000013638 cs_right_v3p496_5 0.03168311929252 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.792078118693 0.6104197358275 0.00000013638 cs_right_v3p496_5 13.222016 (by norm_num) (by norm_num) (-0.71048849077127) (-0.02841953963085) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.76677297340612:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((3496:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_7 : mainRemConst 5 (2:ℝ) 3.099734 ≤ 0.73709521 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 3.099734 (by norm_num) _ 0.04 1.60943791291421 0.73709521 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_7 : ∀ y ∈ Set.Icc (((2934:ℤ):ℝ)/1000) (((3496:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (((3496:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 3.099734 2.934 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.73709521 rb_right_7 0.04 4.027657 4.606736 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.801514103873 0.795192513036 (by rw [hrot]; exact bv_right_2p934_0_5_c0) (by rw [hrot]; exact bv_right_3p496_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_4p058_0_5_c0 : (0.804002228983:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((4058:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((4058:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((4058:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9464300767654) (-0.3229088255214) 0.00000014236 cs_right_v4p058_2 (-0.23660755478135) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.2514908190316) 0.967859684015 0.00000014083 cs_right_v4p058_3 (-0.02794343998465) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.7914597239363 0.6112213227519 0.00000011221 cs_right_v4p058_4 0.04946622573289 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.96942647155 (-0.2453819803046) 0.00000014344 cs_right_v4p058_5 0.0387770531244 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.96942647155 (-0.2453819803046) 0.00000014344 cs_right_v4p058_5 17.467364 (by norm_num) (by norm_num) 0.49225137768281 0.01969005510732 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.82369228409129:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((4058:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_8 : mainRemConst 5 (2:ℝ) 3.636209 ≤ 0.70072613 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 3.636209 (by norm_num) _ 0.04 1.60943791291421 0.70072613 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_8 : ∀ y ∈ Set.Icc (((3496:ℤ):ℝ)/1000) (((4058:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (((4058:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 3.636209 3.496 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.70072613 rb_right_8 0.04 4.524088 5.04652 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.795192513036 0.804002228983 (by rw [hrot]; exact bv_right_3p496_0_5_c0) (by rw [hrot]; exact bv_right_4p058_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_4p62_0_5_c0 : (0.825950655982:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((4620:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((4620:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((4620:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9981554465973) 0.0607099981673 0.00000013421 cs_right_v4p62_2 (-0.24953889520183) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.355267132451 0.9347648178018 0.00000013475 cs_right_v4p62_3 0.03947411085566 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.9926286051732 (-0.1211959248153) 0.00000014343 cs_right_v4p62_4 0.06203927885895 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.406279368421 (-0.9137489123361) 0.0000001505 cs_right_v4p62_5 0.01625116871684 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.406279368421 (-0.9137489123361) 0.0000001505 cs_right_v4p62_5 22.3444 (by norm_num) (by norm_num) 1.05687518117283 0.04227500724692 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.86822566322962:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((4620:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_9 : mainRemConst 5 (2:ℝ) 4.179397 ≤ 0.67487216 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 4.179397 (by norm_num) _ 0.04 1.60943791291421 0.67487216 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_9 : ∀ y ∈ Set.Icc (((4058:ℤ):ℝ)/1000) (((4620:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (((4620:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 4.179397 4.058 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.67487216 rb_right_9 0.04 5.034323 5.508576 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.804002228983 0.825950655982 (by rw [hrot]; exact bv_right_4p058_0_5_c0) (by rw [hrot]; exact bv_right_4p62_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_5p182_0_5_c0 : (0.860460241181:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((5182:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((5182:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((5182:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9003182897513) 0.4352320955795 0.00000011888 cs_right_v5p182_2 (-0.22507960215783) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.8308425240881 0.5565075921917 0.00000012866 cs_right_v5p182_3 0.09231582171422 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.6211460514718 (-0.7836948275579) 0.00000013057 cs_right_v5p182_4 0.03882162005636 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.4672039187481) (-0.8841495904548) 0.00000014766 cs_right_v5p182_5 (-0.01868816265633) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.4672039187481) (-0.8841495904548) 0.00000014766 cs_right_v5p182_5 27.853124 (by norm_num) (by norm_num) 0.6727358943759 0.02690943577504 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.88736967695642:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((5182:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_10 : mainRemConst 5 (2:ℝ) 4.726986 ≤ 0.65564452 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 4.726986 (by norm_num) _ 0.04 1.60943791291421 0.65564452 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_10 : ∀ y ∈ Set.Icc (((4620:ℤ):ℝ)/1000) (((5182:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (((5182:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 4.726986 4.62 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.65564452 rb_right_10 0.04 5.554559 5.987748 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.825950655982 0.860460241181 (by rw [hrot]; exact bv_right_4p62_0_5_c0) (by rw [hrot]; exact bv_right_5p182_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_5p744_0_5_c0 : (0.905862535221:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((5744:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((5744:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((5744:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.6675784209665) 0.7445394897793 0.00000010355 cs_right_v5p744_2 (-0.16689463112913) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.9996289133583 (-0.0272403299922) 0.00000012258 cs_right_v5p744_3 0.11106986564202 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.1086780965769) (-0.9940769946659) 0.00000010587 cs_right_v5p744_4 (-0.00679238765294) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9838138609772) (-0.1791934334688) 0.00000014116 cs_right_v5p744_5 (-0.03935256008549) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9838138609772) (-0.1791934334688) 0.00000014116 cs_right_v5p744_5 33.993536 (by norm_num) (by norm_num) (-0.19580621117275) (-0.00783224844691) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.89803028677446:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((5744:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_11 : mainRemConst 5 (2:ℝ) 5.277605 ≤ 0.64082814 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 5.277605 (by norm_num) _ 0.04 1.60943791291421 0.64082814 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_11 : ∀ y ∈ Set.Icc (((5182:ℤ):ℝ)/1000) (((5744:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (((5744:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 5.277605 5.182 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.64082814 rb_right_11 0.04 6.082232 6.480242 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.860460241181 0.905862535221 (by rw [hrot]; exact bv_right_5p182_0_5_c0) (by rw [hrot]; exact bv_right_5p744_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_6p306_0_5_c0 : (0.958468571111:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((6306:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((6306:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((6306:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.3348093288063) 0.9422858978793 0.00000011496 cs_right_v6p306_2 (-0.08370236094158) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.7993018446929 (-0.6009297472006) 0.00000011649 cs_right_v6p306_3 0.08881130313364 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.775805422151) (-0.6309722235726) 0.00000013709 cs_right_v6p306_4 (-0.04848784745257) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.7489385493879) 0.6626394564219 0.00000014184 cs_right_v6p306_5 (-0.02995754764912) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.7489385493879) 0.6626394564219 0.00000014184 cs_right_v6p306_5 40.765636 (by norm_num) (by norm_num) (-0.79512560052507) (-0.031805024021) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.92666354709037:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((6306:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_12 : mainRemConst 5 (2:ℝ) 5.830397 ≤ 0.62908225 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 5.830397 (by norm_num) _ 0.04 1.60943791291421 0.62908225 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_12 : ∀ y ∈ Set.Icc (((5744:ℤ):ℝ)/1000) (((6306:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (((6306:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 5.830397 5.744 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.62908225 rb_right_12 0.04 6.615561 6.98324 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.905862535221 0.958468571111 (by rw [hrot]; exact bv_right_5p744_0_5_c0) (by rw [hrot]; exact bv_right_6p306_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_6p868_0_5_c0 : (1.013449516177:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((6868:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((6868:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((6868:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.0481272284472 0.9988412135479 0.00000013057 cs_right_v6p868_2 0.0120317744693 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.3038321847254 (-0.9527255656929) 0.00000011041 cs_right_v6p868_3 0.03375911936837 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.9953675299292) 0.096143017844 0.00000014577 cs_right_v6p868_4 (-0.0622104797312) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.0580127373195 0.9983158429618 0.00000013535 cs_right_v6p868_5 0.00232050407878 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.0580127373195 0.9983158429618 0.00000013535 cs_right_v6p868_5 48.169424 (by norm_num) (by norm_num) (-0.68871494980299) (-0.02754859799211) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.98590091818525:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((6868:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_13 : mainRemConst 5 (2:ℝ) 6.384797 ≤ 0.61955315 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 6.384797 (by norm_num) _ 0.04 1.60943791291421 0.61955315 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_13 : ∀ y ∈ Set.Icc (((6306:ℤ):ℝ)/1000) (((6868:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (((6868:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 6.384797 6.306 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.61955315 rb_right_13 0.04 7.153281 7.494627 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.958468571111 1.013449516177 (by rw [hrot]; exact bv_right_6p306_0_5_c0) (by rw [hrot]; exact bv_right_6p868_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_7p43_0_5_c0 : (1.066602034512:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((7430:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((7430:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((7430:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.4238524542193 0.9057312499038 0.00000014618 cs_right_v7p43_2 0.10596307700982 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.3038276558556) (-0.9527270099748) 0.00000010432 cs_right_v7p43_3 (-0.03375864001954) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.6406981173236) 0.7677928903306 0.00000011512 cs_right_v7p43_4 (-0.04004363952773) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8206510517391 0.5714296555828 0.00000012885 cs_right_v7p43_5 0.03282603691556 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8206510517391 0.5714296555828 0.00000012885 cs_right_v7p43_5 56.2049 (by norm_num) (by norm_num) (-0.04038000336488) (-0.00161520013459) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.06498683437811:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((7430:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_14 : mainRemConst 5 (2:ℝ) 6.940419 ≤ 0.61167365 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 6.940419 (by norm_num) _ 0.04 1.60943791291421 0.61167365 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_14 : ∀ y ∈ Set.Icc (((6868:ℤ):ℝ)/1000) (((7430:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (((7430:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 6.940419 6.868 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.61167365 rb_right_14 0.04 7.694473 8.012797 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.013449516177 1.066602034512 (by rw [hrot]; exact bv_right_6p868_0_5_c0) (by rw [hrot]; exact bv_right_7p43_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_7p992_0_5_c0 : (1.115314662765:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((7992:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((7992:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((7992:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.736068157682 0.6769074288605 0.00000014224 cs_right_v7p992_2 0.1840170038605 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.7992989881003) (-0.6009335467195) 0.00000010579 cs_right_v7p992_3 (-0.08881101043233) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.0835925658568 0.9965000165245 0.00000012356 cs_right_v7p992_4 0.00522452764355 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9564358681401 (-0.2919425116954) 0.00000012236 cs_right_v7p992_5 0.0382574298312 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9564358681401 (-0.2919425116954) 0.00000012236 cs_right_v7p992_5 64.872064 (by norm_num) (by norm_num) 0.58433220342992 0.0233732881372 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.13868795090292:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((7992:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_15 : mainRemConst 5 (2:ℝ) 7.496992 ≤ 0.60505318 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 7.496992 (by norm_num) _ 0.04 1.60943791291421 0.60505318 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_15 : ∀ y ∈ Set.Icc (((7430:ℤ):ℝ)/1000) (((7992:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (((7992:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 7.496992 7.43 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.60505318 rb_right_15 0.04 8.238451 8.536514 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.066602034512 1.115314662765 (by rw [hrot]; exact bv_right_7p43_0_5_c0) (by rw [hrot]; exact bv_right_7p992_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_8p554_0_5_c0 : (1.157610451548:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((8554:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((8554:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((8554:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.9379921196888 0.3466565784774 0.00000012691 cs_right_v8p554_2 0.2344979981947 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.9996287835538) (-0.0272450815369) 0.00000011216 cs_right_v8p554_3 (-0.11106987730163) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.7596584331967 0.6503222777002 0.0000001538 cs_right_v8p554_4 0.04747864246229 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.3616480881818 (-0.9323146788045) 0.00000011586 cs_right_v8p554_5 0.01446591889287 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.3616480881818 (-0.9323146788045) 0.00000011586 cs_right_v8p554_5 74.170916 (by norm_num) (by norm_num) 0.69405576748384 0.02776223069936 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.18537268224823:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((8554:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_16 : mainRemConst 5 (2:ℝ) 8.054319 ≤ 0.59941457 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 8.054319 (by norm_num) _ 0.04 1.60943791291421 0.59941457 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_16 : ∀ y ∈ Set.Icc (((7992:ℤ):ℝ)/1000) (((8554:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (((8554:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 8.054319 7.992 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.59941457 rb_right_16 0.04 8.784698 9.064818 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.115314662765 1.157610451548 (by rw [hrot]; exact bv_right_7p992_0_5_c0) (by rw [hrot]; exact bv_right_8p554_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_9p116_0_5_c0 : (1.18981373848:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((9116:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((9116:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((9116:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.9993683643195 (-0.0355369159811) 0.00000011158 cs_right_v9p116_2 0.24984206318487 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.8308451654776) 0.556503648631 0.00000011134 cs_right_v9p116_3 (-0.0923161418687) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.9974742552051 (-0.0710289391939) 0.00000012314 cs_right_v9p116_4 0.06234213325406 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.5093842279261) (-0.8605391962796) 0.00000010936 cs_right_v9p116_5 (-0.02037537349145) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.5093842279261) (-0.8605391962796) 0.00000010936 cs_right_v9p116_5 84.101456 (by norm_num) (by norm_num) 0.24197356495875 0.00967894259835 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.19949268107878:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((9116:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_17 : mainRemConst 5 (2:ℝ) 8.612253 ≤ 0.59455589 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 8.612253 (by norm_num) _ 0.04 1.60943791291421 0.59455589 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_17 : ∀ y ∈ Set.Icc (((8554:ℤ):ℝ)/1000) (((9116:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (((9116:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 8.612253 8.554 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.59455589 rb_right_17 0.04 9.332817 9.596951 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.157610451548 1.18981373848 (by rw [hrot]; exact bv_right_8p554_0_5_c0) (by rw [hrot]; exact bv_right_9p116_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_9p678_0_5_c0 : (1.204907118781:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((9678:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((9678:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((9678:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.911000341941 (-0.4124055976624) 0.00000010862 cs_right_v9p678_2 0.22775005833025 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.3552715692244) 0.9347631315464 0.00000011771 cs_right_v9p678_3 (-0.03947463188164) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.6598432460334 (-0.7514032809777) 0.00000011722 cs_right_v9p678_4 0.04124019555083 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9913239027868) (-0.1314416955976) 0.00000010684 cs_right_v9p678_5 (-0.03965296038508) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9913239027868) (-0.1314416955976) 0.00000010684 cs_right_v9p678_5 94.663684 (by norm_num) (by norm_num) (-0.37611142918233) (-0.01504445716729) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.18986266161436:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((9678:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_18 : mainRemConst 5 (2:ℝ) 9.170684 ≤ 0.59032673 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 9.170684 (by norm_num) _ 0.04 1.60943791291421 0.59032673 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_18 : ∀ y ∈ Set.Icc (((9116:ℤ):ℝ)/1000) (((9678:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (((9678:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 9.170684 9.116 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.59032673 rb_right_18 0.04 9.882494 10.132309 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.18981373848 1.204907118781 (by rw [hrot]; exact bv_right_9p116_0_5_c0) (by rw [hrot]; exact bv_right_9p678_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_10p24_0_5_c0 : (1.19365319944:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((10240:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((10240:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((10240:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.6861290207596 (-0.72747987386) 0.00000012423 cs_right_v10p24_2 0.1715322241324 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.2514862251695 0.9678608776833 0.00000012408 cs_right_v10p24_3 0.02794290012105 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.0584539337429) (-0.9982901069477) 0.00000014844 cs_right_v10p24_4 (-0.00365338013644) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.7160417855815) 0.6980574197548 0.00000010672 cs_right_v10p24_5 (-0.02864167569206) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.7160417855815) 0.6980574197548 0.00000010672 cs_right_v10p24_5 105.8576 (by norm_num) (by norm_num) (-0.66182827539259) (-0.0264731310157) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.16718006842495:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((10240:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_19 : mainRemConst 5 (2:ℝ) 9.729526 ≤ 0.58661282 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 9.729526 (by norm_num) _ 0.04 1.60943791291421 0.58661282 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_19 : ∀ y ∈ Set.Icc (((9678:ℤ):ℝ)/1000) (((10240:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (((10240:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 9.729526 9.678 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.58661282 rb_right_19 0.04 10.433485 10.670408 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.204907118781 1.19365319944 (by rw [hrot]; exact bv_right_9p678_0_5_c0) (by rw [hrot]; exact bv_right_10p24_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)

end H28
end Cert
end ZB
end RHV6Fresh
