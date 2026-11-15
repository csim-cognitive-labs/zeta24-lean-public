/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Side_right_trig0
/-!
# Certificat (V2), côté right (b1), morceaux 1

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
lemma bv_right_10p24_0_5_c1 : (1.19365319944:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((10240:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
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
lemma bv_right_10p802_0_5_c1 : (1.14877355317:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((10802:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((10802:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((10802:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.3584488745688 (-0.9335493582668) 0.00000013984 cs_right_v10p802_2 0.0896121836822 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.7653826097391 0.6435755283639 0.00000013044 cs_right_v10p802_3 0.08504249769989 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.7430288755614) (-0.6692593593293) 0.00000013117 cs_right_v10p802_4 (-0.04643931292072) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.1061881457906 0.9943460553014 0.00000011378 cs_right_v10p802_5 0.00424752128042 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.1061881457906 0.9943460553014 0.00000011378 cs_right_v10p802_5 117.683204 (by norm_num) (by norm_num) (-0.40776658572873) (-0.01631066342914) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.13246288974179:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((10802:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_20 : mainRemConst 5 (2:ℝ) 10.288712 ≤ 0.58332585 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 10.288712 (by norm_num) _ 0.04 1.60943791291421 0.58332585 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_20 : ∀ y ∈ Set.Icc (((10240:ℤ):ℝ)/1000) (((10802:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (((10802:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 10.288712 10.24 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.58332585 rb_right_20 0.04 10.985591 11.210853 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.19365319944 1.14877355317 (by rw [hrot]; exact bv_right_10p24_0_5_c1) (by rw [hrot]; exact bv_right_10p802_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_11p364_0_5_c1 : (1.07009418261:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((11364:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((11364:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((11364:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.022940960471) (-0.9997368215348) 0.00000015027 cs_right_v11p364_2 (-0.00573527768525) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.9966610968577 0.0816496050848 0.00000013681 cs_right_v11p364_3 0.11074010667195 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.998947428644) 0.0458697528204 0.0000001077 cs_right_v11p364_4 (-0.0624342210215) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8473063665365 0.5311044353295 0.00000012083 cs_right_v11p364_5 0.03389224982826 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8473063665365 0.5311044353295 0.00000012083 cs_right_v11p364_5 130.140496 (by norm_num) (by norm_num) 0.15921687956571 0.00636867518263 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.07646285779346:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((11364:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_21 : mainRemConst 5 (2:ℝ) 10.848188 ≤ 0.5803965 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 10.848188 (by norm_num) _ 0.04 1.60943791291421 0.5803965 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_21 : ∀ y ∈ Set.Icc (((10802:ℤ):ℝ)/1000) (((11364:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (((11364:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 10.848188 10.802 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.5803965 rb_right_21 0.04 11.538653 11.753319 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.14877355317 1.07009418261 (by rw [hrot]; exact bv_right_10p802_0_5_c1) (by rw [hrot]; exact bv_right_11p364_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_11p926_0_5_c1 : (0.967425677766:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((11926:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((11926:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((11926:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.4008932536305) (-0.9161247727194) 0.00000013494 cs_right_v11p926_2 (-0.10022334714263) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.8599219937134 (-0.5104254742153) 0.00000014317 cs_right_v11p926_3 0.09554687228259 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.6785692665647) 0.7345364187387 0.00000013492 cs_right_v11p926_4 (-0.0424105875928) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9412104532955 (-0.3378207847474) 0.00000012789 cs_right_v11p926_5 0.03764841301622 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9412104532955 (-0.3378207847474) 0.00000012789 cs_right_v11p926_5 143.229476 (by norm_num) (by norm_num) 0.5783918199147 0.02313567279659 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.99056135056338:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((11926:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_22 : mainRemConst 5 (2:ℝ) 11.407913 ≤ 0.57776964 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 11.407913 (by norm_num) _ 0.04 1.60943791291421 0.57776964 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_22 : ∀ y ∈ Set.Icc (((11364:ℤ):ℝ)/1000) (((11926:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (((11926:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 11.407913 11.364 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.57776964 rb_right_22 0.04 12.092539 12.29754 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.07009418261 0.967425677766 (by rw [hrot]; exact bv_right_11p364_0_5_c1) (by rw [hrot]; exact bv_right_11p926_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_12p488_0_5_c1 : (0.859088033822:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((12488:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((12488:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((12488:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.7187761383905) (-0.6952415859637) 0.00000011961 cs_right_v12p488_2 (-0.17969406450013) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.4056562800311 (-0.9140257012094) 0.00000014954 cs_right_v12p488_3 0.04507290338789 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.0332782814262 0.9994461246036 0.00000014638 cs_right_v12p488_4 0.00207988344038 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.3161718618363 (-0.9487019309472) 0.00000013495 cs_right_v12p488_5 0.01264686907545 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.3161718618363 (-0.9487019309472) 0.00000013495 cs_right_v12p488_5 156.950144 (by norm_num) (by norm_num) 0.52543893953279 0.02101755758132 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.88010559140359:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((12488:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_23 : mainRemConst 5 (2:ℝ) 11.967851 ≤ 0.57540089 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 11.967851 (by norm_num) _ 0.04 1.60943791291421 0.57540089 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_23 : ∀ y ∈ Set.Icc (((11926:ℤ):ℝ)/1000) (((12488:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (((12488:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 11.967851 11.926 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.57540089 rb_right_23 0.04 12.64714 12.843292 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.967425677766 0.859088033822 (by rw [hrot]; exact bv_right_11p926_0_5_c1) (by rw [hrot]; exact bv_right_12p488_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_13p05_0_5_c1 : (0.766715502854:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((13050:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((13050:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((13050:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9289583895565) (-0.3701841572986) 0.00000010428 cs_right_v13p05_2 (-0.23223962345913) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.1983983085332) (-0.980121477762) 0.00000015065 cs_right_v13p05_3 (-0.0220442732426) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.7259273841846 0.6877713521883 0.00000011572 cs_right_v13p05_4 0.04537045427903 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.5503742950452) (-0.8349180410943) 0.00000014201 cs_right_v13p05_5 (-0.02201497748221) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.5503742950452) (-0.8349180410943) 0.00000014201 cs_right_v13p05_5 171.3025 (by norm_num) (by norm_num) 0.05890193101429 0.00235607724058 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.76907158009509:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((13050:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_24 : mainRemConst 5 (2:ℝ) 12.527974 ≤ 0.57325409 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 12.527974 (by norm_num) _ 0.04 1.60943791291421 0.57325409 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_24 : ∀ y ∈ Set.Icc (((12488:ℤ):ℝ)/1000) (((13050:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (((13050:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 12.527974 12.488 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.57325409 rb_right_24 0.04 13.202368 13.390389 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.859088033822 0.766715502854 (by rw [hrot]; exact bv_right_12p488_0_5_c1) (by rw [hrot]; exact bv_right_13p05_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_13p612_0_5_c1 : (0.709259578929:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((13612:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((13612:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((13612:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9999465273173) 0.0103412689664 0.00000011071 cs_right_v13p612_2 (-0.24998665950683) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.7291941346648) (-0.6843068857912) 0.00000014456 cs_right_v13p612_3 (-0.0810215865806) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.9997861164486 (-0.0206814254016) 0.00000012858 cs_right_v13p612_4 0.06248662424178 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9965175882135) (-0.0833828272185) 0.00000014906 cs_right_v13p612_5 (-0.03986070949094) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9965175882135) (-0.0833828272185) 0.00000014906 cs_right_v13p612_5 186.286544 (by norm_num) (by norm_num) (-0.44104775665673) (-0.01764191026626) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.69161766866341:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((13612:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_25 : mainRemConst 5 (2:ℝ) 13.088258 ≤ 0.57129954 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 13.088258 (by norm_num) _ 0.04 1.60943791291421 0.57129954 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_25 : ∀ y ∈ Set.Icc (((13050:ℤ):ℝ)/1000) (((13612:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (((13612:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 13.088258 13.05 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.57129954 rb_right_25 0.04 13.758145 13.938671 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.766715502854 0.709259578929 (by rw [hrot]; exact bv_right_13p05_0_5_c1) (by rw [hrot]; exact bv_right_13p612_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_14p174_0_5_c1 : (0.699167312962:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((14174:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((14174:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((14174:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9211037646069) 0.3893171646387 0.00000012632 cs_right_v14p174_2 (-0.23027597273173) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.9907346750295) (-0.1358116463314) 0.00000013848 cs_right_v14p174_3 (-0.11008164594559) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.6968642239444 (-0.7172030768104) 0.00000015441 cs_right_v14p174_4 0.0435540043459 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6814718976333) 0.7318442817398 0.00000014894 cs_right_v14p174_5 (-0.02725888186294) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6814718976333) 0.7318442817398 0.00000014894 cs_right_v14p174_5 201.902276 (by norm_num) (by norm_num) (-0.58074522891209) (-0.02322980915648) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.67593750380564:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((14174:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_26 : mainRemConst 5 (2:ℝ) 13.648682 ≤ 0.56951259 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 13.648682 (by norm_num) _ 0.04 1.60943791291421 0.56951259 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_26 : ∀ y ∈ Set.Icc (((13612:ℤ):ℝ)/1000) (((14174:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (((14174:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 13.648682 13.612 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.56951259 rb_right_26 0.04 14.314408 14.488005 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.709259578929 0.699167312962 (by rw [hrot]; exact bv_right_13p612_0_5_c1) (by rw [hrot]; exact bv_right_14p174_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_14p736_0_5_c1 : (0.741512079073:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((14736:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((14736:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((14736:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((14736:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((14736:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.7042438170015) 0.7099582003124 0.00000014192 cs_right_v14p736_2 (-0.17606098973038) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((14736:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.8864459561881) 0.4628321149787 0.00000013957 cs_right_v14p736_3 (-0.09849401063987) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((14736:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.0080813852383) (-0.999967345073) 0.00000012375 cs_right_v14p736_4 (-0.00050509431177) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((14736:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.15411543194 0.9880528496178 0.000000156 cs_right_v14p736_5 0.0061646110376 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((14736:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.15411543194 0.9880528496178 0.000000156 cs_right_v14p736_5 218.149696 (by norm_num) (by norm_num) (-0.26018906795301) (-0.01040756271812) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.73110451635558:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((14736:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_27 : mainRemConst 5 (2:ℝ) 14.209232 ≤ 0.56787262 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 14.209232 (by norm_num) _ 0.04 1.60943791291421 0.56787262 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_27 : ∀ y ∈ Set.Icc (((14174:ℤ):ℝ)/1000) (((14736:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (((14736:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 14.209232 14.174 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.56787262 rb_right_27 0.04 14.871103 15.038275 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.699167312962 0.741512079073 (by rw [hrot]; exact bv_right_14p174_0_5_c1) (by rw [hrot]; exact bv_right_14p736_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_15p298_0_5_c1 : (0.834279017383:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((15298:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((15298:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((15298:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((15298:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((15298:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.3818606505901) 0.9242199108048 0.00000015014 cs_right_v15p298_2 (-0.09546520018253) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((15298:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.4548366397735) 0.890574887988 0.00000013349 cs_right_v15p298_3 (-0.05053741925155) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((15298:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.708364811406) (-0.7058465087656) 0.00000012223 cs_right_v15p298_4 (-0.04427280835225) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((15298:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8719818894942 0.4895381337487 0.00000015227 cs_right_v15p298_5 0.03487926948896 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((15298:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8719818894942 0.4895381337487 0.00000015227 cs_right_v15p298_5 235.028804 (by norm_num) (by norm_num) 0.25812060797677 0.01032482431908 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.84460384170263:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((15298:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_28 : mainRemConst 5 (2:ℝ) 14.769891 ≤ 0.56636226 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 14.769891 (by norm_num) _ 0.04 1.60943791291421 0.56636226 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_28 : ∀ y ∈ Set.Icc (((14736:ℤ):ℝ)/1000) (((15298:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((14736:ℤ):ℝ)/1000) (((15298:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 14.769891 14.736 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.56636226 rb_right_28 0.04 15.428183 15.589382 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.741512079073 0.834279017383 (by rw [hrot]; exact bv_right_14p736_0_5_c1) (by rw [hrot]; exact bv_right_15p298_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_15p86_0_5_c1 : (0.967413533985:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((15860:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((15860:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((15860:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((15860:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((15860:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.0022599712813) 0.9999974462615 0.00000013482 cs_right_v15p86_2 (-0.00056502652533) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((15860:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.1447213250722 0.9894724544267 0.0000001274 cs_right_v15p86_3 0.01608013307468 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((15860:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.9999897842383) (-0.0045200378978) 0.00000015345 cs_right_v15p86_4 (-0.06249937110552) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((15860:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9237857403356 (-0.3829097882695) 0.00000014577 cs_right_v15p86_5 0.03695142378262 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((15860:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9237857403356 (-0.3829097882695) 0.00000014577 cs_right_v15p86_5 252.5396 (by norm_num) (by norm_num) 0.56384063101463 0.02255362524059 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.98996715922645:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((15860:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_29 : mainRemConst 5 (2:ℝ) 15.330649 ≤ 0.56496676 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 15.330649 (by norm_num) _ 0.04 1.60943791291421 0.56496676 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_29 : ∀ y ∈ Set.Icc (((15298:ℤ):ℝ)/1000) (((15860:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((15298:ℤ):ℝ)/1000) (((15860:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 15.330649 15.298 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.56496676 rb_right_29 0.04 15.985607 16.14124 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.834279017383 0.967413533985 (by rw [hrot]; exact bv_right_15p298_0_5_c1) (by rw [hrot]; exact bv_right_15p86_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_16p422_0_5_c1 : (1.120425385887:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((16422:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((16422:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((16422:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((16422:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((16422:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.3776793396622 0.925936453755 0.00000011949 cs_right_v16p422_2 0.09441980504305 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((16422:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.6908408709 0.7230068402817 0.00000012131 cs_right_v16p422_3 0.07676008328777 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((16422:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.7147166327808) 0.6994141368318 0.00000013896 cs_right_v16p422_4 (-0.0446697982338) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((16422:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.2699567628003 (-0.962872445456) 0.00000013928 cs_right_v16p422_5 0.01079826494081 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((16422:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.2699567628003 (-0.962872445456) 0.00000013928 cs_right_v16p422_5 270.682084 (by norm_num) (by norm_num) 0.42207422876541 0.01688296915062 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.13730835503783:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((16422:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_30 : mainRemConst 5 (2:ℝ) 15.891494 ≤ 0.56367352 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 15.891494 (by norm_num) _ 0.04 1.60943791291421 0.56367352 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_30 : ∀ y ∈ Set.Icc (((15860:ℤ):ℝ)/1000) (((16422:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((15860:ℤ):ℝ)/1000) (((16422:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 15.891494 15.86 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.56367352 rb_right_30 0.04 16.54334 16.693774 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.967413533985 1.120425385887 (by rw [hrot]; exact bv_right_15p86_0_5_c1) (by rw [hrot]; exact bv_right_16p422_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_16p984_0_5_c1 : (1.261599572047:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((16984:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((16984:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((16984:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((16984:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((16984:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.7010275897904 0.7131341517223 0.00000010436 cs_right_v16p984_2 0.1752568713576 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((16984:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.9818670922616 0.1895706019767 0.00000011523 cs_right_v16p984_3 0.10909633078127 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((16984:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.0171206367055) 0.9998534311581 0.00000010871 cs_right_v16p984_4 (-0.00107004658847) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((16984:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.5900784222527) (-0.8073459330303) 0.00000013278 cs_right_v16p984_5 (-0.02360314220131) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((16984:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.5900784222527) (-0.8073459330303) 0.00000013278 cs_right_v16p984_5 289.456256 (by norm_num) (by norm_num) (-0.04798896746889) (-0.00191955869875) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.25968001334909:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((16984:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_31 : mainRemConst 5 (2:ℝ) 16.452418 ≤ 0.56247172 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 16.452418 (by norm_num) _ 0.04 1.60943791291421 0.56247172 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_31 : ∀ y ∈ Set.Icc (((16422:ℤ):ℝ)/1000) (((16984:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((16422:ℤ):ℝ)/1000) (((16984:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 16.452418 16.422 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.56247172 rb_right_31 0.04 17.101353 17.246921 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.120425385887 1.261599572047 (by rw [hrot]; exact bv_right_16p422_0_5_c1) (by rw [hrot]; exact bv_right_16p984_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_17p546_0_5_c1 : (1.353095410944:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((17546:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((17546:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((17546:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((17546:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((17546:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.9193346295558 0.3934766052759 0.00000011997 cs_right_v17p546_2 0.22983362739645 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((17546:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.9103384166861 (-0.4138646724541) 0.00000010914 cs_right_v17p546_3 0.10114870083844 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((17546:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.6903523222011 0.7234733383004 0.00000013993 cs_right_v17p546_4 0.04314701139194 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((17546:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9993827850515) (-0.0351290241479) 0.00000012629 cs_right_v17p546_5 (-0.03997531645366) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((17546:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9993827850515) (-0.0351290241479) 0.00000012629 cs_right_v17p546_5 308.862116 (by norm_num) (by norm_num) (-0.47353469428949) (-0.01894138777157) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.33415402317317:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((17546:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_32 : mainRemConst 5 (2:ℝ) 17.013414 ≤ 0.56135201 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 17.013414 (by norm_num) _ 0.04 1.60943791291421 0.56135201 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_32 : ∀ y ∈ Set.Icc (((16984:ℤ):ℝ)/1000) (((17546:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((16984:ℤ):ℝ)/1000) (((17546:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 17.013414 16.984 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.56135201 rb_right_32 0.04 17.659619 17.800622 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.261599572047 1.353095410944 (by rw [hrot]; exact bv_right_16p984_0_5_c1) (by rw [hrot]; exact bv_right_17p546_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_18p108_0_5_c1 : (1.363409732534:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((18108:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((18108:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((18108:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((18108:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((18108:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.9998895699414 0.0148609529439 0.00000013558 cs_right_v18p108_2 0.24997235859035 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((18108:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.5026668420963 (-0.8644802171576) 0.00000010603 cs_right_v18p108_3 0.05585185956291 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((18108:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.9995583071271 0.0297185237401 0.00000014699 cs_right_v18p108_4 0.06247238500856 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((18108:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6453095861607) 0.7639211595399 0.00000012697 cs_right_v18p108_5 (-0.02581238852523) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((18108:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6453095861607) 0.7639211595399 0.00000012697 cs_right_v18p108_5 328.899664 (by norm_num) (by norm_num) (-0.52313794745879) (-0.02092551789835) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.34248421463659:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((18108:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_33 : mainRemConst 5 (2:ℝ) 17.574473 ≤ 0.56030627 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 17.574473 (by norm_num) _ 0.04 1.60943791291421 0.56030627 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_33 : ∀ y ∈ Set.Icc (((17546:ℤ):ℝ)/1000) (((18108:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((17546:ℤ):ℝ)/1000) (((18108:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 17.574473 17.546 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.56030627 rb_right_33 0.04 18.218114 18.354827 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.353095410944 1.363409732534 (by rw [hrot]; exact bv_right_17p546_0_5_c1) (by rw [hrot]; exact bv_right_18p108_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_18p67_0_5_c1 : (1.282955635067:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((18670:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((18670:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((18670:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((18670:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((18670:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.9306221464353 (-0.3659814483879) 0.00000015119 cs_right_v18p67_2 0.23265549881132 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((18670:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.090614706151) (-0.9958860251197) 0.00000011239 cs_right_v18p67_3 (-0.01006831317124) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((18670:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.7321150907537 (-0.68118095532) 0.00000011633 cs_right_v18p67_4 0.04575718590148 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((18670:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.2016827054168 0.9794509106309 0.00000012047 cs_right_v18p67_5 0.00806730339787 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((18670:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.2016827054168 0.9794509106309 0.00000012047 cs_right_v18p67_5 349.5689 (by norm_num) (by norm_num) (-0.16359900321191) (-0.00654396012847) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.27641167493943:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((18670:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_34 : mainRemConst 5 (2:ℝ) 18.135591 ≤ 0.55932741 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 18.135591 (by norm_num) _ 0.04 1.60943791291421 0.55932741 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_34 : ∀ y ∈ Set.Icc (((18108:ℤ):ℝ)/1000) (((18670:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((18108:ℤ):ℝ)/1000) (((18670:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 18.135591 18.108 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.55932741 rb_right_34 0.04 18.776819 18.909493 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.363409732534 1.282955635067 (by rw [hrot]; exact bv_right_18p108_0_5_c1) (by rw [hrot]; exact bv_right_18p67_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_19p232_0_5_c1 : (1.133860511637:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((19232:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((19232:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((19232:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((19232:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((19232:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.721911245118 (-0.6919856603804) 0.00000014284 cs_right_v19p232_2 0.1804777755695 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((19232:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.6504367304869) (-0.7595604384225) 0.00000011876 cs_right_v19p232_3 (-0.0722707610275) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((19232:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.0423117915662 (-0.9991044551469) 0.00000013359 cs_right_v19p232_4 0.00264447862351 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((19232:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8946198610006 0.4468280478029 0.00000011398 cs_right_v19p232_5 0.03578478988082 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((19232:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8946198610006 0.4468280478029 0.00000011398 cs_right_v19p232_5 370.869824 (by norm_num) (by norm_num) 0.31939428521059 0.01277577140843 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.14663628304633:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((19232:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_35 : mainRemConst 5 (2:ℝ) 18.696761 ≤ 0.55840923 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 18.696761 (by norm_num) _ 0.04 1.60943791291421 0.55840923 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_35 : ∀ y ∈ Set.Icc (((18670:ℤ):ℝ)/1000) (((19232:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((18670:ℤ):ℝ)/1000) (((19232:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 18.696761 18.67 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.55840923 rb_right_35 0.04 19.335714 19.464579 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.282955635067 1.133860511637 (by rw [hrot]; exact bv_right_18p67_0_5_c1) (by rw [hrot]; exact bv_right_19p232_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_19p794_0_5_c1 : (0.965716340652:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((19794:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((19794:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((19794:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((19794:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((19794:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.4050299858724 (-0.9143034018006) 0.00000012752 cs_right_v19p794_2 0.1012574645881 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((19794:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.9700846785702) (-0.2427667937166) 0.00000012512 cs_right_v19p794_3 (-0.10778720041011) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((19794:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.6719014210862) (-0.7406405878176) 0.00000015502 cs_right_v19p794_4 (-0.04199384850664) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((19794:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9042025164267 (-0.42710397948) 0.00000011234 cs_right_v19p794_5 0.03616809616346 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((19794:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9042025164267 (-0.42710397948) 0.00000011234 cs_right_v19p794_5 392.802436 (by norm_num) (by norm_num) 0.54820427954824 0.02192817118193 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.98764451183481:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((19794:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_36 : mainRemConst 5 (2:ℝ) 19.25798 ≤ 0.55754626 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 19.25798 (by norm_num) _ 0.04 1.60943791291421 0.55754626 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_36 : ∀ y ∈ Set.Icc (((19232:ℤ):ℝ)/1000) (((19794:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((19232:ℤ):ℝ)/1000) (((19794:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 19.25798 19.232 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.55754626 rb_right_36 0.04 19.894785 20.020051 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.133860511637 0.965716340652 (by rw [hrot]; exact bv_right_19p232_0_5_c1) (by rw [hrot]; exact bv_right_19p794_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_20p356_0_5_c1 : (0.835971163055:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((20356:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((20356:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((20356:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((20356:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((20356:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.0274594747786 (-0.9996229175268) 0.00000011219 cs_right_v20p356_2 0.00686484064715 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((20356:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.9315283891555) 0.3636686129362 0.00000012431 cs_right_v20p356_3 (-0.10350316816292) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((20356:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.9984919542222) (-0.054898240326) 0.00000012436 cs_right_v20p356_4 (-0.06240575491139) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((20356:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.2231109697811 (-0.97479305248) 0.0000001194 cs_right_v20p356_5 0.00892443401524 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((20356:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.2231109697811 (-0.97479305248) 0.0000001194 cs_right_v20p356_5 415.366736 (by norm_num) (by norm_num) 0.34772971330887 0.01390918853236 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.84988035158808:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((20356:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_37 : mainRemConst 5 (2:ℝ) 19.819244 ≤ 0.55673367 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 19.819244 (by norm_num) _ 0.04 1.60943791291421 0.55673367 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_37 : ∀ y ∈ Set.Icc (((19794:ℤ):ℝ)/1000) (((20356:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((19794:ℤ):ℝ)/1000) (((20356:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 19.819244 19.794 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.55673367 rb_right_37 0.04 20.454016 20.575878 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.965716340652 0.835971163055 (by rw [hrot]; exact bv_right_19p794_0_5_c1) (by rw [hrot]; exact bv_right_20p356_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_20p918_0_5_c1 : (0.78335230939:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((20918:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((20918:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((20918:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((20918:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((20918:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.354225534102) (-0.9351600242674) 0.00000011363 cs_right_v20p918_2 (-0.088556411933) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((20918:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.5490047914201) 0.8358192023334 0.00000013068 cs_right_v20p918_3 (-0.06100054690006) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((20918:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.7490485372183) 0.6625151234934 0.00000012007 cs_right_v20p918_4 (-0.04681554108052) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((20918:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6284036714991) (-0.7778874119253) 0.00000012646 cs_right_v20p918_5 (-0.02513615191837) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((20918:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6284036714991) (-0.7778874119253) 0.00000012646 cs_right_v20p918_5 438.562724 (by norm_num) (by norm_num) (-0.12152403056692) (-0.00486096122267) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.77849134816805:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((20918:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_38 : mainRemConst 5 (2:ℝ) 20.380547 ≤ 0.55596719 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 20.380547 (by norm_num) _ 0.04 1.60943791291421 0.55596719 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_38 : ∀ y ∈ Set.Icc (((20356:ℤ):ℝ)/1000) (((20918:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((20356:ℤ):ℝ)/1000) (((20918:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 20.380547 20.356 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.55596719 rb_right_38 0.04 21.013394 21.132031 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.835971163055 0.78335230939 (by rw [hrot]; exact bv_right_20p356_0_5_c1) (by rw [hrot]; exact bv_right_20p918_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_21p48_0_5_c1 : (0.808792751305:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((21480:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
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
lemma rb_right_39 : mainRemConst 5 (2:ℝ) 20.941889 ≤ 0.555243 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 20.941889 (by norm_num) _ 0.04 1.60943791291421 0.555243 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_39 : ∀ y ∈ Set.Icc (((20918:ℤ):ℝ)/1000) (((21480:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((20918:ℤ):ℝ)/1000) (((21480:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 20.941889 20.918 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.555243 rb_right_39 0.04 21.572909 21.688486 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.78335230939 0.808792751305 (by rw [hrot]; exact bv_right_20p918_0_5_c1) (by rw [hrot]; exact bv_right_21p48_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)

end H22
end Cert
end ZB
end RHV6Fresh
