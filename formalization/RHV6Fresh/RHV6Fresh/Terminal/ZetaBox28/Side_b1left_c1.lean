/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig0
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig1
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig2
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig3
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig4
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig5
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig6
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig7
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig8
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig9
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig10
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig11
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig12
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig13
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig14
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig15
import RHV6Fresh.Terminal.ZetaBox28.Side_b1left_trig16
/-!
# Certificat (V2), côté b1left (b1), morceaux 1

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
lemma bv_b1left_4p212_0_5_c1 : (0.561290707175:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((4212:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((4212:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((4212:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((4212:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((4212:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.9754465408301) (-0.2202363405179) 0.00000012554 cs_b1left_v4p212_2 (-0.82024960502189) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((4212:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.0849315333043) 0.9963867896807 0.00000014842 cs_b1left_v4p212_3 (-0.06453412261653) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((4212:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.9029919115842 0.4296575469062 0.00000014389 cs_b1left_v4p212_4 0.63851160229215 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((4212:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8796040066162 (-0.4757066233981) 0.00000012221 cs_b1left_v4p212_5 0.58822656991622 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((4212:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8796040066162 (-0.4757066233981) 0.00000012221 cs_b1left_v4p212_5 18.303444 (by norm_num) (by norm_num) 1.16736456825691 0.78066373739489 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.34195444456995:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((4212:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b1left_4p527_0_5_c1 : (0.572125096336:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((4527:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((4527:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((4527:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((4527:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((4527:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.9999930977437) (-0.0037153447408) 0.0000001148 cs_b1left_v4p527_2 (-0.84089070770613) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((4527:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.2580746635627 0.9661249753665 0.00000012472 cs_b1left_v4p527_3 0.19609424417073 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((4527:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.9999723924758 0.0074306316188 0.00000013676 cs_b1left_v4p527_4 0.707087163015 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((4527:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.5379945657744 (-0.8429483063612) 0.0000001246 cs_b1left_v4p527_5 0.35977856666657 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((4527:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.5379945657744 (-0.8429483063612) 0.0000001246 cs_b1left_v4p527_5 21.056229 (by norm_num) (by norm_num) 1.27096297843097 0.84994416980977 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.42206926614617:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((4527:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_20 : mainRemConst 5 (1/4:ℝ) 4.278252 ≤ 7.63954441 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 4.278252 (by norm_num) _ 0.6687403049765 1.60943791291421 7.63954441 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_20 : ∀ y ∈ Set.Icc (((4212:ℤ):ℝ)/1000) (((4527:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((4212:ℤ):ℝ)/1000) (((4527:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 4.278252 4.212 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 7.63954441 rb_b1left_20 0.6687403049765 4.533898 4.696406 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.561290707175 0.572125096336 (by rw [hrot]; exact bv_b1left_4p212_0_5_c1) (by rw [hrot]; exact bv_b1left_4p527_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_4p842_0_5_c1 : (0.595735374814:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((4842:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((4842:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((4842:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((4842:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((4842:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.9770561275763) 0.2129819787187 0.00000014227 cs_b1left_v4p842_2 (-0.82160311481501) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((4842:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.5704812804229 0.8213106042704 0.00000010672 cs_b1left_v4p842_3 0.43347195377181 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((4842:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.9092773147211 (-0.4161907794914) 0.00000011317 cs_b1left_v4p842_4 0.64295607519506 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((4842:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.0610452486592 (-0.9981349996949) 0.00000013771 cs_b1left_v4p842_5 0.04082332611348 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((4842:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.0610452486592 (-0.9981349996949) 0.00000013771 cs_b1left_v4p842_5 24.007464 (by norm_num) (by norm_num) 1.04661385031212 0.69991286545036 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.29564824026534:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((4842:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_21 : mainRemConst 5 (1/4:ℝ) 4.588706 ≤ 7.4560456 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 4.588706 (by norm_num) _ 0.6687403049765 1.60943791291421 7.4560456 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_21 : ∀ y ∈ Set.Icc (((4527:ℤ):ℝ)/1000) (((4842:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((4527:ℤ):ℝ)/1000) (((4842:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 4.588706 4.527 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 7.4560456 rb_b1left_21 0.6687403049765 4.84845 5.000747 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.572125096336 0.595735374814 (by rw [hrot]; exact bv_b1left_4p527_0_5_c1) (by rw [hrot]; exact bv_b1left_4p842_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_5p157_0_5_c1 : (0.637057754479:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((5157:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((5157:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((5157:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((5157:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((5157:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.9077247465762) 0.4195661858723 0.00000010422 cs_b1left_v5p157_2 (-0.76330257307132) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((5157:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.8152464473879 0.5791141770164 0.00000013587 cs_b1left_v5p157_3 0.61945324008705 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((5157:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.6479284367005 (-0.7617012149884) 0.00000011561 cs_b1left_v5p157_4 0.45815450956587 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((5157:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.431260738361) (-0.9022273413859) 0.00000010973 cs_b1left_v5p157_5 (-0.2884015110768) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((5157:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.431260738361) (-0.9022273413859) 0.00000010973 cs_b1left_v5p157_5 27.157149 (by norm_num) (by norm_num) 0.58146025913377 0.38884591102484 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.0259036655048:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((5157:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_22 : mainRemConst 5 (1/4:ℝ) 4.899741 ≤ 7.29862867 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 4.899741 (by norm_num) _ 0.6687403049765 1.60943791291421 7.29862867 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_22 : ∀ y ∈ Set.Icc (((4842:ℤ):ℝ)/1000) (((5157:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((4842:ℤ):ℝ)/1000) (((5157:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 4.899741 4.842 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 7.29862867 rb_b1left_22 0.6687403049765 5.163057 5.306332 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.595735374814 0.637057754479 (by rw [hrot]; exact bv_b1left_4p842_0_5_c1) (by rw [hrot]; exact bv_b1left_5p157_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_5p472_0_5_c1 : (0.697574046959:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((5472:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((5472:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((5472:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((5472:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((5472:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.7952910771042) 0.6062277646487 0.00000013659 cs_b1left_v5p472_2 (-0.6687575306783) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((5472:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9633485529713 0.2682528014542 0.00000013774 cs_b1left_v5p472_3 0.73198650360856 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((5472:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.264975898022 (-0.9642550354898) 0.00000013951 cs_b1left_v5p472_4 0.18736615569387 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((5472:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.8150772802357) (-0.5793522479357) 0.0000001523 cs_b1left_v5p472_5 (-0.54507513081339) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((5472:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.8150772802357) (-0.5793522479357) 0.0000001523 cs_b1left_v5p472_5 30.505284 (by norm_num) (by norm_num) 0.01188196792066 0.00794595085099 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.70551999781074:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((5472:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_23 : mainRemConst 5 (1/4:ℝ) 5.211252 ≤ 7.16216612 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 5.211252 (by norm_num) _ 0.6687403049765 1.60943791291421 7.16216612 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_23 : ∀ y ∈ Set.Icc (((5157:ℤ):ℝ)/1000) (((5472:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((5157:ℤ):ℝ)/1000) (((5472:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 5.211252 5.157 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 7.16216612 rb_b1left_23 0.6687403049765 5.477708 5.612957 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.637057754479 0.697574046959 (by rw [hrot]; exact bv_b1left_5p157_0_5_c1) (by rw [hrot]; exact bv_b1left_5p472_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_5p787_0_5_c1 : (0.774638859668:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((5787:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((5787:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((5787:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((5787:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((5787:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.6450939819171) 0.7641032354846 0.00000012813 cs_b1left_v5p787_2 (-0.54245732463995) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((5787:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9972273490857 (-0.0744151478902) 0.00000010875 cs_b1left_v5p787_3 0.75772884391082 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((5787:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.1677076004903) (-0.9858367819964) 0.0000001424 cs_b1left_v5p787_4 (-0.11858728225523) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((5787:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.9938501691364) (-0.110733196698) 0.00000011095 cs_b1left_v5p787_5 (-0.66462773940596) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((5787:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.9938501691364) (-0.110733196698) 0.00000011095 cs_b1left_v5p787_5 34.051869 (by norm_num) (by norm_num) (-0.51228011757319) (-0.34258236205924) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.43205649760968:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((5787:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_24 : mainRemConst 5 (1/4:ℝ) 5.523158 ≤ 7.04277815 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 5.523158 (by norm_num) _ 0.6687403049765 1.60943791291421 7.04277815 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_24 : ∀ y ∈ Set.Icc (((5472:ℤ):ℝ)/1000) (((5787:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((5472:ℤ):ℝ)/1000) (((5787:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 5.523158 5.472 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 7.04277815 rb_b1left_24 0.6687403049765 5.792398 5.920462 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.697574046959 0.774638859668 (by rw [hrot]; exact bv_b1left_5p472_0_5_c1) (by rw [hrot]; exact bv_b1left_5p787_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_6p208_0_5_c1 : (0.892069752441:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((6208:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((6208:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((6208:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((6208:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((6208:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.3979959356337) 0.9173871784671 0.00000011189 cs_b1left_v6p208_2 (-0.33467344964787) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((6208:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.8592473296511 (-0.511560384009) 0.00000012076 cs_b1left_v6p208_3 0.6528866921119 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((6208:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.6831984651929) (-0.7302327417591) 0.00000011659 cs_b1left_v6p208_4 (-0.48309435007576) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((6208:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.8437241159806) 0.5367770636332 0.00000014903 cs_b1left_v6p208_5 (-0.56423242229927) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((6208:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.8437241159806) 0.5367770636332 0.00000014903 cs_b1left_v6p208_5 39.101764 (by norm_num) (by norm_num) (-0.92888566418055) (-0.6211832823523) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.270886470089:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((6208:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_25 : mainRemConst 5 (1/4:ℝ) 5.835397 ≤ 6.93747783 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 5.835397 (by norm_num) _ 0.6687403049765 1.60943791291421 6.93747783 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_25 : ∀ y ∈ Set.Icc (((5787:ℤ):ℝ)/1000) (((6208:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((5787:ℤ):ℝ)/1000) (((6208:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 5.835397 5.787 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 6.93747783 rb_b1left_25 0.6687403049765 6.213032 6.332596 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.774638859668 0.892069752441 (by rw [hrot]; exact bv_b1left_5p787_0_5_c1) (by rw [hrot]; exact bv_b1left_6p208_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_6p629_0_5_c1 : (1.007094709545:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((6629:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((6629:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((6629:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((6629:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((6629:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.1172459751671) 0.9931029056984 0.00000014899 cs_b1left_v6p629_2 (-0.09859184550611) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((6629:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.5407098510081 (-0.8412091636584) 0.00000014734 cs_b1left_v6p629_3 0.41085052842507 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((6629:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.9725067375433) (-0.2328747413304) 0.00000011588 cs_b1left_v6p629_4 (-0.68766619080606) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((6629:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.3208344425032) 0.9471352915512 0.00000011036 cs_b1left_v6p629_5 (-0.21455499672874) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((6629:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.3208344425032) 0.9471352915512 0.00000011036 cs_b1left_v6p629_5 44.506141 (by norm_num) (by norm_num) (-0.89280877751504) (-0.59705721416101) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.41003749538416:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((6629:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_26 : mainRemConst 5 (1/4:ℝ) 6.25314 ≤ 6.81475998 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 6.25314 (by norm_num) _ 0.6687403049765 1.60943791291421 6.81475998 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_26 : ∀ y ∈ Set.Icc (((6208:ℤ):ℝ)/1000) (((6629:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((6208:ℤ):ℝ)/1000) (((6629:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 6.25314 6.208 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 6.81475998 rb_b1left_26 0.6687403049765 6.633713 6.745824 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.892069752441 1.007094709545 (by rw [hrot]; exact bv_b1left_6p208_0_5_c1) (by rw [hrot]; exact bv_b1left_6p629_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_7p05_0_5_c1 : (1.101923079779:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((7050:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((7050:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((7050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((7050:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((7050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.1734174340174 0.9848484114719 0.00000011748 cs_b1left_v7p05_2 0.14582599981921 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((7050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.1085507082865 (-0.9940909132119) 0.00000012964 cs_b1left_v7p05_3 0.08248060335373 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((7050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.9398527870964) 0.3415797687334 0.00000013494 cs_b1left_v7p05_4 (-0.66457637448998) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((7050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.3438022894033 0.9390420575252 0.00000013538 cs_b1left_v7p05_5 0.22991435733308 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((7050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.3438022894033 0.9390420575252 0.00000013538 cs_b1left_v7p05_5 50.265 (by norm_num) (by norm_num) (-0.46098386992568) (-0.3082784937633) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.79364458601604:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((7050:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_27 : mainRemConst 5 (1/4:ℝ) 6.671292 ≤ 6.70881778 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 6.671292 (by norm_num) _ 0.6687403049765 1.60943791291421 6.70881778 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_27 : ∀ y ∈ Set.Icc (((6629:ℤ):ℝ)/1000) (((7050:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((6629:ℤ):ℝ)/1000) (((7050:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 6.671292 6.629 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 6.70881778 rb_b1left_27 0.6687403049765 7.054432 7.159959 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.007094709545 1.101923079779 (by rw [hrot]; exact bv_b1left_6p629_0_5_c1) (by rw [hrot]; exact bv_b1left_7p05_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_7p471_0_5_c1 : (1.170193831088:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((7471:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((7471:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((7471:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((7471:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((7471:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.4494179068262 0.8933216358199 0.00000012317 cs_b1left_v7p471_2 0.37791380322776 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((7471:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.3464187612035) (-0.9380799762728) 0.00000010327 cs_b1left_v7p471_3 (-0.26322141540988) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((7471:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.5960470900471) 0.8029494793788 0.00000014633 cs_b1left_v7p471_4 (-0.42146904274978) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((7471:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8565445445963 0.5160730986229 0.00000013304 cs_b1left_v7p471_5 0.57280577100999 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((7471:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8565445445963 0.5160730986229 0.00000013304 cs_b1left_v7p471_5 56.378341 (by norm_num) (by norm_num) 0.14330717660785 0.09583528499006 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.26602911607809:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((7471:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_28 : mainRemConst 5 (1/4:ℝ) 7.089781 ≤ 6.61645245 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 7.089781 (by norm_num) _ 0.6687403049765 1.60943791291421 6.61645245 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_28 : ∀ y ∈ Set.Icc (((7050:ℤ):ℝ)/1000) (((7471:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((7050:ℤ):ℝ)/1000) (((7471:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 7.089781 7.05 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 6.61645245 rb_b1left_28 0.6687403049765 7.475182 7.57485 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.101923079779 1.170193831088 (by rw [hrot]; exact bv_b1left_7p05_0_5_c1) (by rw [hrot]; exact bv_b1left_7p471_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_7p892_0_5_c1 : (1.220738944883:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((7892:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((7892:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((7892:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((7892:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((7892:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.6874184897292 0.7262615368987 0.00000014371 cs_b1left_v7p892_2 0.57804762294717 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((7892:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.7285937171808) (-0.6849461258053) 0.00000012708 cs_b1left_v7p892_3 (-0.55361160321545) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((7892:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.0549115401079) 0.9984912231776 0.00000012052 cs_b1left_v7p892_4 (-0.03882840759621) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((7892:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9908591019388 (-0.1349008528698) 0.00000011355 cs_b1left_v7p892_5 0.66262734208373 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((7892:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9908591019388 (-0.1349008528698) 0.00000011355 cs_b1left_v7p892_5 62.846164 (by norm_num) (by norm_num) 0.63925563653764 0.42749600933613 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.64823495421924:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((7892:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_29 : mainRemConst 5 (1/4:ℝ) 7.508551 ≤ 6.53522548 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 7.508551 (by norm_num) _ 0.6687403049765 1.60943791291421 6.53522548 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_29 : ∀ y ∈ Set.Icc (((7471:ℤ):ℝ)/1000) (((7892:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((7471:ℤ):ℝ)/1000) (((7892:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 7.508551 7.471 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 6.53522548 rb_b1left_29 0.6687403049765 7.895959 7.99038 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.170193831088 1.220738944883 (by rw [hrot]; exact bv_b1left_7p471_0_5_c1) (by rw [hrot]; exact bv_b1left_7p892_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_8p313_0_5_c1 : (1.273639658001:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((8313:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((8313:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((8313:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((8313:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((8313:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.8672955834251 0.4977935023394 0.00000010683 cs_b1left_v8p313_2 0.72930565723456 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((8313:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.9576660091984) (-0.2878815982317) 0.00000015053 cs_b1left_v8p313_3 (-0.72766892310257) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((8313:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.5044032580574 0.8634682120733 0.00000011364 cs_b1left_v8p313_4 0.35666688386933 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((8313:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.6874046906359 (-0.7262745977189) 0.00000015263 cs_b1left_v8p313_5 0.45969512038822 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((8313:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.6874046906359 (-0.7262745977189) 0.00000015263 cs_b1left_v8p313_5 69.668469 (by norm_num) (by norm_num) 0.81400668740488 0.54435908038805 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.81799873838954:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((8313:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_30 : mainRemConst 5 (1/4:ℝ) 7.927557 ≤ 6.46324668 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 7.927557 (by norm_num) _ 0.6687403049765 1.60943791291421 6.46324668 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_30 : ∀ y ∈ Set.Icc (((7892:ℤ):ℝ)/1000) (((8313:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((7892:ℤ):ℝ)/1000) (((8313:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 7.927557 7.892 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 6.46324668 rb_b1left_30 0.6687403049765 8.316759 8.406455 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.220738944883 1.273639658001 (by rw [hrot]; exact bv_b1left_7p892_0_5_c1) (by rw [hrot]; exact bv_b1left_8p313_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_8p734_0_5_c1 : (1.349567616984:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((8734:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((8734:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((8734:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((8734:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((8734:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9738398766318 0.2272353288591 0.00000013445 cs_b1left_v8p734_2 0.81889834823226 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((8734:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.9854997548443) 0.1696768482671 0.00000011698 cs_b1left_v8p734_3 (-0.74881797081719) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((8734:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.8967281663784 0.442581738918 0.00000013987 cs_b1left_v8p734_4 0.63408246842407 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((8734:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.0802498408886 (-0.9967747804982) 0.00000011705 cs_b1left_v8p734_5 0.05366622479409 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((8734:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.0802498408886 (-0.9967747804982) 0.00000011705 cs_b1left_v8p734_5 76.845256 (by norm_num) (by norm_num) 0.61049326713272 0.40826145364844 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.75782907063323:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((8734:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_31 : mainRemConst 5 (1/4:ℝ) 8.346763 ≤ 6.39902874 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 8.346763 (by norm_num) _ 0.6687403049765 1.60943791291421 6.39902874 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_31 : ∀ y ∈ Set.Icc (((8313:ℤ):ℝ)/1000) (((8734:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((8313:ℤ):ℝ)/1000) (((8734:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 8.346763 8.313 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 6.39902874 rb_b1left_31 0.6687403049765 8.737578 8.822996 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.273639658001 1.349567616984 (by rw [hrot]; exact bv_b1left_8p313_0_5_c1) (by rw [hrot]; exact bv_b1left_8p734_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_9p155_0_5_c1 : (1.456894755077:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((9155:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((9155:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((9155:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((9155:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((9155:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9980426921203 (-0.0625362671197) 0.00000013306 cs_b1left_v9p155_2 0.83925041018443 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((9155:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.8062460563232) 0.5915803382564 0.000000114 cs_b1left_v9p155_3 (-0.61261461163151) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((9155:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.9921784181067 (-0.1248278280005) 0.00000014308 cs_b1left_v9p155_4 0.7015759864173 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((9155:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.5623600619274) (-0.8268924722959) 0.0000001308 cs_b1left_v9p155_5 (-0.37607292679117) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((9155:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.5623600619274) (-0.8268924722959) 0.0000001308 cs_b1left_v9p155_5 84.376525 (by norm_num) (by norm_num) 0.14242315349089 0.09524410310122 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.55213885817905:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((9155:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_32 : mainRemConst 5 (1/4:ℝ) 8.766142 ≤ 6.34138551 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 8.766142 (by norm_num) _ 0.6687403049765 1.60943791291421 6.34138551 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_32 : ∀ y ∈ Set.Icc (((8734:ℤ):ℝ)/1000) (((9155:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((8734:ℤ):ℝ)/1000) (((9155:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 8.766142 8.734 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 6.34138551 rb_b1left_32 0.6687403049765 9.158413 9.239942 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.349567616984 1.456894755077 (by rw [hrot]; exact bv_b1left_8p734_0_5_c1) (by rw [hrot]; exact bv_b1left_9p155_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_9p576_0_5_c1 : (1.582705079932:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((9576:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((9576:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((9576:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((9576:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((9576:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9378576157393 (-0.3470203057456) 0.00000010864 cs_b1left_v9p576_2 0.78864101573857 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((9576:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.4575722915199) 0.8891724231151 0.00000014058 cs_b1left_v9p576_3 (-0.3476798626799) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((9576:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.7591538148004 (-0.6509112731195) 0.00000011727 cs_b1left_v9p576_4 0.53680272748655 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((9576:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.9565150503998) (-0.2916829753973) 0.00000013972 cs_b1left_v9p576_5 (-0.63966025995537) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((9576:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.9565150503998) (-0.2916829753973) 0.00000013972 cs_b1left_v9p576_5 92.262276 (by norm_num) (by norm_num) (-0.36576449411307) (-0.24460145934271) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.33810362058985:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((9576:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_33 : mainRemConst 5 (1/4:ℝ) 9.185669 ≤ 6.28936032 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 9.185669 (by norm_num) _ 0.6687403049765 1.60943791291421 6.28936032 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_33 : ∀ y ∈ Set.Icc (((9155:ℤ):ℝ)/1000) (((9576:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((9155:ℤ):ℝ)/1000) (((9576:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 9.185669 9.155 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 6.28936032 rb_b1left_33 0.6687403049765 9.579263 9.65724 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.456894755077 1.582705079932 (by rw [hrot]; exact bv_b1left_9p155_0_5_c1) (by rw [hrot]; exact bv_b1left_9p576_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_9p997_0_5_c1 : (1.69267167042:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((9997:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((9997:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((9997:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((9997:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((9997:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.7983734783038 (-0.6021625936083) 0.00000014574 cs_b1left_v9p997_2 0.67134927338704 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((9997:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.0127469279842) 0.999918754613 0.00000013787 cs_b1left_v9p997_3 (-0.00968567552338) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((9997:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.274800517868 (-0.9615012612469) 0.00000011857 cs_b1left_v9p997_4 0.19431322581637 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((9997:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.9280746093814) 0.3723943061667 0.00000011615 cs_b1left_v9p997_5 (-0.62064097499285) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((9997:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.9280746093814) 0.3723943061667 0.00000011615 cs_b1left_v9p997_5 100.502509 (by norm_num) (by norm_num) (-0.68387656363814) (-0.45733582173358) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.23533584868718:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((9997:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_34 : mainRemConst 5 (1/4:ℝ) 9.605325 ≤ 6.24217273 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 9.605325 (by norm_num) _ 0.6687403049765 1.60943791291421 6.24217273 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_34 : ∀ y ∈ Set.Icc (((9576:ℤ):ℝ)/1000) (((9997:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((9576:ℤ):ℝ)/1000) (((9997:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 9.605325 9.576 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 6.24217273 rb_b1left_34 0.6687403049765 10.000126 10.074846 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.582705079932 1.69267167042 (by rw [hrot]; exact bv_b1left_9p576_0_5_c1) (by rw [hrot]; exact bv_b1left_9p997_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_10p418_0_5_c1 : (1.741086867155:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((10418:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((10418:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((10418:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((10418:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((10418:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.5913842201444 (-0.8063899206738) 0.00000012241 cs_b1left_v10p418_2 0.4972927678229 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((10418:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.4347570930836 0.9005477610952 0.0000001115 cs_b1left_v10p418_3 0.33034386919335 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((10418:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.3005294083286) (-0.9537725487389) 0.0000001448 cs_b1left_v10p418_4 (-0.21250648496422) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((10418:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.4896039436222) 0.8719449399955 0.00000015522 cs_b1left_v10p418_5 (-0.32741799437748) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((10418:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.4896039436222) 0.8719449399955 0.00000015522 cs_b1left_v10p418_5 109.097224 (by norm_num) (by norm_num) (-0.67795331925902) (-0.45337470948103) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.28771215767455:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((10418:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_35 : mainRemConst 5 (1/4:ℝ) 10.025093 ≤ 6.19918012 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 10.025093 (by norm_num) _ 0.6687403049765 1.60943791291421 6.19918012 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_35 : ∀ y ∈ Set.Icc (((9997:ℤ):ℝ)/1000) (((10418:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((9997:ℤ):ℝ)/1000) (((10418:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 10.025093 9.997 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 6.19918012 rb_b1left_35 0.6687403049765 10.421 10.492723 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.69267167042 1.741086867155 (by rw [hrot]; exact bv_b1left_9p997_0_5_c1) (by rw [hrot]; exact bv_b1left_10p418_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_10p839_0_5_c1 : (1.687694203993:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((10839:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((10839:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((10839:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((10839:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((10839:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.3343913483584 (-0.9424343086619) 0.00000011992 cs_b1left_v10p839_2 0.28118838528613 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((10839:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.7909036744583 0.6119406652024 0.00000012032 cs_b1left_v10p839_3 0.60095674434288 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((10839:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.7763648522785) (-0.6302837584021) 0.00000013983 cs_b1left_v10p839_4 (-0.54897295059581) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((10839:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.1651774468143 0.9862638648272 0.00000011655 cs_b1left_v10p839_5 0.11046073821613 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((10839:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.1651774468143 0.9862638648272 0.00000011655 cs_b1left_v10p839_5 118.046421 (by norm_num) (by norm_num) (-0.36495674767588) (-0.24406128674396) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.44363291724933:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((10839:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_36 : mainRemConst 5 (1/4:ℝ) 10.444961 ≤ 6.15984833 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 10.444961 (by norm_num) _ 0.6687403049765 1.60943791291421 6.15984833 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_36 : ∀ y ∈ Set.Icc (((10418:ℤ):ℝ)/1000) (((10839:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((10418:ℤ):ℝ)/1000) (((10839:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 10.444961 10.418 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 6.15984833 rb_b1left_36 0.6687403049765 10.841883 10.91084 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.741086867155 1.687694203993 (by rw [hrot]; exact bv_b1left_10p418_0_5_c1) (by rw [hrot]; exact bv_b1left_10p839_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_11p154_0_5_c1 : (1.569214794956:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((11154:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((11154:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((11154:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.1223109936732 (-0.9924918240603) 0.00000014748 cs_b1left_v11p154_2 0.1028507521105 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9515835954359 0.3073900793736 0.00000014947 cs_b1left_v11p154_3 0.72304706012011 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.970080065826) (-0.2427852252817) 0.00000011624 cs_b1left_v11p154_4 (-0.68595027503361) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.623265000345 0.7820107028327 0.00000015206 cs_b1left_v11p154_5 0.41680232472318 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.623265000345 0.7820107028327 0.00000015206 cs_b1left_v11p154_5 124.974216 (by norm_num) (by norm_num) (-0.01863942242379) (-0.01246493303626) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.55674986192018:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((11154:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_37 : mainRemConst 5 (1/4:ℝ) 10.864916 ≤ 6.12373022 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 10.864916 (by norm_num) _ 0.6687403049765 1.60943791291421 6.12373022 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_37 : ∀ y ∈ Set.Icc (((10839:ℤ):ℝ)/1000) (((11154:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((10839:ℤ):ℝ)/1000) (((11154:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 10.864916 10.839 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 6.12373022 rb_b1left_37 0.6687403049765 11.156802 11.223824 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.687694203993 1.569214794956 (by rw [hrot]; exact bv_b1left_10p839_0_5_c1) (by rw [hrot]; exact bv_b1left_11p154_0_5_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_11p154_0_10_c1 : (1.439166274377:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1/4:ℝ):ℝ)):ℂ) + ((((((11154:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((11154:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((11154:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.1223109936732 (-0.9924918240603) 0.00000014748 cs_b1left_v11p154_2 0.1028507521105 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9515835954359 0.3073900793736 0.00000014947 cs_b1left_v11p154_3 0.72304706012011 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.970080065826) (-0.2427852252817) 0.00000011624 cs_b1left_v11p154_4 (-0.68595027503361) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.623265000345 0.7820107028327 0.00000015206 cs_b1left_v11p154_5 0.41680232472318 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6389431042462 0.6389431042463 (pwl_6_1_4 (1/4:ℝ) (by norm_num)) (pwh_6_1_4 (1/4:ℝ) (by norm_num)) 0.4214712756965 (-0.9068417523266) 0.00000010758 cs_b1left_v11p154_6 0.26929609650662 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6147881529512 0.6147881529513 (pwl_7_1_4 (1/4:ℝ) (by norm_num)) (pwh_7_1_4 (1/4:ℝ) (by norm_num)) (-0.9592482317273) (-0.2825647354101) 0.00000012479 cs_b1left_v11p154_7 (-0.58973452532485) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_8_1_4 (1/4:ℝ) (by norm_num)) (pwh_8_1_4 (1/4:ℝ) (by norm_num)) (-0.3596138013384) 0.9331012345316 0.00000013523 cs_b1left_v11p154_8 (-0.21382772601066) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5773502691896 0.5773502691897 (pwl_9_1_4 (1/4:ℝ) (by norm_num)) (pwh_9_1_4 (1/4:ℝ) (by norm_num)) 0.8110226197039 0.5850147949656 0.00000011226 cs_b1left_v11p154_9 0.46824406299156 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5623413251903 0.5623413251904 (pwl_10_1_4 (1/4:ℝ) (by norm_num)) (pwh_10_1_4 (1/4:ℝ) (by norm_num)) 0.8523713904031 (-0.5229369109388) 0.00000011018 cs_b1left_v11p154_10 0.47932359527481 (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5623413251903 0.5623413251904 (pwl_10_1_4 (1/4:ℝ) (by norm_num)) (pwh_10_1_4 (1/4:ℝ) (by norm_num)) 0.8523713904031 (-0.5229369109388) 0.00000011018 cs_b1left_v11p154_10 124.974216 (by norm_num) (by norm_num) 0.94406202638649 0.53088509098012 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.97005136535766:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((11154:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma bv_b1left_11p469_0_10_c1 : (1.288281961161:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1/4:ℝ):ℝ)):ℂ) + ((((((11469:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((11469:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((11469:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((11469:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((11469:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.0955772551917) (-0.9954220151723) 0.00000010943 cs_b1left_v11p469_2 (-0.0803706632898) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((11469:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9994351127771 (-0.0336073704451) 0.00000012714 cs_b1left_v11p469_3 0.75940636757566 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((11469:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.981729975075) 0.1902794148179 0.00000011167 cs_b1left_v11p469_4 (-0.6941880016323) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((11469:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.924561752911 0.38103223624 0.00000010981 cs_b1left_v11p469_5 0.61829163517684 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1/4:ℝ) (((11469:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6389431042462 0.6389431042463 (pwl_6_1_4 (1/4:ℝ) (by norm_num)) (pwh_6_1_4 (1/4:ℝ) (by norm_num)) (-0.1289767812345) (-0.9916476137731) 0.00000013656 cs_b1left_v11p469_6 (-0.08240891223174) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1/4:ℝ) (((11469:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6147881529512 0.6147881529513 (pwl_7_1_4 (1/4:ℝ) (by norm_num)) (pwh_7_1_4 (1/4:ℝ) (by norm_num)) (-0.9471723157624) 0.3207251222733 0.00000013518 cs_b1left_v11p469_7 (-0.58231040164124) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1/4:ℝ) (((11469:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_8_1_4 (1/4:ℝ) (by norm_num)) (pwh_8_1_4 (1/4:ℝ) (by norm_num)) 0.2832393750789 0.9590492460791 0.00000012108 cs_b1left_v11p469_8 0.16841506805176 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1/4:ℝ) (((11469:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5773502691896 0.5773502691897 (pwl_9_1_4 (1/4:ℝ) (by norm_num)) (pwh_9_1_4 (1/4:ℝ) (by norm_num)) 0.9977410893035 (-0.0671767721418) 0.00000015427 cs_b1left_v11p469_9 0.57604599742307 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1/4:ℝ) (((11469:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5623413251903 0.5623413251904 (pwl_10_1_4 (1/4:ℝ) (by norm_num)) (pwh_10_1_4 (1/4:ℝ) (by norm_num)) 0.2909208018454 (-0.9567471385134) 0.0000001111 cs_b1left_v11p469_10 0.16359672675904 (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1/4:ℝ) (((11469:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5623413251903 0.5623413251904 (pwl_10_1_4 (1/4:ℝ) (by norm_num)) (pwh_10_1_4 (1/4:ℝ) (by norm_num)) 0.2909208018454 (-0.9567471385134) 0.0000001111 cs_b1left_v11p469_10 132.100461 (by norm_num) (by norm_num) 0.99262819576811 0.5581958550296 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.84647781619129:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((11469:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma rb_b1left_38 : mainRemConst 10 (1/4:ℝ) 11.179186 ≤ 21.3967302 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1/4:ℝ) 0.6389431042463 1.791759469708165 (pwh_6_1_4 (1/4:ℝ) (by norm_num)) (lg_6).2 2.05126421802629 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1/4:ℝ) 0.6147881529513 1.945910149535424 (pwh_7_1_4 (1/4:ℝ) (by norm_num)) (lg_7).2 2.32793610779247 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1/4:ℝ) 0.5946035575014 2.0794415424 (pwh_8_1_4 (1/4:ℝ) (by norm_num)) (lg_8).2 2.57111164337318 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1/4:ℝ) 0.5773502691897 2.19722457781633 (pwh_9_1_4 (1/4:ℝ) (by norm_num)) (lg_9).2 2.7873292309116 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1/4:ℝ) 0.5623413251904 2.30258509371421 (pwh_10_1_4 (1/4:ℝ) (by norm_num)) (lg_10).2 2.9814764113359 (by norm_num))
  exact mainRemConst_le 10 (by norm_num) (1/4:ℝ) 11.179186 (by norm_num) _ 0.5623413251904 2.30258509371421 21.3967302 c10 (pwh_10_1_4 (1/4:ℝ) (by norm_num)) (lg_10).2 (by norm_num)
lemma pc_b1left_38 : ∀ y ∈ Set.Icc (((11154:ℤ):ℝ)/1000) (((11469:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 10 (by norm_num) (1/4:ℝ) (((11154:ℤ):ℝ)/1000) (((11469:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.30258509371421 (lg_10).2 (by norm_num) 11.179186 11.154 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 21.3967302 rb_b1left_38 0.5623413251904 11.471725 11.536918 (pwh_10_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.439166274377 1.288281961161 (by rw [hrot]; exact bv_b1left_11p154_0_10_c1) (by rw [hrot]; exact bv_b1left_11p469_0_10_c1) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_11p784_0_10_c1 : (1.129698230986:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1/4:ℝ):ℝ)):ℂ) + ((((((11784:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((11784:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((11784:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((11784:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((11784:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.3089271256169) (-0.9510857117296) 0.00000013454 cs_b1left_v11p784_2 (-0.25977582564012) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((11784:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9287845426908 (-0.3706201198782) 0.00000010777 cs_b1left_v11p784_3 0.70572355793048 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((11784:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.8091281166493) 0.5876322751472 0.00000013557 cs_b1left_v11p784_4 (-0.57214007399393) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((11784:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9932725484382 (-0.1158000195122) 0.00000014426 cs_b1left_v11p784_5 0.66424129049477 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1/4:ℝ) (((11784:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6389431042462 0.6389431042463 (pwl_6_1_4 (1/4:ℝ) (by norm_num)) (pwh_6_1_4 (1/4:ℝ) (by norm_num)) (-0.6394182395854) (-0.7688590994909) 0.0000001423 cs_b1left_v11p784_6 (-0.40855196583401) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1/4:ℝ) (((11784:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6147881529512 0.6147881529513 (pwl_7_1_4 (1/4:ℝ) (by norm_num)) (pwh_7_1_4 (1/4:ℝ) (by norm_num)) (-0.5902267217434) 0.8072375220025 0.00000013839 cs_b1left_v11p784_7 (-0.36286448116366) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1/4:ℝ) (((11784:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_8_1_4 (1/4:ℝ) (by norm_num)) (pwh_8_1_4 (1/4:ℝ) (by norm_num)) 0.808850284008 0.5880146410253 0.00000011077 cs_b1left_v11p784_8 0.48094519049285 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1/4:ℝ) (((11784:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5773502691896 0.5773502691897 (pwl_9_1_4 (1/4:ℝ) (by norm_num)) (pwh_9_1_4 (1/4:ℝ) (by norm_num)) 0.7252814534829 (-0.6884524771063) 0.00000011553 cs_b1left_v11p784_9 0.4187413757053 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1/4:ℝ) (((11784:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5623413251903 0.5623413251904 (pwl_10_1_4 (1/4:ℝ) (by norm_num)) (pwh_10_1_4 (1/4:ℝ) (by norm_num)) (-0.4169845773194) (-0.9089135614975) 0.00000011562 cs_b1left_v11p784_10 (-0.23448772481166) (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1/4:ℝ) (((11784:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5623413251903 0.5623413251904 (pwl_10_1_4 (1/4:ℝ) (by norm_num)) (pwh_10_1_4 (1/4:ℝ) (by norm_num)) (-0.4169845773194) (-0.9089135614975) 0.00000011562 cs_b1left_v11p784_10 139.425156 (by norm_num) (by norm_num) 0.53727709250527 0.30213311219386 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.43183134318002:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((11784:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma rb_b1left_39 : mainRemConst 10 (1/4:ℝ) 11.493496 ≤ 21.31788617 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1/4:ℝ) 0.6389431042463 1.791759469708165 (pwh_6_1_4 (1/4:ℝ) (by norm_num)) (lg_6).2 2.05126421802629 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1/4:ℝ) 0.6147881529513 1.945910149535424 (pwh_7_1_4 (1/4:ℝ) (by norm_num)) (lg_7).2 2.32793610779247 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1/4:ℝ) 0.5946035575014 2.0794415424 (pwh_8_1_4 (1/4:ℝ) (by norm_num)) (lg_8).2 2.57111164337318 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1/4:ℝ) 0.5773502691897 2.19722457781633 (pwh_9_1_4 (1/4:ℝ) (by norm_num)) (lg_9).2 2.7873292309116 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1/4:ℝ) 0.5623413251904 2.30258509371421 (pwh_10_1_4 (1/4:ℝ) (by norm_num)) (lg_10).2 2.9814764113359 (by norm_num))
  exact mainRemConst_le 10 (by norm_num) (1/4:ℝ) 11.493496 (by norm_num) _ 0.5623413251904 2.30258509371421 21.31788617 c10 (pwh_10_1_4 (1/4:ℝ) (by norm_num)) (lg_10).2 (by norm_num)
lemma pc_b1left_39 : ∀ y ∈ Set.Icc (((11469:ℤ):ℝ)/1000) (((11784:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 10 (by norm_num) (1/4:ℝ) (((11469:ℤ):ℝ)/1000) (((11784:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.30258509371421 (lg_10).2 (by norm_num) 11.493496 11.469 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 21.31788617 rb_b1left_39 0.5623413251904 11.786652 11.850113 (pwh_10_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.288281961161 1.129698230986 (by rw [hrot]; exact bv_b1left_11p469_0_10_c1) (by rw [hrot]; exact bv_b1left_11p784_0_10_c1) (by rw [lt_min_iff]; constructor <;> norm_num)

end H28
end Cert
end ZB
end RHV6Fresh
