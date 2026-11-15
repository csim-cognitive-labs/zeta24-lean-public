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
# Certificat (V2), côté b1left (b1), morceaux 0

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
lemma bv_b1left_m1_3_5_c0 : (0.556767974975:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((-1000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-1000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((-1000:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_b1left_vm1_2 0.53730015864917 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_b1left_vm1_3 0.67669213619214 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_b1left_vm1_4 0.69510548780509 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_b1left_vm1_5 0.66824101970217 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_b1left_vm1_5 1.5625 (by norm_num) (by norm_num) 3.02145812408317 2.02057082737311 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.57733880234857:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-1000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b1left_m0p92_3_5_c0 : (0.577616586105:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((-920:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-920:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((-920:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((-920:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((-920:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.8034699232432 0.5953453472092 0.00000010635 cs_b1left_vm0p92_2 0.50062367887685 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((-920:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.5312480688297 0.8472163179288 0.00000010581 cs_b1left_vm0p92_3 0.64374511143035 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((-920:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.2911278351128 0.9566841608507 0.00000011269 cs_b1left_vm0p92_4 0.67647777790738 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((-920:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.0899915163459 0.9959425319694 0.00000012105 cs_b1left_vm0p92_5 0.66602683161717 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((-920:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.0899915163459 0.9959425319694 0.00000012105 cs_b1left_vm0p92_5 1.4089 (by norm_num) (by norm_num) 2.85500484944363 1.90925681372632 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.48687339983175:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-920:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_0 : mainRemConst 5 (1/4:ℝ) 1.18697 ≤ 18.39430912 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 1.18697 (by norm_num) _ 0.6687403049765 1.60943791291421 18.39430912 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_0 : ∀ y ∈ Set.Icc (((-1000:ℤ):ℝ)/1000) (((-920:ℤ):ℝ)/1000), 0 < (I ^ ((-9):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-9):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-9) (-3) 3 (by norm_num), rot3])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (((-920:ℤ):ℝ)/1000) (I ^ ((-9):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.18697 0.92 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 18.39430912 rb_b1left_0 0.6687403049765 1.030777 1.600782 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.556767974975 0.577616586105 (by rw [hrot]; exact bv_b1left_m1_3_5_c0) (by rw [hrot]; exact bv_b1left_m0p92_3_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_m0p683_3_5_c0 : (0.610323180854:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((-683:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-683:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((-683:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((-683:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((-683:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.8900144340204 0.4559323494065 0.0000001245 cs_b1left_vm0p683_2 0.38339177352251 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((-683:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.7314487503264 0.6818964185607 0.00000010703 cs_b1left_vm0p683_3 0.51812915141515 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((-683:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.5842513855293 0.8115727438173 0.00000014899 cs_b1left_vm0p683_4 0.5738684852275 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((-683:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.4542678736866 0.8908651407123 0.00000010618 cs_b1left_vm0p683_5 0.59575735488594 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((-683:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.4542678736866 0.8908651407123 0.00000010618 cs_b1left_vm0p683_5 1.028989 (by norm_num) (by norm_num) 2.18444076620675 1.46082358419621 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.0711467650511:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-683:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_1 : mainRemConst 5 (1/4:ℝ) 1.01439 ≤ 22.24995155 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 1.01439 (by norm_num) _ 0.6687403049765 1.60943791291421 22.24995155 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_1 : ∀ y ∈ Set.Icc (((-920:ℤ):ℝ)/1000) (((-683:ℤ):ℝ)/1000), 0 < (I ^ ((-9):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-9):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-9) (-3) 3 (by norm_num), rot3])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((-920:ℤ):ℝ)/1000) (((-683:ℤ):ℝ)/1000) (I ^ ((-9):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.01439 0.683 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 22.24995155 rb_b1left_1 0.6687403049765 0.953363 1.552064 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.577616586105 0.610323180854 (by rw [hrot]; exact bv_b1left_m0p92_3_5_c0) (by rw [hrot]; exact bv_b1left_m0p683_3_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_m0p454_3_5_c0 : (0.55649163449:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((-454:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-454:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((-454:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((-454:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((-454:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9508927477582 0.3095205683971 0.0000001201 cs_b1left_vm0p454_2 0.26027463542074 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((-454:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.8781715913069 0.4783457496639 0.00000012108 cs_b1left_vm0p454_3 0.36346407867344 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((-454:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.8083940354783 0.5886417275416 0.00000014018 cs_b1left_vm0p454_4 0.41623245811177 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((-454:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.7447175553294 0.6673797740299 0.00000011248 cs_b1left_vm0p454_5 0.44630367839992 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((-454:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.7447175553294 0.6673797740299 0.00000011248 cs_b1left_vm0p454_5 0.768616 (by norm_num) (by norm_num) 1.39035019901854 0.9297832161158 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.48627485060587:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-454:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_2 : mainRemConst 5 (1/4:ℝ) 0.876707 ≤ 27.12117204 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.876707 (by norm_num) _ 0.6687403049765 1.60943791291421 27.12117204 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_2 : ∀ y ∈ Set.Icc (((-683:ℤ):ℝ)/1000) (((-454:ℤ):ℝ)/1000), 0 < (I ^ ((-9):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-9):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-9) (-3) 3 (by norm_num), rot3])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((-683:ℤ):ℝ)/1000) (((-454:ℤ):ℝ)/1000) (I ^ ((-9):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.876707 0.454 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 27.12117204 rb_b1left_2 0.6687403049765 0.727317 1.424426 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.610323180854 0.55649163449 (by rw [hrot]; exact bv_b1left_m0p683_3_5_c0) (by rw [hrot]; exact bv_b1left_m0p454_3_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_m0p454_2_5_c0 : (0.460396454753:ℝ) ≤ (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((-454:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-454:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((-454:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((-454:ℤ):ℝ)/1000)) (-1) (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((-454:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9508927477582 0.3095205683971 0.0000001201 cs_b1left_vm0p454_2 (-0.79960240387237) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((-454:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.8781715913069 0.4783457496639 0.00000012108 cs_b1left_vm0p454_3 (-0.66726620520134) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((-454:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.8083940354783 0.5886417275416 0.00000014018 cs_b1left_vm0p454_4 (-0.57162100347974) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((-454:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.7447175553294 0.6673797740299 0.00000011248 cs_b1left_vm0p454_5 (-0.49802272029225) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((-454:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.7447175553294 0.6673797740299 0.00000011248 cs_b1left_vm0p454_5 0.768616 (by norm_num) (by norm_num) (-5.97677268418832) (-3.99690878759871) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-3.5365123328457):ℝ) ≤ ∑ n ∈ Finset.range 5, (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-454:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b1left_m0p286_2_5_c0 : (0.647606345784:ℝ) ≤ (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((-286:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-286:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((-286:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((-286:ℤ):ℝ)/1000)) (-1) (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((-286:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9804146980618 0.1969442048511 0.00000010645 cs_b1left_vm0p286_2 (-0.82442729457573) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((-286:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9510429697324 0.309058683299 0.00000011464 cs_b1left_vm0p286_3 (-0.72263647409832) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((-286:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.9224259603512 0.3861739862682 0.00000011288 cs_b1left_vm0p286_4 (-0.65225373152511) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((-286:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8959196281463 0.4442161859975 0.00000014311 cs_b1left_vm0p286_5 (-0.59913766106442) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((-286:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8959196281463 0.4442161859975 0.00000014311 cs_b1left_vm0p286_5 0.644296 (by norm_num) (by norm_num) (-6.64841265579907) (-4.44606150704802) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-3.79845516126358):ℝ) ≤ ∑ n ∈ Finset.range 5, (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-286:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_3 : mainRemConst 5 (1/4:ℝ) 0.80268 ≤ 30.88664587 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.80268 (by norm_num) _ 0.6687403049765 1.60943791291421 30.88664587 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_3 : ∀ y ∈ Set.Icc (((-454:ℤ):ℝ)/1000) (((-286:ℤ):ℝ)/1000), 0 < (I ^ ((-10):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-10):ℤ) = (((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-10) (-3) 2 (by norm_num), rot2])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((-454:ℤ):ℝ)/1000) (((-286:ℤ):ℝ)/1000) (I ^ ((-10):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.80268 0.286 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 30.88664587 rb_b1left_3 0.6687403049765 0.518282 1.329894 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.460396454753 0.647606345784 (by rw [hrot]; exact bv_b1left_m0p454_2_5_c0) (by rw [hrot]; exact bv_b1left_m0p286_2_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_m0p066_2_5_c0 : (0.805858837825:ℝ) ≤ (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((-66:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-66:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((-66:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((-66:ℤ):ℝ)/1000)) (-1) (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((-66:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9989537564609 0.0457317444751 0.00000011395 cs_b1left_vm0p066_2 (-0.84001672863244) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((-66:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.99737241747 0.0724448816 0.00000011108 cs_b1left_vm0p066_3 (-0.75783923908086) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((-66:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.9958172150945 0.0913677958657 0.00000012788 cs_b1left_vm0p066_4 (-0.7041491960405) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((-66:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9943636504697 0.106023255112 0.00000010227 cs_b1left_vm0p066_5 (-0.66497111926473) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((-66:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9943636504697 0.106023255112 0.00000010227 cs_b1left_vm0p066_5 0.566856 (by norm_num) (by norm_num) (-7.13705318092404) (-4.77283512084392) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-3.96697628301853):ℝ) ≤ ∑ n ∈ Finset.range 5, (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-66:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_4 : mainRemConst 5 (1/4:ℝ) 0.752898 ≤ 34.11033592 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.752898 (by norm_num) _ 0.6687403049765 1.60943791291421 34.11033592 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_4 : ∀ y ∈ Set.Icc (((-286:ℤ):ℝ)/1000) (((-66:ℤ):ℝ)/1000), 0 < (I ^ ((-10):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-10):ℤ) = (((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-10) (-3) 2 (by norm_num), rot2])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((-286:ℤ):ℝ)/1000) (((-66:ℤ):ℝ)/1000) (I ^ ((-10):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.752898 0.066 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 34.11033592 rb_b1left_4 0.6687403049765 0.379864 1.282302 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.647606345784 0.805858837825 (by rw [hrot]; exact bv_b1left_m0p286_2_5_c0) (by rw [hrot]; exact bv_b1left_m0p066_2_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_0p17_2_5_c0 : (0.7512027265:ℝ) ≤ (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((170:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((170:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((170:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((170:ℤ):ℝ)/1000)) (-1) (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((170:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9930654858224 (-0.1175624977125) 0.00000012075 cs_b1left_v0p17_2 (-0.83506530867858) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((170:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9826102212463 (-0.1856802442432) 0.00000011099 cs_b1left_v0p17_3 (-0.74662239552312) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((170:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.9723581182632 (-0.2334945178108) 0.00000014149 cs_b1left_v0p17_4 (-0.68756111921429) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((170:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9628032311531 (-0.2702035123405) 0.00000014521 cs_b1left_v0p17_5 (-0.64386542354147) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((170:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9628032311531 (-0.2702035123405) 0.00000014521 cs_b1left_v0p17_5 0.5914 (by norm_num) (by norm_num) (-6.97478070148955) (-4.66431697345763) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-3.91311424695746):ℝ) ≤ ∑ n ∈ Finset.range 5, (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((170:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_5 : mainRemConst 5 (1/4:ℝ) 0.75 ≤ 34.31946501 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.75 (by norm_num) _ 0.6687403049765 1.60943791291421 34.31946501 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_5 : ∀ y ∈ Set.Icc (((-66:ℤ):ℝ)/1000) (((170:ℤ):ℝ)/1000), 0 < (I ^ ((-10):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-10):ℤ) = (((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-10) (-3) 2 (by norm_num), rot2])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((-66:ℤ):ℝ)/1000) (((170:ℤ):ℝ)/1000) (I ^ ((-10):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.75 0 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 34.31946501 rb_b1left_5 0.6687403049765 0.302325 1.261508 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.805858837825 0.7512027265 (by rw [hrot]; exact bv_b1left_m0p066_2_5_c0) (by rw [hrot]; exact bv_b1left_0p17_2_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_0p406_2_5_c0 : (0.515444083656:ℝ) ≤ (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((406:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((406:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((406:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((406:ℤ):ℝ)/1000)) (-1) (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((406:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9606626554676 (-0.277717954749) 0.00000014481 cs_b1left_v0p406_2 (-0.80781790502112) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((406:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9021639678919 (-0.4313932950771) 0.00000011092 cs_b1left_v0p406_3 (-0.68549646139429) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((406:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.8457455285787 (-0.5335864511858) 0.00000011082 cs_b1left_v0p406_4 (-0.59803247677782) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((406:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.7940022360837 (-0.6079148370407) 0.00000010778 cs_b1left_v0p406_5 (-0.53098136958747) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((406:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.7940022360837 (-0.6079148370407) 0.00000010778 cs_b1left_v0p406_5 0.727336 (by norm_num) (by norm_num) (-6.18741276044915) (-4.13777229643763) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-3.6223282127807):ℝ) ≤ ∑ n ∈ Finset.range 5, (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((406:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_6 : mainRemConst 5 (1/4:ℝ) 0.769025 ≤ 32.99246537 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.769025 (by norm_num) _ 0.6687403049765 1.60943791291421 32.99246537 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_6 : ∀ y ∈ Set.Icc (((170:ℤ):ℝ)/1000) (((406:ℤ):ℝ)/1000), 0 < (I ^ ((-10):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-10):ℤ) = (((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-10) (-3) 2 (by norm_num), rot2])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((170:ℤ):ℝ)/1000) (((406:ℤ):ℝ)/1000) (I ^ ((-10):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.769025 0.17 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 32.99246537 rb_b1left_6 0.6687403049765 0.476798 1.314282 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.7512027265 0.515444083656 (by rw [hrot]; exact bv_b1left_0p17_2_5_c0) (by rw [hrot]; exact bv_b1left_0p406_2_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_0p406_1_5_c0 : (0.527838033556:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((406:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((406:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((406:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((406:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((406:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9606626554676 (-0.277717954749) 0.00000014481 cs_b1left_v0p406_2 0.23353191082981 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((406:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9021639678919 (-0.4313932950771) 0.00000011092 cs_b1left_v0p406_3 0.32778793586939 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((406:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.8457455285787 (-0.5335864511858) 0.00000011082 cs_b1left_v0p406_4 0.37730251962114 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((406:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.7940022360837 (-0.6079148370407) 0.00000010778 cs_b1left_v0p406_5 0.40653708144544 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((406:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.7940022360837 (-0.6079148370407) 0.00000010778 cs_b1left_v0p406_5 0.727336 (by norm_num) (by norm_num) 1.22218058060397 0.81732141420946 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.34515944776578:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((406:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b1left_0p642_1_5_c0 : (0.608837373907:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((642:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((642:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((642:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((642:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((642:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9026104501671 (-0.4304583316062) 0.00000011026 cs_b1left_v0p642_2 0.3619707752465 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((642:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.7614112081253 (-0.648269212705) 0.00000011086 cs_b1left_v0p642_3 0.49257799748707 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((642:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.6294112495016 (-0.7770723769385) 0.00000012051 cs_b1left_v0p642_4 0.54947306199248 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((642:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.5120220926488 (-0.8589722793196) 0.00000014011 cs_b1left_v0p642_5 0.57442929034125 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((642:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.5120220926488 (-0.8589722793196) 0.00000014011 cs_b1left_v0p642_5 0.974664 (by norm_num) (by norm_num) 2.04805025354063 1.36961375115996 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.9784511250673:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((642:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_7 : mainRemConst 5 (1/4:ℝ) 0.852839 ≤ 28.22341988 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.852839 (by norm_num) _ 0.6687403049765 1.60943791291421 28.22341988 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_7 : ∀ y ∈ Set.Icc (((406:ℤ):ℝ)/1000) (((642:ℤ):ℝ)/1000), 0 < (I ^ ((-11):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-11):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (-11) (-3) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((406:ℤ):ℝ)/1000) (((642:ℤ):ℝ)/1000) (I ^ ((-11):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.852839 0.406 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 28.22341988 rb_b1left_7 0.6687403049765 0.688959 1.405228 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.527838033556 0.608837373907 (by rw [hrot]; exact bv_b1left_0p406_1_5_c0) (by rw [hrot]; exact bv_b1left_0p642_1_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_0p878_1_5_c0 : (0.587137541685:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((878:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((878:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((878:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((878:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((878:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.8204588335427 (-0.5717056082126) 0.00000012476 cs_b1left_v0p878_2 0.48074509161617 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((878:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.5697607717285 (-0.8218106004423) 0.00000011079 cs_b1left_v0p878_3 0.62444093688055 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((878:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.3463053950765 (-0.9381218328879) 0.0000001495 cs_b1left_v0p878_4 0.66335220390167 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((878:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.1570568693156 (-0.9875895603948) 0.00000011335 cs_b1left_v0p878_5 0.66044086800821 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((878:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.1570568693156 (-0.9875895603948) 0.00000011335 cs_b1left_v0p878_5 1.333384 (by norm_num) (by norm_num) 2.75419553003658 1.84184155872158 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.4289791004066:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((878:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_8 : mainRemConst 5 (1/4:ℝ) 0.98725 ≤ 23.04768939 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.98725 (by norm_num) _ 0.6687403049765 1.60943791291421 23.04768939 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_8 : ∀ y ∈ Set.Icc (((642:ℤ):ℝ)/1000) (((878:ℤ):ℝ)/1000), 0 < (I ^ ((-11):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-11):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (-11) (-3) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((642:ℤ):ℝ)/1000) (((878:ℤ):ℝ)/1000) (I ^ ((-11):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.98725 0.642 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 23.04768939 rb_b1left_8 0.6687403049765 0.912899 1.527542 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.608837373907 0.587137541685 (by rw [hrot]; exact bv_b1left_0p642_1_5_c0) (by rw [hrot]; exact bv_b1left_0p878_1_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_1p193_1_5_c0 : (0.497821329257:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((1193:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1193:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((1193:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((1193:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((1193:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.6771419991189 (-0.735852371763) 0.00000011392 cs_b1left_v1p193_2 0.61877552577652 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((1193:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.2572272728216 (-0.9663509352801) 0.00000013994 cs_b1left_v1p193_3 0.73426781915711 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((1193:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.0829574260587) (-0.9965530921438) 0.00000012782 cs_b1left_v1p193_4 0.70466935888486 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((1193:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.3422054654885) (-0.9396251483371) 0.00000013012 cs_b1left_v1p193_5 0.62836512124595 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((1193:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.3422054654885) (-0.9396251483371) 0.00000013012 cs_b1left_v1p193_5 1.985749 (by norm_num) (by norm_num) 3.27220668400402 2.188256495807 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.68607782506444:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1193:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_9 : mainRemConst 5 (1/4:ℝ) 1.154722 ≤ 18.98664796 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 1.154722 (by norm_num) _ 0.6687403049765 1.60943791291421 18.98664796 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_9 : ∀ y ∈ Set.Icc (((878:ℤ):ℝ)/1000) (((1193:ℤ):ℝ)/1000), 0 < (I ^ ((-11):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-11):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (-11) (-3) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((878:ℤ):ℝ)/1000) (((1193:ℤ):ℝ)/1000) (I ^ ((-11):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.154722 0.878 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 18.98664796 rb_b1left_9 0.6687403049765 1.218914 1.727933 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.587137541685 0.497821329257 (by rw [hrot]; exact bv_b1left_0p878_1_5_c0) (by rw [hrot]; exact bv_b1left_1p193_1_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_1p429_1_5_c0 : (0.420655377907:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((1429:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1429:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((1429:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((1429:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((1429:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.5482656740173 (-0.8363042213778) 0.00000012138 cs_b1left_v1p429_2 0.70324511975012 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((1429:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.0008793266815 (-0.9999996133921) 0.00000013988 cs_b1left_v1p429_3 0.7598352856072 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((1429:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.3988095013889) (-0.9170337952326) 0.00000014274 cs_b1left_v1p429_4 0.64844071425374 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((1429:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.6661916031789) (-0.7457806298337) 0.00000012389 cs_b1left_v1p429_5 0.49873348299024 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((1429:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.6661916031789) (-0.7457806298337) 0.00000012389 cs_b1left_v1p429_5 2.604541 (by norm_num) (by norm_num) 3.27421453200903 2.18959922469421 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.6102546026013:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1429:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_10 : mainRemConst 5 (1/4:ℝ) 1.409166 ≤ 15.3296453 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 1.409166 (by norm_num) _ 0.6687403049765 1.60943791291421 15.3296453 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_10 : ∀ y ∈ Set.Icc (((1193:ℤ):ℝ)/1000) (((1429:ℤ):ℝ)/1000), 0 < (I ^ ((-11):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-11):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (-11) (-3) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((1193:ℤ):ℝ)/1000) (((1429:ℤ):ℝ)/1000) (I ^ ((-11):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.409166 1.193 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 15.3296453 rb_b1left_10 0.6687403049765 1.450704 1.898563 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.497821329257 0.420655377907 (by rw [hrot]; exact bv_b1left_1p193_1_5_c0) (by rw [hrot]; exact bv_b1left_1p429_1_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_1p665_1_5_c0 : (0.346304426057:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((1665:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1665:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((1665:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((1665:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((1665:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.4047507387294 (-0.9144270553182) 0.00000014482 cs_b1left_v1p665_2 0.76893831104945 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((1665:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.2555273993722) (-0.9668018143181) 0.00000013982 cs_b1left_v1p665_3 0.73461041323128 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((1665:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.6723536049707) (-0.7402301195326) 0.00000011208 cs_b1left_v1p665_4 0.52342165790746 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((1665:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.8952169366061) (-0.4456306052131) 0.00000012502 cs_b1left_v1p665_5 0.29801106323111 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((1665:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.8952169366061) (-0.4456306052131) 0.00000012502 cs_b1left_v1p665_5 3.334725 (by norm_num) (by norm_num) 2.95881226933247 1.97867701936161 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.3249814454193:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1665:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_11 : mainRemConst 5 (1/4:ℝ) 1.613859 ≤ 13.50677966 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 1.613859 (by norm_num) _ 0.6687403049765 1.60943791291421 13.50677966 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_11 : ∀ y ∈ Set.Icc (((1429:ℤ):ℝ)/1000) (((1665:ℤ):ℝ)/1000), 0 < (I ^ ((-11):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-11):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (-11) (-3) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((1429:ℤ):ℝ)/1000) (((1665:ℤ):ℝ)/1000) (I ^ ((-11):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.613859 1.429 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 13.50677966 rb_b1left_11 0.6687403049765 1.683665 2.082001 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.420655377907 0.346304426057 (by rw [hrot]; exact bv_b1left_1p429_1_5_c0) (by rw [hrot]; exact bv_b1left_1p665_1_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_1p665_0_5_c0 : (0.300682059038:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((1665:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1665:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((1665:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((1665:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((1665:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.4047507387294 (-0.9144270553182) 0.00000014482 cs_b1left_v1p665_2 0.34035332349022 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((1665:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.2555273993722) (-0.9668018143181) 0.00000013982 cs_b1left_v1p665_3 (-0.19415894294498) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((1665:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.6723536049707) (-0.7402301195326) 0.00000011208 cs_b1left_v1p665_4 (-0.47542587268257) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((1665:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.8952169366061) (-0.4456306052131) 0.00000012502 cs_b1left_v1p665_5 (-0.59866773081201) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((1665:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.8952169366061) (-0.4456306052131) 0.00000012502 cs_b1left_v1p665_5 3.334725 (by norm_num) (by norm_num) (-0.34180874143011) (-0.22858128198757) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.07210077705066:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1665:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b1left_1p901_0_5_c0 : (0.356632338581:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((1901:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1901:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((1901:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((1901:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((1901:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.250429171357 (-0.9681349235171) 0.00000011026 cs_b1left_v1p901_2 0.21058489975181 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((1901:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.4948530123495) (-0.8689766948328) 0.00000013975 cs_b1left_v1p901_3 (-0.37600708412238) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((1901:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.8745704602423) (-0.4848984532663) 0.00000012051 cs_b1left_v1p901_4 (-0.61841478827626) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((1901:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.9966356919835) (-0.0819591175869) 0.00000012947 cs_b1left_v1p901_5 (-0.66649054318932) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((1901:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.9966356919835) (-0.0819591175869) 0.00000012947 cs_b1left_v1p901_5 4.176301 (by norm_num) (by norm_num) (-1.20668643479723) (-0.80695985441718) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-0.45032751583615):ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1901:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_12 : mainRemConst 5 (1/4:ℝ) 1.826122 ≤ 12.18414698 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 1.826122 (by norm_num) _ 0.6687403049765 1.60943791291421 12.18414698 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_12 : ∀ y ∈ Set.Icc (((1665:ℤ):ℝ)/1000) (((1901:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((1665:ℤ):ℝ)/1000) (((1901:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.826122 1.665 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 12.18414698 rb_b1left_12 0.6687403049765 1.917369 2.275149 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.300682059038 0.356632338581 (by rw [hrot]; exact bv_b1left_1p665_0_5_c0) (by rw [hrot]; exact bv_b1left_1p901_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_2p216_0_5_c0 : (0.417088410157:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((2216:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((2216:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((2216:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((2216:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((2216:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.0347751140041 (-0.9993951628089) 0.00000014847 cs_b1left_v2p216_2 0.02924214385819 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((2216:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.760269885298) (-0.6496073440722) 0.00000013224 cs_b1left_v2p216_3 (-0.57768029005635) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((2216:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.9975813756912) (-0.0695082609553) 0.00000010532 cs_b1left_v2p216_4 (-0.7053966300092) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((2216:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.9110709927463) 0.4122494949011 0.00000010785 cs_b1left_v2p216_5 (-0.60926996566805) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((2216:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.9110709927463) 0.4122494949011 0.00000010785 cs_b1left_v2p216_5 5.473156 (by norm_num) (by norm_num) (-1.9143352696205) (-1.28019315203309) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-0.86310474187541):ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((2216:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_13 : mainRemConst 5 (1/4:ℝ) 2.0436 ≤ 11.19690786 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 2.0436 (by norm_num) _ 0.6687403049765 1.60943791291421 11.19690786 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_13 : ∀ y ∈ Set.Icc (((1901:ℤ):ℝ)/1000) (((2216:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((1901:ℤ):ℝ)/1000) (((2216:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 2.0436 1.901 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 11.19690786 rb_b1left_13 0.6687403049765 2.230058 2.54424 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.356632338581 0.417088410157 (by rw [hrot]; exact bv_b1left_1p901_0_5_c0) (by rw [hrot]; exact bv_b1left_2p216_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_2p531_0_5_c0 : (0.465780131773:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((2531:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((2531:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((2531:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((2531:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((2531:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.1825301021958) (-0.9832002653537) 0.00000011462 cs_b1left_v2p531_2 (-0.15348900499591) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((2531:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.9355423318292) (-0.3532145880134) 0.00000010324 cs_b1left_v2p531_3 (-0.71085852760698) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((2531:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.9333655209527) 0.3589272964415 0.00000012205 cs_b1left_v2p531_4 (-0.65998917549381) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((2531:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.5963141180708) 0.802751189708 0.00000015042 cs_b1left_v2p531_5 (-0.39877938577238) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((2531:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.5963141180708) 0.802751189708 0.00000015042 cs_b1left_v2p531_5 6.968461 (by norm_num) (by norm_num) (-2.07688427825671) (-1.38889622564208) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-0.92311609386908):ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((2531:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_14 : mainRemConst 5 (1/4:ℝ) 2.339477 ≤ 10.22493398 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 2.339477 (by norm_num) _ 0.6687403049765 1.60943791291421 10.22493398 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_14 : ∀ y ∈ Set.Icc (((2216:ℤ):ℝ)/1000) (((2531:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((2216:ℤ):ℝ)/1000) (((2531:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 2.339477 2.216 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 10.22493398 rb_b1left_14 0.6687403049765 2.543317 2.822847 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.417088410157 0.465780131773 (by rw [hrot]; exact bv_b1left_2p216_0_5_c0) (by rw [hrot]; exact bv_b1left_2p531_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_2p846_0_5_c0 : (0.503738351954:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((2846:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((2846:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((2846:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((2846:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((2846:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.3911681817763) (-0.9203192128619) 0.00000012488 cs_b1left_v2p846_2 (-0.32893202682819) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((2846:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.9998883692729) (-0.0149414972984) 0.00000012721 cs_b1left_v2p846_3 (-0.75975096130024) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((2846:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.6939749739595) 0.7199991218711 0.00000014595 cs_b1left_v2p846_4 (-0.4907145132628) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((2846:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.1315462991846) 0.9913100277765 0.00000010989 cs_b1left_v2p846_5 (-0.08797038572312) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((2846:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.1315462991846) 0.9913100277765 0.00000010989 cs_b1left_v2p846_5 8.662216 (by norm_num) (by norm_num) (-1.75121228727187) (-1.1711062390686) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-0.66736788711435):ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((2846:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_15 : mainRemConst 5 (1/4:ℝ) 2.639784 ≤ 9.51341048 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 2.639784 (by norm_num) _ 0.6687403049765 1.60943791291421 9.51341048 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_15 : ∀ y ∈ Set.Icc (((2531:ℤ):ℝ)/1000) (((2846:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((2531:ℤ):ℝ)/1000) (((2846:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 2.639784 2.531 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 9.51341048 rb_b1left_15 0.6687403049765 2.85696 3.108411 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.465780131773 0.503738351954 (by rw [hrot]; exact bv_b1left_2p531_0_5_c0) (by rw [hrot]; exact bv_b1left_2p846_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_3p161_0_5_c0 : (0.530603311191:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((3161:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((3161:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((3161:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((3161:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((3161:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.5812319989295) (-0.8137378960143) 0.00000013852 cs_b1left_v3p161_2 (-0.48875602081159) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((3161:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.9456785769934) 0.3251031049119 0.00000013807 cs_b1left_v3p161_3 (-0.71856043486633) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((3161:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.3243386254537) 0.9459410425797 0.00000013334 cs_b1left_v3p161_4 (-0.22934213574468) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((3161:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.3663136820976 0.9304914219423 0.00000013556 cs_b1left_v3p161_5 0.24496863282854 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((3161:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.3663136820976 0.9304914219423 0.00000013556 cs_b1left_v3p161_5 10.554421 (by norm_num) (by norm_num) (-1.08008036065819) (-0.72229326978557) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-0.19168995859406):ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((3161:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_16 : mainRemConst 5 (1/4:ℝ) 2.943164 ≤ 8.97358684 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 2.943164 (by norm_num) _ 0.6687403049765 1.60943791291421 8.97358684 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_16 : ∀ y ∈ Set.Icc (((2846:ℤ):ℝ)/1000) (((3161:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((2846:ℤ):ℝ)/1000) (((3161:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 2.943164 2.846 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 8.97358684 rb_b1left_16 0.6687403049765 3.170871 3.39918 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.503738351954 0.530603311191 (by rw [hrot]; exact bv_b1left_2p846_0_5_c0) (by rw [hrot]; exact bv_b1left_3p161_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_3p476_0_5_c0 : (0.546770128631:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((3476:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((3476:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((3476:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((3476:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((3476:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.7436967605199) (-0.6685171114937) 0.00000010129 cs_b1left_v3p476_2 (-0.62537202513145) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((3476:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.7793405316015) 0.6266006190238 0.00000010908 cs_b1left_v3p476_3 (-0.59217083006839) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((3476:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.1061697503704 0.9943480196119 0.00000010975 cs_b1left_v3p476_4 0.07507327283881 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((3476:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.7720225882415 0.6355950937861 0.00000012538 cs_b1left_v3p476_5 0.51628253726263 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((3476:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.7720225882415 0.6355950937861 0.00000012538 cs_b1left_v3p476_5 12.645076 (by norm_num) (by norm_num) (-0.25863129894057) (-0.17295717372995) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.3738129549016:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((3476:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_17 : mainRemConst 5 (1/4:ℝ) 3.248756 ≤ 8.55175554 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 3.248756 (by norm_num) _ 0.6687403049765 1.60943791291421 8.55175554 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_17 : ∀ y ∈ Set.Icc (((3161:ℤ):ℝ)/1000) (((3476:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((3161:ℤ):ℝ)/1000) (((3476:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 3.248756 3.161 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 8.55175554 rb_b1left_17 0.6687403049765 3.484979 3.693925 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.530603311191 0.546770128631 (by rw [hrot]; exact bv_b1left_3p161_0_5_c0) (by rw [hrot]; exact bv_b1left_3p476_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_3p897_0_5_c0 : (0.556326227359:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((3897:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((3897:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((3897:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((3897:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((3897:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.9045820447775) (-0.426299570894) 0.00000013839 cs_b1left_v3p897_2 (-0.76065991512801) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((3897:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.4178675716295) 0.908507948549 0.00000011927 cs_b1left_v3p897_3 (-0.31751078342628) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((3897:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.636537280012 0.7712459342874 0.00000011999 cs_b1left_v3p897_4 0.45009974232875 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((3897:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9999372156802 0.0112055654828 0.00000013946 cs_b1left_v3p897_5 0.6686982253087 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((3897:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9999372156802 0.0112055654828 0.00000013946 cs_b1left_v3p897_5 15.749109 (by norm_num) (by norm_num) 0.7241989724853 0.48430104172349 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.04062726908316:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((3897:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_18 : mainRemConst 5 (1/4:ℝ) 3.555991 ≤ 8.2139605 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 3.555991 (by norm_num) _ 0.6687403049765 1.60943791291421 8.2139605 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_18 : ∀ y ∈ Set.Icc (((3476:ℤ):ℝ)/1000) (((3897:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((3476:ℤ):ℝ)/1000) (((3897:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 3.555991 3.476 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 8.2139605 rb_b1left_18 0.6687403049765 3.905011 4.092568 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.546770128631 0.556326227359 (by rw [hrot]; exact bv_b1left_3p476_0_5_c0) (by rw [hrot]; exact bv_b1left_3p897_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_4p212_0_5_c0 : (0.561290707175:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((4212:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
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
lemma rb_b1left_19 : mainRemConst 5 (1/4:ℝ) 3.968514 ≤ 7.85603611 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 3.968514 (by norm_num) _ 0.6687403049765 1.60943791291421 7.85603611 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_19 : ∀ y ∈ Set.Icc (((3897:ℤ):ℝ)/1000) (((4212:ℤ):ℝ)/1000), 0 < (I ^ ((-12):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-12):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-12) (-3) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((3897:ℤ):ℝ)/1000) (((4212:ℤ):ℝ)/1000) (I ^ ((-12):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 3.968514 3.897 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 7.85603611 rb_b1left_19 0.6687403049765 4.219413 4.393569 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.556326227359 0.561290707175 (by rw [hrot]; exact bv_b1left_3p897_0_5_c0) (by rw [hrot]; exact bv_b1left_4p212_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)

end H28
end Cert
end ZB
end RHV6Fresh
