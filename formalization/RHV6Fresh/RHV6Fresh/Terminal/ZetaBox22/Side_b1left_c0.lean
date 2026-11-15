/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_trig0
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_trig1
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_trig2
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_trig3
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_trig4
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_trig5
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_trig6
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_trig7
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_trig8
import RHV6Fresh.Terminal.ZetaBox22.Side_b1left_trig9
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
namespace H22

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
lemma bv_b1left_m0p806_3_5_c0 : (0.600378549373:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((-806:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-806:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((-806:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((-806:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((-806:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.8479573406866 0.5300644756779 0.00000012774 cs_b1left_vm0p806_2 0.44572921003477 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((-806:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.6329167880249 0.7742198263002 0.00000010487 cs_b1left_vm0p806_3 0.58827977287782 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((-806:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.4380632133543 0.8989441701829 0.00000014537 cs_b1left_vm0p806_4 0.63564941585228 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((-806:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.2701889997792 0.9628073038767 0.00000014301 cs_b1left_vm0p806_5 0.64386795439145 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((-806:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.2701889997792 0.9628073038767 0.00000014301 cs_b1left_vm0p806_5 1.212136 (by norm_num) (by norm_num) 2.56175348043865 1.71314780378316 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.31352635315632:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-806:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_0 : mainRemConst 5 (1/4:ℝ) 1.10097 ≤ 20.09041969 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 1.10097 (by norm_num) _ 0.6687403049765 1.60943791291421 20.09041969 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_0 : ∀ y ∈ Set.Icc (((-1000:ℤ):ℝ)/1000) (((-806:ℤ):ℝ)/1000), 0 < (I ^ ((-5):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-5):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-5) (-2) 3 (by norm_num), rot3])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (((-806:ℤ):ℝ)/1000) (I ^ ((-5):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.10097 0.806 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 20.09041969 rb_b1left_0 0.6687403049765 1.030777 1.600782 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.556767974975 0.600378549373 (by rw [hrot]; exact bv_b1left_m1_3_5_c0) (by rw [hrot]; exact bv_b1left_m0p806_3_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_m0p558_3_5_c0 : (0.595843671123:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((-558:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-558:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((-558:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((-558:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((-558:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9261299406342 0.377204630222 0.0000001269 cs_b1left_vm0p558_2 0.31718991466102 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((-558:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.8179109435374 0.5753448430652 0.00000014308 cs_b1left_vm0p558_3 0.43716743459921 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((-558:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.7154332640101 0.6986810751322 0.0000001468 cs_b1left_vm0p558_4 0.49404202230937 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((-558:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.6231234461992 0.7821235009874 0.00000014517 cs_b1left_vm0p558_5 0.52303741149849 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((-558:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.6231234461992 0.7821235009874 0.00000014517 cs_b1left_vm0p558_5 0.873864 (by norm_num) (by norm_num) 1.7579217271585 1.1755931119448 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.77143678306809:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-558:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_1 : mainRemConst 5 (1/4:ℝ) 0.934806 ≤ 24.79503169 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.934806 (by norm_num) _ 0.6687403049765 1.60943791291421 24.79503169 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_1 : ∀ y ∈ Set.Icc (((-806:ℤ):ℝ)/1000) (((-558:ℤ):ℝ)/1000), 0 < (I ^ ((-5):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-5):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-5) (-2) 3 (by norm_num), rot3])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((-806:ℤ):ℝ)/1000) (((-558:ℤ):ℝ)/1000) (I ^ ((-5):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.934806 0.558 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 24.79503169 rb_b1left_1 0.6687403049765 0.843882 1.487326 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.600378549373 0.595843671123 (by rw [hrot]; exact bv_b1left_m0p806_3_5_c0) (by rw [hrot]; exact bv_b1left_m0p558_3_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_m0p354_3_5_c0 : (0.48837075823:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((-354:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-354:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((-354:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((-354:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((-354:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9700465167679 0.2429192361804 0.00000010202 cs_b1left_vm0p354_2 0.20426982911201 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((-354:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9253233707209 0.3791789282089 0.00000014992 cs_b1left_vm0p354_3 0.28811356698564 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((-354:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.8819804893871 0.4712859178254 0.00000010402 cs_b1left_vm0p354_4 0.33324939481879 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((-354:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8420407116235 0.5394139782843 0.00000012119 cs_b1left_vm0p354_5 0.36072778730173 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((-354:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8420407116235 0.5394139782843 0.00000012119 cs_b1left_vm0p354_5 0.687816 (by norm_num) (by norm_num) 1.0437382266236 0.6979898199879 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.18636057821817:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-354:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_2 : mainRemConst 5 (1/4:ℝ) 0.829346 ≤ 29.40740644 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.829346 (by norm_num) _ 0.6687403049765 1.60943791291421 29.40740644 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_2 : ∀ y ∈ Set.Icc (((-558:ℤ):ℝ)/1000) (((-354:ℤ):ℝ)/1000), 0 < (I ^ ((-5):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-5):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-5) (-2) 3 (by norm_num), rot3])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((-558:ℤ):ℝ)/1000) (((-354:ℤ):ℝ)/1000) (I ^ ((-5):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.829346 0.354 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 29.40740644 rb_b1left_2 0.6687403049765 0.611445 1.368892 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.595843671123 0.48837075823 (by rw [hrot]; exact bv_b1left_m0p558_3_5_c0) (by rw [hrot]; exact bv_b1left_m0p354_3_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_m0p354_2_5_c0 : (0.574351772879:ℝ) ≤ (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((-354:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-354:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((-354:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((-354:ℤ):ℝ)/1000)) (-1) (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((-354:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9700465167679 0.2429192361804 0.00000010202 cs_b1left_vm0p354_2 (-0.81570872436782) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((-354:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9253233707209 0.3791789282089 0.00000014992 cs_b1left_vm0p354_3 (-0.70309383175574) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((-354:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.8819804893871 0.4712859178254 0.00000010402 cs_b1left_vm0p354_4 (-0.62365445847315) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((-354:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8420407116235 0.5394139782843 0.00000012119 cs_b1left_vm0p354_5 (-0.56310664333837) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((-354:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8420407116235 0.5394139782843 0.00000012119 cs_b1left_vm0p354_5 0.687816 (by norm_num) (by norm_num) (-6.39996632319884) (-4.27991543081468) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-3.70556365793508):ℝ) ≤ ∑ n ∈ Finset.range 5, (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-354:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b1left_m0p155_2_5_c0 : (0.761693701549:ℝ) ≤ (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((-155:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-155:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((-155:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((-155:ℤ):ℝ)/1000)) (-1) (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((-155:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9942341090174 0.1072312289696 0.00000011304 cs_b1left_vm0p155_2 (-0.83604799325072) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((-155:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.98553652686 0.1694631352972 0.0000001048 cs_b1left_vm0p155_3 (-0.74884590225215) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((-155:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.9770029270673 0.2132258907868 0.00000012606 cs_b1left_vm0p155_4 (-0.69084548410633) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((-155:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9690451626166 0.2468835207327 0.00000012367 cs_b1left_vm0p155_5 (-0.64803964028735) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((-155:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9690451626166 0.2468835207327 0.00000012367 cs_b1left_vm0p155_5 0.586525 (by norm_num) (by norm_num) (-7.00641592346007) (-4.68547272144619) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-3.92377901989655):ℝ) ≤ ∑ n ∈ Finset.range 5, (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((-155:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_3 : mainRemConst 5 (1/4:ℝ) 0.765849 ≤ 33.20664719 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.765849 (by norm_num) _ 0.6687403049765 1.60943791291421 33.20664719 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_3 : ∀ y ∈ Set.Icc (((-354:ℤ):ℝ)/1000) (((-155:ℤ):ℝ)/1000), 0 < (I ^ ((-6):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-6):ℤ) = (((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-6) (-2) 2 (by norm_num), rot2])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((-354:ℤ):ℝ)/1000) (((-155:ℤ):ℝ)/1000) (I ^ ((-6):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.765849 0.155 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 33.20664719 rb_b1left_3 0.6687403049765 0.433378 1.29916 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.574351772879 0.761693701549 (by rw [hrot]; exact bv_b1left_m0p354_2_5_c0) (by rw [hrot]; exact bv_b1left_m0p155_2_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_0p081_2_5_c0 : (0.800755150069:ℝ) ≤ (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((81:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((81:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((81:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((81:ℤ):ℝ)/1000)) (-1) (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((81:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9984242890868 (-0.0561154075238) 0.00000012166 cs_b1left_v0p081_2 (-0.83957150789888) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((81:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.996043215637 (-0.0888702007627) 0.00000010465 cs_b1left_v0p081_3 (-0.75682925920897) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((81:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.9937021220769 (-0.1120539717276) 0.0000001433 cs_b1left_v0p081_4 (-0.7026536103285) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((81:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9915145762013 (-0.1299955583103) 0.00000012915 cs_b1left_v0p081_5 (-0.66306584644532) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((81:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9915145762013 (-0.1299955583103) 0.00000012915 cs_b1left_v0p081_5 0.569061 (by norm_num) (by norm_num) (-7.12215988554658) (-4.7628753739511) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-3.96212022388167):ℝ) ≤ ∑ n ∈ Finset.range 5, (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((81:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_4 : mainRemConst 5 (1/4:ℝ) 0.75 ≤ 34.31946501 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.75 (by norm_num) _ 0.6687403049765 1.60943791291421 34.31946501 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_4 : ∀ y ∈ Set.Icc (((-155:ℤ):ℝ)/1000) (((81:ℤ):ℝ)/1000), 0 < (I ^ ((-6):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-6):ℤ) = (((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-6) (-2) 2 (by norm_num), rot2])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((-155:ℤ):ℝ)/1000) (((81:ℤ):ℝ)/1000) (I ^ ((-6):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.75 0 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 34.31946501 rb_b1left_4 0.6687403049765 0.294152 1.259574 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.761693701549 0.800755150069 (by rw [hrot]; exact bv_b1left_m0p155_2_5_c0) (by rw [hrot]; exact bv_b1left_0p081_2_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_0p317_2_5_c0 : (0.614960109319:ℝ) ≤ (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((317:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((317:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((317:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((317:ℤ):ℝ)/1000)) (-1) (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((317:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9759568370762 (-0.2179638781181) 0.00000014386 cs_b1left_v0p317_2 (-0.82067872671118) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((317:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9399678985829 (-0.3412628746781) 0.00000010459 cs_b1left_v0p317_3 (-0.71422123218145) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((317:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.9049835382161 (-0.4254465836717) 0.00000011264 cs_b1left_v0p317_4 (-0.63992007638336) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((317:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8726508591974 (-0.4883446302991) 0.00000011841 cs_b1left_v0p317_5 (-0.58357688090322) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((317:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8726508591974 (-0.4883446302991) 0.00000011841 cs_b1left_v0p317_5 0.662989 (by norm_num) (by norm_num) (-6.53969409792458) (-4.37335702549844) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-3.75839691617921):ℝ) ≤ ∑ n ∈ Finset.range 5, (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((317:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_5 : mainRemConst 5 (1/4:ℝ) 0.754361 ≤ 34.00574298 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.754361 (by norm_num) _ 0.6687403049765 1.60943791291421 34.00574298 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_5 : ∀ y ∈ Set.Icc (((81:ℤ):ℝ)/1000) (((317:ℤ):ℝ)/1000), 0 < (I ^ ((-6):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-6):ℤ) = (((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-6) (-2) 2 (by norm_num), rot2])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((81:ℤ):ℝ)/1000) (((317:ℤ):ℝ)/1000) (I ^ ((-6):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.754361 0.081 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 34.00574298 rb_b1left_5 0.6687403049765 0.403719 1.28957 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.800755150069 0.614960109319 (by rw [hrot]; exact bv_b1left_0p081_2_5_c0) (by rw [hrot]; exact bv_b1left_0p317_2_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_0p317_1_5_c0 : (0.454683462318:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((317:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((317:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((317:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((317:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((317:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9759568370762 (-0.2179638781181) 0.00000014386 cs_b1left_v0p317_2 0.18328492279294 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((317:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.9399678985829 (-0.3412628746781) 0.00000010459 cs_b1left_v0p317_3 0.25930363089722 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((317:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.9049835382161 (-0.4254465836717) 0.00000011264 cs_b1left_v0p317_4 0.30083608469838 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((317:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8726508591974 (-0.4883446302991) 0.00000011841 cs_b1left_v0p317_5 0.32657565781426 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((317:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8726508591974 (-0.4883446302991) 0.00000011841 cs_b1left_v0p317_5 0.662989 (by norm_num) (by norm_num) 0.92011327761403 0.61531683388454 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.0700002962028:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((317:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b1left_0p494_1_5_c0 : (0.575080867468:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((494:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((494:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((494:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((494:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((494:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9419466465352 (-0.3357625873756) 0.00000010733 cs_b1left_v0p494_2 0.28234146584703 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((494:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.8563099009128 (-0.5164623448024) 0.00000012954 cs_b1left_v0p494_3 0.39242642144699 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((494:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.7745269698377 (-0.6325408864208) 0.00000011465 cs_b1left_v0p494_4 0.44727386909607 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((494:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.7002402909795 (-0.7139072312906) 0.00000012899 cs_b1left_v0p494_5 0.47741845331732 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((494:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.7002402909795 (-0.7139072312906) 0.00000012899 cs_b1left_v0p494_5 0.806536 (by norm_num) (by norm_num) 1.53180440092423 1.02437934223842 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.59946020970741:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((494:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_6 : mainRemConst 5 (1/4:ℝ) 0.814241 ≤ 30.22642933 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.814241 (by norm_num) _ 0.6687403049765 1.60943791291421 30.22642933 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_6 : ∀ y ∈ Set.Icc (((317:ℤ):ℝ)/1000) (((494:ℤ):ℝ)/1000), 0 < (I ^ ((-7):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-7):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (-7) (-2) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((317:ℤ):ℝ)/1000) (((494:ℤ):ℝ)/1000) (I ^ ((-7):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.814241 0.317 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 30.22642933 rb_b1left_6 0.6687403049765 0.553657 1.344075 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.454683462318 0.575080867468 (by rw [hrot]; exact bv_b1left_0p317_1_5_c0) (by rw [hrot]; exact bv_b1left_0p494_1_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_0p73_1_5_c0 : (0.608802630522:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((730:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((730:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((730:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((730:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((730:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.8746914896505 (-0.4846800985526) 0.000000142 cs_b1left_v0p73_2 0.4075656380104 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((730:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.695279948375 (-0.718739030099) 0.00000012948 cs_b1left_v0p73_3 0.54612346535624 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((730:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.530170319345 (-0.8478911678309) 0.00000011678 cs_b1left_v0p73_4 0.59954951190544 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((730:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.3856448439597 (-0.9226473076573) 0.00000012432 cs_b1left_v0p73_5 0.6170113587706 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((730:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.3856448439597 (-0.9226473076573) 0.00000012432 cs_b1left_v0p73_5 1.0954 (by norm_num) (by norm_num) 2.33490838207408 1.56144734352041 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.17024997404268:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((730:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_7 : mainRemConst 5 (1/4:ℝ) 0.898073 ≤ 26.21115491 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 0.898073 (by norm_num) _ 0.6687403049765 1.60943791291421 26.21115491 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_7 : ∀ y ∈ Set.Icc (((494:ℤ):ℝ)/1000) (((730:ℤ):ℝ)/1000), 0 < (I ^ ((-7):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-7):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (-7) (-2) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((494:ℤ):ℝ)/1000) (((730:ℤ):ℝ)/1000) (I ^ ((-7):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.898073 0.494 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 26.21115491 rb_b1left_7 0.6687403049765 0.771622 1.44755 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.575080867468 0.608802630522 (by rw [hrot]; exact bv_b1left_0p494_1_5_c0) (by rw [hrot]; exact bv_b1left_0p73_1_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_0p966_1_5_c0 : (0.56600342682:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((966:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((966:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((966:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((966:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((966:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.7840822867233 (-0.6206568839921) 0.00000012385 cs_b1left_v0p966_2 0.52190804470646 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((966:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.4877729626623 (-0.8729705246431) 0.00000012941 cs_b1left_v0p966_3 0.6633140588154 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((966:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.2295700647065 (-0.9732921377421) 0.00000014768 cs_b1left_v0p966_4 0.68822136624741 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((966:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.0160786339329 (-0.99987073041) 0.00000012389 cs_b1left_v0p966_5 0.66865377434112 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((966:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.0160786339329 (-0.99987073041) 0.00000012389 cs_b1left_v0p966_5 1.495656 (by norm_num) (by norm_num) 2.95494948126258 1.97609381728969 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.54209724411039:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((966:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_8 : mainRemConst 5 (1/4:ℝ) 1.046613 ≤ 21.38313631 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 1.046613 (by norm_num) _ 0.6687403049765 1.60943791291421 21.38313631 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_8 : ∀ y ∈ Set.Icc (((730:ℤ):ℝ)/1000) (((966:ℤ):ℝ)/1000), 0 < (I ^ ((-7):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-7):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (-7) (-2) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((730:ℤ):ℝ)/1000) (((966:ℤ):ℝ)/1000) (I ^ ((-7):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.046613 0.73 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 21.38313631 rb_b1left_8 0.6687403049765 0.997826 1.579765 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.608802630522 0.56600342682 (by rw [hrot]; exact bv_b1left_0p73_1_5_c0) (by rw [hrot]; exact bv_b1left_0p966_1_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_1p281_1_5_c0 : (0.469131551426:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((1281:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1281:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((1281:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((1281:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((1281:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.6310258094574 (-0.7757618370341) 0.00000013862 cs_b1left_v1p281_2 0.65233523128753 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((1281:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.1627468923569 (-0.9866678514212) 0.00000014211 cs_b1left_v1p281_3 0.74970533541467 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((1281:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.2036129535024) (-0.9790514619595) 0.00000012409 cs_b1left_v1p281_4 0.69229384013723 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((1281:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.4714142173668) (-0.8819119205789) 0.00000013485 cs_b1left_v1p281_5 0.58976995655062 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((1281:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.4714142173668) (-0.8819119205789) 0.00000013485 cs_b1left_v1p281_5 2.203461 (by norm_num) (by norm_num) 3.31215689480808 2.21497281196398 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.68410436339005:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1281:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_9 : mainRemConst 5 (1/4:ℝ) 1.22297 ≤ 17.78652754 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 1.22297 (by norm_num) _ 0.6687403049765 1.60943791291421 17.78652754 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_9 : ∀ y ∈ Set.Icc (((966:ℤ):ℝ)/1000) (((1281:ℤ):ℝ)/1000), 0 < (I ^ ((-7):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-7):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (-7) (-2) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((966:ℤ):ℝ)/1000) (((1281:ℤ):ℝ)/1000) (I ^ ((-7):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.22297 0.966 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 17.78652754 rb_b1left_9 0.6687403049765 1.305168 1.789822 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.56600342682 0.469131551426 (by rw [hrot]; exact bv_b1left_0p966_1_5_c0) (by rw [hrot]; exact bv_b1left_1p281_1_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_1p517_1_5_c0 : (0.392325095196:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((1517:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1517:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((1517:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((1517:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((1517:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.4962656206443 (-0.8681707399852) 0.0000001275 cs_b1left_v1p517_2 0.73004155586741 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((1517:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.0956520111154) (-0.9954148345133) 0.00000014229 cs_b1left_v1p517_3 0.75635160517306 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((1517:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.5074407813641) (-0.8616866329484) 0.00000014656 cs_b1left_v1p517_4 0.609304357782 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((1517:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.764793640991) (-0.6442753189918) 0.00000011391 cs_b1left_v1p517_5 0.43085279713513 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((1517:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.764793640991) (-0.6442753189918) 0.00000011391 cs_b1left_v1p517_5 2.863789 (by norm_num) (by norm_num) 3.19141108271701 2.13422522076156 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.5265503159576:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1517:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_10 : mainRemConst 5 (1/4:ℝ) 1.484405 ≤ 14.57770445 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 1.484405 (by norm_num) _ 0.6687403049765 1.60943791291421 14.57770445 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_10 : ∀ y ∈ Set.Icc (((1281:ℤ):ℝ)/1000) (((1517:ℤ):ℝ)/1000), 0 < (I ^ ((-7):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-7):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (-7) (-2) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((1281:ℤ):ℝ)/1000) (((1517:ℤ):ℝ)/1000) (I ^ ((-7):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.484405 1.281 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 14.57770445 rb_b1left_10 0.6687403049765 1.537462 1.965653 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.469131551426 0.392325095196 (by rw [hrot]; exact bv_b1left_1p281_1_5_c0) (by rw [hrot]; exact bv_b1left_1p517_1_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_1p753_1_5_c0 : (0.320159384793:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((1753:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1753:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((1753:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((1753:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((1753:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.3482553755146 (-0.9373996977945) 0.00000010796 cs_b1left_v1p753_2 0.78825595475211 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((1753:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.347656912137) (-0.9376218168542) 0.00000014247 cs_b1left_v1p753_3 0.71243840783742 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((1753:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.7574363868442) (-0.6529089675052) 0.0000001159 cs_b1left_v1p753_4 0.46167627646672 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((1753:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.949157390924) (-0.3148019171688) 0.00000014043 cs_b1left_v1p753_5 0.21052063618341 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((1753:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.949157390924) (-0.3148019171688) 0.00000014043 cs_b1left_v1p753_5 3.635509 (by norm_num) (by norm_num) 2.77048037430874 1.85273189044664 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.17289127523966:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1753:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_11 : mainRemConst 5 (1/4:ℝ) 1.692273 ≤ 12.96552505 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 1.692273 (by norm_num) _ 0.6687403049765 1.60943791291421 12.96552505 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_11 : ∀ y ∈ Set.Icc (((1517:ℤ):ℝ)/1000) (((1753:ℤ):ℝ)/1000), 0 < (I ^ ((-7):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-7):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (-7) (-2) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((1517:ℤ):ℝ)/1000) (((1753:ℤ):ℝ)/1000) (I ^ ((-7):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.692273 1.517 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 12.96552505 rb_b1left_11 0.6687403049765 1.770737 2.153024 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.392325095196 0.320159384793 (by rw [hrot]; exact bv_b1left_1p517_1_5_c0) (by rw [hrot]; exact bv_b1left_1p753_1_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_1p753_0_5_c0 : (0.322901623709:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((1753:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1753:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((1753:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((1753:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((1753:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.3482553755146 (-0.9373996977945) 0.00000010796 cs_b1left_v1p753_2 0.29284660607988 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((1753:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.347656912137) (-0.9376218168542) 0.00000014247 cs_b1left_v1p753_3 (-0.26416223645893) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((1753:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.7574363868442) (-0.6529089675052) 0.0000001159 cs_b1left_v1p753_4 (-0.53558848740869) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((1753:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.949157390924) (-0.3148019171688) 0.00000014043 cs_b1left_v1p753_5 (-0.63473989698842) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((1753:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.949157390924) (-0.3148019171688) 0.00000014043 cs_b1left_v1p753_5 3.635509 (by norm_num) (by norm_num) (-0.69465775433154) (-0.46454563848589) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-0.14164401477616):ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1753:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b1left_1p989_0_5_c0 : (0.374900146641:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((1989:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1989:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((1989:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((1989:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((1989:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.1909468228605 (-0.9816003824568) 0.00000014263 cs_b1left_v1p989_2 0.16056637891042 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((1989:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.5764221643276) (-0.8171520595713) 0.00000014265 cs_b1left_v1p989_3 (-0.43798623884721) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((1989:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.9270786591154) (-0.374866855908) 0.00000011678 cs_b1left_v1p989_4 (-0.65554368912981) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((1989:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.9982256750042) 0.0595441114586 0.00000010162 cs_b1left_v1p989_5 (-0.66755381029508) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((1989:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.9982256750042) 0.0595441114586 0.00000010162 cs_b1left_v1p989_5 4.518621 (by norm_num) (by norm_num) (-1.45858937878416) (-0.97541750600345) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-0.60051735936168):ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((1989:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_12 : mainRemConst 5 (1/4:ℝ) 1.906701 ≤ 11.78347578 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 1.906701 (by norm_num) _ 0.6687403049765 1.60943791291421 11.78347578 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_12 : ∀ y ∈ Set.Icc (((1753:ℤ):ℝ)/1000) (((1989:ℤ):ℝ)/1000), 0 < (I ^ ((-8):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-8):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-8) (-2) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((1753:ℤ):ℝ)/1000) (((1989:ℤ):ℝ)/1000) (I ^ ((-8):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.906701 1.753 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 11.78347578 rb_b1left_12 0.6687403049765 2.00465 2.349175 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.322901623709 0.374900146641 (by rw [hrot]; exact bv_b1left_1p753_0_5_c0) (by rw [hrot]; exact bv_b1left_1p989_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_2p304_0_5_c0 : (0.431779191515:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((2304:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((2304:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((2304:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((2304:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((2304:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.0262117707803) (-0.99965641251) 0.00000010458 cs_b1left_v2p304_2 (-0.02204147202756) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((2304:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.8194245637966) (-0.5731870411911) 0.00000011366 cs_b1left_v2p304_3 (-0.62262811163508) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((2304:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.9986258854982) 0.0524055363972 0.00000010196 cs_b1left_v2p304_4 (-0.70613520760086) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((2304:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.8437564821036) 0.5367261860931 0.00000014419 cs_b1left_v2p304_5 (-0.56425406359353) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((2304:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.8437564821036) 0.5367261860931 0.00000014419 cs_b1left_v2p304_5 5.870916 (by norm_num) (by norm_num) (-2.01399263114629) (-1.34683804637299) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-0.91505885485703):ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((2304:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_13 : mainRemConst 5 (1/4:ℝ) 2.125704 ≤ 10.89192632 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 2.125704 (by norm_num) _ 0.6687403049765 1.60943791291421 10.89192632 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_13 : ∀ y ∈ Set.Icc (((1989:ℤ):ℝ)/1000) (((2304:ℤ):ℝ)/1000), 0 < (I ^ ((-8):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-8):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-8) (-2) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((1989:ℤ):ℝ)/1000) (((2304:ℤ):ℝ)/1000) (I ^ ((-8):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 2.125704 1.989 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 10.89192632 rb_b1left_13 0.6687403049765 2.317524 2.621244 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.374900146641 0.431779191515 (by rw [hrot]; exact bv_b1left_1p989_0_5_c0) (by rw [hrot]; exact bv_b1left_2p304_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_2p619_0_5_c0 : (0.477475530876:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((2619:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((2619:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((2619:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((2619:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((2619:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.2421257279736) (-0.9702448824148) 0.00000013481 cs_b1left_v2p619_2 (-0.20360277005497) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((2619:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.9652685331496) (-0.2612597532327) 0.00000011667 cs_b1left_v2p619_3 (-0.73344556637367) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((2619:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.8827503072903) 0.4698424149438 0.00000012587 cs_b1left_v2p619_4 (-0.62419881738306) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((2619:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.4770288978589) 0.8788876097671 0.00000011589 cs_b1left_v2p619_5 (-0.31900852813708) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((2619:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (-0.4770288978589) 0.8788876097671 0.00000011589 cs_b1left_v2p619_5 7.421661 (by norm_num) (by norm_num) (-2.03028171432406) (-1.35773121282508) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-0.88025568194878):ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((2619:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_14 : mainRemConst 5 (1/4:ℝ) 2.422997 ≤ 10.00462057 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 2.422997 (by norm_num) _ 0.6687403049765 1.60943791291421 10.00462057 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_14 : ∀ y ∈ Set.Icc (((2304:ℤ):ℝ)/1000) (((2619:ℤ):ℝ)/1000), 0 < (I ^ ((-8):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-8):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-8) (-2) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((2304:ℤ):ℝ)/1000) (((2619:ℤ):ℝ)/1000) (I ^ ((-8):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 2.422997 2.304 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 10.00462057 rb_b1left_14 0.6687403049765 2.630905 2.90201 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.431779191515 0.477475530876 (by rw [hrot]; exact bv_b1left_2p304_0_5_c0) (by rw [hrot]; exact bv_b1left_2p619_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_2p934_0_5_c0 : (0.512371575173:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((2934:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((2934:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((2934:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.4465425278859) (-0.8947624102435) 0.00000012848 cs_b1left_v2p934_2 (-0.375496118996) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.9966614923173) 0.081644774618 0.00000014849 cs_b1left_v2p934_3 (-0.75729908120547) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.6011995358404) 0.7990989413665 0.00000014977 cs_b1left_v2p934_4 (-0.42511237454237) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.0097016745975 0.9999529376475 0.00000012933 cs_b1left_v2p934_5 0.00648781434093 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.0097016745975 0.9999529376475 0.00000012933 cs_b1left_v2p934_5 9.170856 (by norm_num) (by norm_num) (-1.59073907712758) (-1.06379133557617) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-0.55141976040291):ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((2934:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_15 : mainRemConst 5 (1/4:ℝ) 2.724272 ≤ 9.34810599 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 2.724272 (by norm_num) _ 0.6687403049765 1.60943791291421 9.34810599 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_15 : ∀ y ∈ Set.Icc (((2619:ℤ):ℝ)/1000) (((2934:ℤ):ℝ)/1000), 0 < (I ^ ((-8):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-8):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-8) (-2) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((2619:ℤ):ℝ)/1000) (((2934:ℤ):ℝ)/1000) (I ^ ((-8):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 2.724272 2.619 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 9.34810599 rb_b1left_15 0.6687403049765 2.944632 3.189178 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.477475530876 0.512371575173 (by rw [hrot]; exact bv_b1left_2p619_0_5_c0) (by rw [hrot]; exact bv_b1left_2p934_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_3p249_0_5_c0 : (0.536135814911:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((3249:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((3249:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((3249:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((3249:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((3249:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.6297558552391) (-0.776793127401) 0.00000011122 cs_b1left_v3p249_2 (-0.52955953468015) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((3249:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.9098812235495) 0.4148688454241 0.0000001195 cs_b1left_v3p249_3 (-0.69136031415762) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((3249:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (-0.2068151185564) 0.9783800420775 0.00000012961 cs_b1left_v3p249_4 (-0.14624046443126) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((3249:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.4939917471344 0.8694665915164 0.00000013139 cs_b1left_v3p249_5 0.33035210376869 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((3249:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.4939917471344 0.8694665915164 0.00000013139 cs_b1left_v3p249_5 11.118501 (by norm_num) (by norm_num) (-0.85675114861294) (-0.57294402441229) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-0.03680820950034):ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((3249:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_16 : mainRemConst 5 (1/4:ℝ) 3.028342 ≤ 8.8455994 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 3.028342 (by norm_num) _ 0.6687403049765 1.60943791291421 8.8455994 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_16 : ∀ y ∈ Set.Icc (((2934:ℤ):ℝ)/1000) (((3249:ℤ):ℝ)/1000), 0 < (I ^ ((-8):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-8):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-8) (-2) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((2934:ℤ):ℝ)/1000) (((3249:ℤ):ℝ)/1000) (I ^ ((-8):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 3.028342 2.934 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 8.8455994 rb_b1left_16 0.6687403049765 3.258605 3.481164 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.512371575173 0.536135814911 (by rw [hrot]; exact bv_b1left_2p934_0_5_c0) (by rw [hrot]; exact bv_b1left_3p249_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_3p67_0_5_c0 : (0.552370784235:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((3670:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((3670:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((3670:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((3670:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((3670:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.8266082172349) (-0.5627778026352) 0.00000014831 cs_b1left_v3p67_2 (-0.69509201140551) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((3670:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.6291676424574) 0.7772696299676 0.00000010874 cs_b1left_v3p67_3 (-0.47806410962096) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((3670:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.3665622032866 0.9303935463672 0.00000010379 cs_b1left_v3p67_4 0.25919854628 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((3670:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9299394438319 0.3677127014473 0.00000013323 cs_b1left_v3p67_5 0.62188789818145 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((3670:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9299394438319 0.3677127014473 0.00000013323 cs_b1left_v3p67_5 14.0314 (by norm_num) (by norm_num) 0.23261576734951 0.15555953919966 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.70793032343498:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((3670:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_17 : mainRemConst 5 (1/4:ℝ) 3.334441 ≤ 8.45005355 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 3.334441 (by norm_num) _ 0.6687403049765 1.60943791291421 8.45005355 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_17 : ∀ y ∈ Set.Icc (((3249:ℤ):ℝ)/1000) (((3670:ℤ):ℝ)/1000), 0 < (I ^ ((-8):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-8):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-8) (-2) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((3249:ℤ):ℝ)/1000) (((3670:ℤ):ℝ)/1000) (I ^ ((-8):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 3.334441 3.249 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 8.45005355 rb_b1left_17 0.6687403049765 3.678506 3.877035 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.536135814911 0.552370784235 (by rw [hrot]; exact bv_b1left_3p249_0_5_c0) (by rw [hrot]; exact bv_b1left_3p67_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_4p091_0_5_c0 : (0.559090453882:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((4091:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((4091:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((4091:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((4091:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((4091:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.9535680041942) (-0.3011777899578) 0.00000011667 cs_b1left_v4p091_2 (-0.80185201453501) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((4091:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (-0.2162442690859) 0.9763392935279 0.00000013532 cs_b1left_v4p091_3 (-0.16431021529008) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((4091:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.8185838816635 0.5743870025346 0.00000012614 cs_b1left_v4p091_4 0.57882612449977 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((4091:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9550330198168 (-0.2964994621574) 0.00000010955 cs_b1left_v4p091_5 0.63866899967431 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((4091:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.9550330198168 (-0.2964994621574) 0.00000010955 cs_b1left_v4p091_5 17.298781 (by norm_num) (by norm_num) 1.03514388966083 0.69224244046635 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.25133289434899:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((4091:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_18 : mainRemConst 5 (1/4:ℝ) 3.745851 ≤ 8.03771682 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 3.745851 (by norm_num) _ 0.6687403049765 1.60943791291421 8.03771682 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_18 : ∀ y ∈ Set.Icc (((3670:ℤ):ℝ)/1000) (((4091:ℤ):ℝ)/1000), 0 < (I ^ ((-8):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-8):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-8) (-2) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((3670:ℤ):ℝ)/1000) (((4091:ℤ):ℝ)/1000) (I ^ ((-8):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 3.745851 3.67 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 8.03771682 rb_b1left_18 0.6687403049765 4.098632 4.277708 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.552370784235 0.559090453882 (by rw [hrot]; exact bv_b1left_3p67_0_5_c0) (by rw [hrot]; exact bv_b1left_4p091_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1left_4p406_0_5_c0 : (0.566804251516:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1/4:ℝ):ℝ)):ℂ) + ((((((4406:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((4406:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((4406:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((4406:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((4406:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (-0.9961667840501) (-0.0874742125248) 0.00000012361 cs_b1left_v4p406_2 (-0.83767318164585) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((4406:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.1277466957791 0.9918068268153 0.00000013776 cs_b1left_v4p406_3 0.09706639350206 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((4406:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.9846965080283 0.1742779018607 0.00000015005 cs_b1left_v4p406_4 0.6962854721361 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((4406:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.6909470008599 (-0.7229054170517) 0.00000013714 cs_b1left_v4p406_5 0.46206401636653 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1/4:ℝ) (((4406:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.6909470008599 (-0.7229054170517) 0.00000013714 cs_b1left_v4p406_5 19.975336 (by norm_num) (by norm_num) 1.27244977237109 0.85093844884273 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.41774270035884:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((4406:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1left_19 : mainRemConst 5 (1/4:ℝ) 4.15918 ≤ 7.718351 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1/4:ℝ) 1 0 (pw1_hi (1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1/4:ℝ) 0.8408964152538 0.6931471808 (pwh_2_1_4 (1/4:ℝ) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1/4:ℝ) 0.7598356856516 1.098612288908165 (pwh_3_1_4 (1/4:ℝ) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1/4:ℝ) 0.7071067811866 1.3862943616 (pwh_4_1_4 (1/4:ℝ) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1/4:ℝ) 0.6687403049765 1.60943791291421 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1/4:ℝ) 4.15918 (by norm_num) _ 0.6687403049765 1.60943791291421 7.718351 c5 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1left_19 : ∀ y ∈ Set.Icc (((4091:ℤ):ℝ)/1000) (((4406:ℤ):ℝ)/1000), 0 < (I ^ ((-8):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-8):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (-8) (-2) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1/4:ℝ) (((4091:ℤ):ℝ)/1000) (((4406:ℤ):ℝ)/1000) (I ^ ((-8):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 4.15918 4.091 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 7.718351 rb_b1left_19 0.6687403049765 4.413087 4.579884 (pwh_5_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.559090453882 0.566804251516 (by rw [hrot]; exact bv_b1left_4p091_0_5_c0) (by rw [hrot]; exact bv_b1left_4p406_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)

end H22
end Cert
end ZB
end RHV6Fresh
