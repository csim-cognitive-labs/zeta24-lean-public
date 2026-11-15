/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Side_b1bottom_trig0
/-!
# Certificat (V2), côté b1bottom (b1), morceaux 0

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
lemma bv_b1bottom_0p25_3_5_c0 : (0.556767974975:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((8:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((8:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((8:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (((8:ℤ):ℝ)/32)) (pw1_hi (((8:ℤ):ℝ)/32)) 1 0 0 (cs_one (-1:ℝ)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((8:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) (pwh_2_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_hm1_2 0.53730015864917 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((8:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) (pwh_3_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_hm1_3 0.67669213619214 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((8:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) (pwh_4_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_hm1_4 0.69510548780509 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((8:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) (pwh_5_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 0.66824101970217 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((8:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) (pwh_5_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 1.5625 (by norm_num) (by norm_num) 3.02145812408317 2.02057082737311 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.57733880234857:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((8:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b1bottom_0p53125_3_5_c0 : (0.738184693861:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((17:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((17:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((17:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (((17:ℤ):ℝ)/32)) (pw1_hi (((17:ℤ):ℝ)/32)) 1 0 0 (cs_one (-1:ℝ)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((17:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.6919549409819 0.691954940982 (pwl_2_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) (pwh_2_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_hm1_2 0.44213233975493 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((17:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.5578652806066 0.5578652806067 (pwl_3_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) (pwh_3_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_hm1_3 0.49682195186375 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((17:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4788016403492 0.4788016403493 (pwl_4_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) (pwh_4_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_hm1_4 0.4706752312831 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((17:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4252772835227 0.4252772835228 (pwl_5_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) (pwh_5_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 0.42495976911008 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((17:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4252772835227 0.4252772835228 (pwl_5_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) (pwh_5_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 1.2197265625 (by norm_num) (by norm_num) 2.57809349483229 1.09640459815008 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.83458929201186:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((17:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1bottom_0 : mainRemConst 5 (((8:ℤ):ℝ)/32) 1 ≤ 22.66470731 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (((8:ℤ):ℝ)/32))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (((8:ℤ):ℝ)/32) 1 0 (pw1_hi (((8:ℤ):ℝ)/32)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (((8:ℤ):ℝ)/32) 0.8408964152538 0.6931471808 (pwh_2_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) (lg_2).2 0.40401121738154 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (((8:ℤ):ℝ)/32) 0.7598356856516 1.098612288908165 (pwh_3_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) (lg_3).2 0.9170828915863 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (((8:ℤ):ℝ)/32) 0.7071067811866 1.3862943616 (pwh_4_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) (lg_4).2 1.35892633767367 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (((8:ℤ):ℝ)/32) 0.6687403049765 1.60943791291421 (pwh_5_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 1.73223158908153 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (((8:ℤ):ℝ)/32) 1 (by norm_num) _ 0.6687403049765 1.60943791291421 22.66470731 c5 (pwh_5_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1bottom_0 : ∀ x ∈ Set.Icc (((8:ℤ):ℝ)/32) (((17:ℤ):ℝ)/32), 0 < (I ^ ((-1):ℤ) * riemannZeta ((x:ℂ) + ((-1:ℝ):ℂ) * I)).re := by
  have hrot : I ^ ((-1):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-1) (-1) 3 (by norm_num), rot3])
  refine horizontal_piece 5 (by norm_num) (-1:ℝ) (((8:ℤ):ℝ)/32) (((17:ℤ):ℝ)/32) (I ^ ((-1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1 (by norm_num) (by norm_num) 22.66470731 rb_b1bottom_0 0.6687403049765 1.132355 1.82886 (pwh_5_8_32 (((8:ℤ):ℝ)/32) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0.556767974975 0.738184693861 (by rw [hrot]; exact bv_b1bottom_0p25_3_5_c0) (by rw [hrot]; exact bv_b1bottom_0p53125_3_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1bottom_0p9375_3_5_c0 : (0.918735456493:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((30:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((30:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((30:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (((30:ℤ):ℝ)/32)) (pw1_hi (((30:ℤ):ℝ)/32)) 1 0 0 (cs_one (-1:ℝ)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((30:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.5221368912137 0.5221368912138 (pwl_2_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) (pwh_2_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_hm1_2 0.3336251997234 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((30:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3570251610243 0.3570251610244 (pwl_3_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) (pwh_3_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_hm1_3 0.31795837369855 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((30:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2726269331663 0.2726269331664 (pwl_4_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) (pwh_4_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_hm1_4 0.26799980202337 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((30:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.221164603406 0.2211646034061 (pwl_5_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) (pwh_5_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 0.22099948066875 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((30:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.221164603406 0.2211646034061 (pwl_5_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) (pwh_5_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 1.00390625 (by norm_num) (by norm_num) 1.00308727619029 0.22184739962034 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.14058285611407:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((30:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1bottom_1 : mainRemConst 5 (((17:ℤ):ℝ)/32) 1 ≤ 14.63495267 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (((17:ℤ):ℝ)/32))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (((17:ℤ):ℝ)/32) 1 0 (pw1_hi (((17:ℤ):ℝ)/32)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (((17:ℤ):ℝ)/32) 0.691954940982 0.6931471808 (pwh_2_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) (lg_2).2 0.33245183712067 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (((17:ℤ):ℝ)/32) 0.5578652806067 1.098612288908165 (pwh_3_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) (lg_3).2 0.67331492099593 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (((17:ℤ):ℝ)/32) 0.4788016403493 1.3862943616 (pwh_4_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) (lg_4).2 0.92016676533656 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (((17:ℤ):ℝ)/32) 0.4252772835228 1.60943791291421 (pwh_5_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 1.10159166294435 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (((17:ℤ):ℝ)/32) 1 (by norm_num) _ 0.4252772835228 1.60943791291421 14.63495267 c5 (pwh_5_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1bottom_1 : ∀ x ∈ Set.Icc (((17:ℤ):ℝ)/32) (((30:ℤ):ℝ)/32), 0 < (I ^ ((-1):ℤ) * riemannZeta ((x:ℂ) + ((-1:ℝ):ℂ) * I)).re := by
  have hrot : I ^ ((-1):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-1) (-1) 3 (by norm_num), rot3])
  refine horizontal_piece 5 (by norm_num) (-1:ℝ) (((17:ℤ):ℝ)/32) (((30:ℤ):ℝ)/32) (I ^ ((-1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1 (by norm_num) (by norm_num) 14.63495267 rb_b1bottom_1 0.4252772835228 1.370733 2.180346 (pwh_5_17_32 (((17:ℤ):ℝ)/32) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0.738184693861 0.918735456493 (by rw [hrot]; exact bv_b1bottom_0p53125_3_5_c0) (by rw [hrot]; exact bv_b1bottom_0p9375_3_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1bottom_1p5_3_5_c0 : (0.729795372729:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((48:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((48:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((48:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (((48:ℤ):ℝ)/32)) (pw1_hi (((48:ℤ):ℝ)/32)) 1 0 0 (cs_one (-1:ℝ)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((48:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_2_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (pwh_2_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_hm1_2 0.22590688866162 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((48:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_3_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (pwh_3_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_hm1_3 0.17139161109282 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((48:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.125 0.125 (pwl_4_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (pwh_4_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_hm1_4 0.12287845101675 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((48:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.0894427190999 0.0894427191 (pwl_5_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (pwh_5_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 0.08937594066258 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((48:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.0894427190999 0.0894427191 (pwl_5_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (pwh_5_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 1.25 (by norm_num) (by norm_num) (-1.34435180980375) (-0.12024248129571) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.60955289143377:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((48:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1bottom_2 : mainRemConst 5 (((30:ℤ):ℝ)/32) 1 ≤ 7.81501119 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (((30:ℤ):ℝ)/32))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (((30:ℤ):ℝ)/32) 1 0 (pw1_hi (((30:ℤ):ℝ)/32)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (((30:ℤ):ℝ)/32) 0.5221368912138 0.6931471808 (pwh_2_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) (lg_2).2 0.25086224323532 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (((30:ℤ):ℝ)/32) 0.3570251610244 1.098612288908165 (pwh_3_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) (lg_3).2 0.43091114727066 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (((30:ℤ):ℝ)/32) 0.2726269331664 1.3862943616 (pwh_4_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) (lg_4).2 0.5239377272232 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (((30:ℤ):ℝ)/32) 0.2211646034061 1.60943791291421 (pwh_5_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 0.57288054803306 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (((30:ℤ):ℝ)/32) 1 (by norm_num) _ 0.2211646034061 1.60943791291421 7.81501119 c5 (pwh_5_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1bottom_2 : ∀ x ∈ Set.Icc (((30:ℤ):ℝ)/32) (((48:ℤ):ℝ)/32), 0 < (I ^ ((-1):ℤ) * riemannZeta ((x:ℂ) + ((-1:ℝ):ℂ) * I)).re := by
  have hrot : I ^ ((-1):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-1) (-1) 3 (by norm_num), rot3])
  refine horizontal_piece 5 (by norm_num) (-1:ℝ) (((30:ℤ):ℝ)/32) (((48:ℤ):ℝ)/32) (I ^ ((-1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1 (by norm_num) (by norm_num) 7.81501119 rb_b1bottom_2 0.2211646034061 1.802776 2.692583 (pwh_5_30_32 (((30:ℤ):ℝ)/32) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0.918735456493 0.729795372729 (by rw [hrot]; exact bv_b1bottom_0p9375_3_5_c0) (by rw [hrot]; exact bv_b1bottom_1p5_3_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b1bottom_1p5_0_5_c0 : (1.016289354822:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((48:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((48:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((48:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (((48:ℤ):ℝ)/32)) (pw1_hi (((48:ℤ):ℝ)/32)) 1 0 0 (cs_one (-1:ℝ)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((48:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_2_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (pwh_2_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_hm1_2 0.27196697503789 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((48:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_3_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (pwh_3_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_hm1_3 0.08753251716345 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((48:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.125 0.125 (pwl_4_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (pwh_4_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_hm1_4 0.02293209963913 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((48:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0894427190999 0.0894427191 (pwl_5_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (pwh_5_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 (-0.00345535742455) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((48:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0894427190999 0.0894427191 (pwl_5_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (pwh_5_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 1.25 (by norm_num) (by norm_num) 4.0549625865936 0.36268687959371 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.37897623441592:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((48:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b1bottom_2_0_5_c0 : (1.149751453998:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((64:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((64:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((64:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (((64:ℤ):ℝ)/32)) (pw1_hi (((64:ℤ):ℝ)/32)) 1 0 0 (cs_one (-1:ℝ)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((64:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_2_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_hm1_2 0.19230969230812 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((64:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_3_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_hm1_3 0.05053692234718 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((64:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_4_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_hm1_4 0.01146604981956 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((64:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_5_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 (-0.00154528281757) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((64:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_5_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 2 (by norm_num) (by norm_num) 2.57539819146265 0.10301592765851 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.25276738165729:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((64:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b1bottom_3 : mainRemConst 5 (((48:ℤ):ℝ)/32) 1 ≤ 3.31528286 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (((48:ℤ):ℝ)/32))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (((48:ℤ):ℝ)/32) 1 0 (pw1_hi (((48:ℤ):ℝ)/32)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (((48:ℤ):ℝ)/32) 0.3535533905933 0.6931471808 (pwh_2_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (lg_2).2 0.16986579220921 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (((48:ℤ):ℝ)/32) 0.1924500897299 1.098612288908165 (pwh_3_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (lg_3).2 0.2322774359093 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (((48:ℤ):ℝ)/32) 0.125 1.3862943616 (pwh_4_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (lg_4).2 0.2402265071255 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (((48:ℤ):ℝ)/32) 0.0894427191 1.60943791291421 (pwh_5_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 0.23168261623443 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (((48:ℤ):ℝ)/32) 1 (by norm_num) _ 0.0894427191 1.60943791291421 3.31528286 c5 (pwh_5_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b1bottom_3 : ∀ x ∈ Set.Icc (((48:ℤ):ℝ)/32) (((64:ℤ):ℝ)/32), 0 < (I ^ ((0):ℤ) * riemannZeta ((x:ℂ) + ((-1:ℝ):ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine horizontal_piece 5 (by norm_num) (-1:ℝ) (((48:ℤ):ℝ)/32) (((64:ℤ):ℝ)/32) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1 (by norm_num) (by norm_num) 3.31528286 rb_b1bottom_3 0.0894427191 2.236068 3.162278 (pwh_5_48_32 (((48:ℤ):ℝ)/32) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1.016289354822 1.149751453998 (by rw [hrot]; exact bv_b1bottom_1p5_0_5_c0) (by rw [hrot]; exact bv_b1bottom_2_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)

end H22
end Cert
end ZB
end RHV6Fresh
