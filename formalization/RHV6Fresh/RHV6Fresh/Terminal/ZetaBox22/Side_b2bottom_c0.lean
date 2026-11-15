/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Side_b2bottom_trig0
/-!
# Certificat (V2), côté b2bottom (b2), morceaux 0

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
lemma bv_b2bottom_0p75_3_5_c0 : (0.861638479504:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((24:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((24:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((24:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (((24:ℤ):ℝ)/32)) (pw1_hi (((24:ℤ):ℝ)/32)) 1 0 0 (cs_one (-1:ℝ)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((24:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_2_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_hm1_2 0.3799285857134 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((24:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_3_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_hm1_3 0.39068838698905 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((24:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_4_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_hm1_4 0.34755274390249 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((24:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_5_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 0.29884646908153 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((24:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_5_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 1.0625 (by norm_num) (by norm_num) 1.85701728304685 0.55537770618228 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.41701618568647:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((24:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b2bottom_1p15625_3_5_c0 : (0.901521257831:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((37:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((37:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((37:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (((37:ℤ):ℝ)/32)) (pw1_hi (((37:ℤ):ℝ)/32)) 1 0 0 (cs_one (-1:ℝ)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((37:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4486772687507 0.4486772687508 (pwl_2_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (pwh_2_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_hm1_2 0.28668735329225 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((37:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2807556786728 0.2807556786729 (pwl_3_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (pwh_3_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_hm1_3 0.25003453185575 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((37:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2013112914936 0.2013112914937 (pwl_4_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (pwh_4_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_hm1_4 0.19789455736732 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((37:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1555306304691 0.1555306304692 (pwl_5_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (pwh_5_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 0.15541451042532 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((37:ℤ):ℝ)/32) (-1:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1555306304691 0.1555306304692 (pwl_5_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (pwh_5_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 1.0244140625 (by norm_num) (by norm_num) (-0.07387808341396) (-0.01149030489122) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.89003095294064:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((37:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2bottom_0 : mainRemConst 5 (((24:ℤ):ℝ)/32) 1 ≤ 10.43204396 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (((24:ℤ):ℝ)/32))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (((24:ℤ):ℝ)/32) 1 0 (pw1_hi (((24:ℤ):ℝ)/32)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (((24:ℤ):ℝ)/32) 0.5946035575014 0.6931471808 (pwh_2_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (((24:ℤ):ℝ)/32) 0.4386913376509 1.098612288908165 (pwh_3_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (((24:ℤ):ℝ)/32) 0.3535533905933 1.3862943616 (pwh_4_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (((24:ℤ):ℝ)/32) 0.2990697562443 1.60943791291421 (pwh_5_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (((24:ℤ):ℝ)/32) 1 (by norm_num) _ 0.2990697562443 1.60943791291421 10.43204396 c5 (pwh_5_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2bottom_0 : ∀ x ∈ Set.Icc (((24:ℤ):ℝ)/32) (((37:ℤ):ℝ)/32), 0 < (I ^ ((-1):ℤ) * riemannZeta ((x:ℂ) + ((-1:ℝ):ℂ) * I)).re := by
  have hrot : I ^ ((-1):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-1) (-1) 3 (by norm_num), rot3])
  refine horizontal_piece 5 (by norm_num) (-1:ℝ) (((24:ℤ):ℝ)/32) (((37:ℤ):ℝ)/32) (I ^ ((-1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1 (by norm_num) (by norm_num) 10.43204396 rb_b2bottom_0 0.2990697562443 1.528697 2.37685 (pwh_5_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0.861638479504 0.901521257831 (by rw [hrot]; exact bv_b2bottom_0p75_3_5_c0) (by rw [hrot]; exact bv_b2bottom_1p15625_3_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2bottom_1p15625_0_5_c0 : (0.743628786189:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((37:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((37:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((37:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (((37:ℤ):ℝ)/32)) (pw1_hi (((37:ℤ):ℝ)/32)) 1 0 0 (cs_one (-1:ℝ)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((37:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.4486772687507 0.4486772687508 (pwl_2_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (pwh_2_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_hm1_2 0.34513994999638 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((37:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.2807556786728 0.2807556786729 (pwl_3_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (pwh_3_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_hm1_3 0.12769675138457 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((37:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.2013112914936 0.2013112914937 (pwl_4_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (pwh_4_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_hm1_4 0.03693192476011 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((37:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1555306304691 0.1555306304692 (pwl_5_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (pwh_5_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 (-0.00600847027174) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((37:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1555306304691 0.1555306304692 (pwl_5_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (pwh_5_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 1.0244140625 (by norm_num) (by norm_num) 4.8873419170663 0.76013136967988 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.50376015586932:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((37:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b2bottom_1p625_0_5_c0 : (1.07442613635:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((52:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((52:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((52:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (((52:ℤ):ℝ)/32)) (pw1_hi (((52:ℤ):ℝ)/32)) 1 0 0 (cs_one (-1:ℝ)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((52:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.3242098886627 0.3242098886628 (pwl_2_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) (pwh_2_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_hm1_2 0.2493948157279 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((52:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1677559609419 0.167755960942 (pwl_3_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) (pwh_3_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_hm1_3 0.07630082974258 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((52:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1051120519067 0.1051120519068 (pwl_4_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) (pwh_4_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_hm1_4 0.01928352038078 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((52:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0731431639991 0.0731431639992 (pwl_5_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) (pwh_5_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 (-0.00282567186377) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((52:ℤ):ℝ)/32) (-1:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0731431639991 0.0731431639992 (pwl_5_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) (pwh_5_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_hm1_5 1.390625 (by norm_num) (by norm_num) 3.66031961155146 0.2677273576372 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.34215349398749:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((52:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2bottom_1 : mainRemConst 5 (((37:ℤ):ℝ)/32) 1 ≤ 5.58919795 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (((37:ℤ):ℝ)/32))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (((37:ℤ):ℝ)/32) 1 0 (pw1_hi (((37:ℤ):ℝ)/32)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (((37:ℤ):ℝ)/32) 0.4486772687508 0.6931471808 (pwh_2_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (lg_2).2 0.21556834619723 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (((37:ℤ):ℝ)/32) 0.2807556786729 1.098612288908165 (pwh_3_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (lg_3).2 0.33885777476458 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (((37:ℤ):ℝ)/32) 0.2013112914937 1.3862943616 (pwh_4_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (lg_4).2 0.38688246720363 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (((37:ℤ):ℝ)/32) 0.1555306304692 1.60943791291421 (pwh_5_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 0.40286949831442 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (((37:ℤ):ℝ)/32) 1 (by norm_num) _ 0.1555306304692 1.60943791291421 5.58919795 c5 (pwh_5_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2bottom_1 : ∀ x ∈ Set.Icc (((37:ℤ):ℝ)/32) (((52:ℤ):ℝ)/32), 0 < (I ^ ((0):ℤ) * riemannZeta ((x:ℂ) + ((-1:ℝ):ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine horizontal_piece 5 (by norm_num) (-1:ℝ) (((37:ℤ):ℝ)/32) (((52:ℤ):ℝ)/32) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1 (by norm_num) (by norm_num) 5.58919795 rb_b2bottom_1 0.1555306304692 1.908043 2.809026 (pwh_5_37_32 (((37:ℤ):ℝ)/32) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0.743628786189 1.07442613635 (by rw [hrot]; exact bv_b2bottom_1p15625_0_5_c0) (by rw [hrot]; exact bv_b2bottom_1p625_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2bottom_2_0_5_c0 : (1.149751453998:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((64:ℤ):ℝ)/32):ℝ)):ℂ) + ((((-1:ℝ):ℝ)):ℂ) * I)).re := by
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
lemma rb_b2bottom_2 : mainRemConst 5 (((52:ℤ):ℝ)/32) 1 ≤ 2.74606207 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (((52:ℤ):ℝ)/32))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (((52:ℤ):ℝ)/32) 1 0 (pw1_hi (((52:ℤ):ℝ)/32)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (((52:ℤ):ℝ)/32) 0.3242098886628 0.6931471808 (pwh_2_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) (lg_2).2 0.15576761825802 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (((52:ℤ):ℝ)/32) 0.167755960942 1.098612288908165 (pwh_3_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) (lg_3).2 0.20247288281755 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (((52:ℤ):ℝ)/32) 0.1051120519068 1.3862943616 (pwh_4_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) (lg_4).2 0.20200560869092 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (((52:ℤ):ℝ)/32) 0.0731431639992 1.60943791291421 (pwh_5_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 0.18946203520549 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (((52:ℤ):ℝ)/32) 1 (by norm_num) _ 0.0731431639992 1.60943791291421 2.74606207 c5 (pwh_5_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2bottom_2 : ∀ x ∈ Set.Icc (((52:ℤ):ℝ)/32) (((64:ℤ):ℝ)/32), 0 < (I ^ ((0):ℤ) * riemannZeta ((x:ℂ) + ((-1:ℝ):ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine horizontal_piece 5 (by norm_num) (-1:ℝ) (((52:ℤ):ℝ)/32) (((64:ℤ):ℝ)/32) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1 (by norm_num) (by norm_num) 2.74606207 rb_b2bottom_2 0.0731431639992 2.236068 3.162278 (pwh_5_52_32 (((52:ℤ):ℝ)/32) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1.07442613635 1.149751453998 (by rw [hrot]; exact bv_b2bottom_1p625_0_5_c0) (by rw [hrot]; exact bv_b2bottom_2_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)

end H22
end Cert
end ZB
end RHV6Fresh
