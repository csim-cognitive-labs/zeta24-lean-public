/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Side_right_trig0
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
namespace H22

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
lemma bv_right_22_0_5_c2 : (0.870608663827:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((22000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((22000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((22000:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.8966176905623) (-0.4428055068064) 0.00000014777 cs_right_v22_2 (-0.22415445958308) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.5708374291683 0.8210631093044 0.00000012728 cs_right_v22_3 0.06342636687647 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.6078464924715 0.7940545583208 0.00000011932 cs_right_v22_4 0.03799039832196 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6598968542787) 0.7513562016082 0.00000014105 cs_right_v22_5 (-0.02639587981315) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6598968542787) 0.7513562016082 0.00000014105 cs_right_v22_5 485 (by norm_num) (by norm_num) (-0.49355595062519) (-0.019742238025) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.8508664258022:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((22000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
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
lemma pc_right_40 : ∀ y ∈ Set.Icc (((21480:ℤ):ℝ)/1000) (((22000:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((21480:ℤ):ℝ)/1000) (((22000:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 21.503264 21.48 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.5545577 rb_right_40 0.04 22.090723 22.203604 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.808792751305 0.870608663827 (by rw [hrot]; exact bv_right_21p48_0_5_c2) (by rw [hrot]; exact bv_right_22_0_5_c2) (by rw [lt_min_iff]; constructor <;> norm_num)

end H22
end Cert
end ZB
end RHV6Fresh
