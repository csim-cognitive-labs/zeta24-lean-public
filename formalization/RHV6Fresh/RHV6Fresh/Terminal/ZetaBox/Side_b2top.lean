/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox.Base
/-!
# Certificat (V2), côté b2top (b2)

Fichier GENERE par `experiments/e192_zeta_box_certificate_generator.py` : constantes rationnelles calculees en
arithmetique exacte puis verifiees par Lean (`norm_num`, `linarith`, `decide`). Aucune preuve admise, aucun axiome ajoute.
-/

set_option maxHeartbeats 4000000
set_option linter.style.longLine false

namespace RHV6Fresh
namespace ZB
namespace Cert

open Complex Set
lemma bv_b2top_0p75_3_10 : (0.616549796996:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((((24:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((24:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((24:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (((24:ℤ):ℝ)/32)) (pw1_hi (((24:ℤ):ℝ)/32)) 1 0 0 (cs_one (15:ℝ)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((24:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_2_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.5632935954295) 0.826256815608 0.00000010987 cs_h15_2 0.49129517664111 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((24:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_3_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.7170601161939) 0.6970113268357 0.0000001121 cs_h15_3 0.30577278215001 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((24:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_4_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.3654006440121) (-0.9308503474528) 0.00000011255 cs_h15_4 (-0.32910533626933) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((24:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_5_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) 0.5477092431889 0.8366687426487 0.00000015002 cs_h15_5 0.25022227205464 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (((24:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_6_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.1719949813052) (-0.9850978258047) 0.00000011692 cs_h15_6 (-0.25696026667015) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (((24:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_7_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.6103306811647) 0.7921467412141 0.00000010788 cs_h15_7 0.1840695924584 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (((24:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_8_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) 0.9749492864381 0.2224272664803 0.00000012241 cs_h15_8 0.04675954702595 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (((24:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_9_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) 0.0283504276599 (-0.9995980458421) 0.00000013136 cs_h15_9 (-0.19237275889639) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (((24:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_10_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.9998243594199) (-0.0187416559615) 0.0000001527 cs_h15_10 (-0.00333281724497) (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (((24:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_10_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.9998243594199) (-0.0187416559615) 0.0000001527 cs_h15_10 225.0625 (by norm_num) (by norm_num) (-0.67594330266052) (-0.12020160574742) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.49634819124927:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((24:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma bv_b2top_1p0625_3_10 : (0.488374072687:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((((34:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((34:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (((34:ℤ):ℝ)/32)) (pw1_hi (((34:ℤ):ℝ)/32)) 1 0 0 (cs_one (15:ℝ)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4788016403492 0.4788016403493 (pwl_2_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_2_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.5632935954295) 0.826256815608 0.00000010987 cs_h15_2 0.39561306605688 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3112136713063 0.3112136713064 (pwl_3_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_3_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.7170601161939) 0.6970113268357 0.0000001121 cs_h15_3 0.21691941907956 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2292510108011 0.2292510108012 (pwl_4_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_4_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.3654006440121) (-0.9308503474528) 0.00000011255 cs_h15_4 (-0.21339840886041) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1808607678804 0.1808607678805 (pwl_5_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_5_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) 0.5477092431889 0.8366687426487 0.00000015002 cs_h15_5 0.15132052412424 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1490096163205 0.1490096163206 (pwl_6_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_6_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.1719949813052) (-0.9850978258047) 0.00000011692 cs_h15_6 (-0.14678906648362) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1264979048539 0.126497904854 (pwl_7_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_7_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.6103306811647) 0.7921467412141 0.00000010788 cs_h15_7 0.10020488945383 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1097657600233 0.1097657600234 (pwl_8_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_8_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) 0.9749492864381 0.2224272664803 0.00000012241 cs_h15_8 0.02441488451868 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.0968539492079 0.096853949208 (pwl_9_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_9_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) 0.0283504276599 (-0.9995980458421) 0.00000013136 cs_h15_9 (-0.09681503108315) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.086596432336 0.0865964323361 (pwl_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.9998243594199) (-0.0187416559615) 0.0000001527 cs_h15_10 (-0.00162297376562) (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (0:ℝ) ((-1):ℝ) (by norm_num) 0.086596432336 0.0865964323361 (pwl_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.9998243594199) (-0.0187416559615) 0.0000001527 cs_h15_10 225.00390625 (by norm_num) (by norm_num) (-0.67585659211133) (-0.0585267696476) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.42984730304039:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((34:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma rb_b2top_0 : mainRemConst 10 (((24:ℤ):ℝ)/32) 15 ≤ 7.8862492 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (((24:ℤ):ℝ)/32))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (((24:ℤ):ℝ)/32) 1 0 (pw1_hi (((24:ℤ):ℝ)/32)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (((24:ℤ):ℝ)/32) 0.5946035575014 0.6931471808 (pwh_2_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (((24:ℤ):ℝ)/32) 0.4386913376509 1.098612288908165 (pwh_3_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (((24:ℤ):ℝ)/32) 0.3535533905933 1.3862943616 (pwh_4_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (((24:ℤ):ℝ)/32) 0.2990697562443 1.60943791291421 (pwh_5_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (((24:ℤ):ℝ)/32) 0.2608474300123 1.791759469708165 (pwh_6_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (((24:ℤ):ℝ)/32) 0.2323680802426 1.945910149535424 (pwh_7_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (((24:ℤ):ℝ)/32) 0.2102241038135 2.0794415424 (pwh_8_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (((24:ℤ):ℝ)/32) 0.1924500897299 2.19722457781633 (pwh_9_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (((24:ℤ):ℝ)/32) 0.1778279410039 2.30258509371421 (pwh_10_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  exact mainRemConst_le 10 (by norm_num) (((24:ℤ):ℝ)/32) 15 (by norm_num) _ 0.1778279410039 2.30258509371421 7.8862492 c10 (pwh_10_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_10).2 (by norm_num)
lemma pc_b2top_0 : ∀ x ∈ Set.Icc (((24:ℤ):ℝ)/32) (((34:ℤ):ℝ)/32), 0 < (I ^ ((-1):ℤ) * riemannZeta ((x:ℂ) + ((15:ℝ):ℂ) * I)).re := by
  have hrot : I ^ ((-1):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-1) (-1) 3 (by norm_num), rot3])
  refine horizontal_piece 10 (by norm_num) (15:ℝ) (((24:ℤ):ℝ)/32) (((34:ℤ):ℝ)/32) (I ^ ((-1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.30258509371421 (lg_10).2 (by norm_num) 15 (by norm_num) (by norm_num) 7.8862492 rb_b2top_0 0.1778279410039 15.037584 15.141133 (pwh_10_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0.616549796996 0.488374072687 (by rw [hrot]; exact bv_b2top_0p75_3_10) (by rw [hrot]; exact bv_b2top_1p0625_3_10) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2top_1p0625_0_10 : (0.484739988549:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((((34:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((34:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (((34:ℤ):ℝ)/32)) (pw1_hi (((34:ℤ):ℝ)/32)) 1 0 0 (cs_one (15:ℝ)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.4788016403492 0.4788016403493 (pwl_2_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_2_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.5632935954295) 0.826256815608 0.00000010987 cs_h15_2 (-0.26970595009584) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.3112136713063 0.3112136713064 (pwl_3_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_3_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.7170601161939) 0.6970113268357 0.0000001121 cs_h15_3 (-0.22315894619515) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.2292510108011 0.2292510108012 (pwl_4_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_4_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.3654006440121) (-0.9308503474528) 0.00000011255 cs_h15_4 (-0.08376849278939) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1808607678804 0.1808607678805 (pwl_5_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_5_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) 0.5477092431889 0.8366687426487 0.00000015002 cs_h15_5 0.0990590871656 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1490096163205 0.1490096163206 (pwl_6_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_6_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.1719949813052) (-0.9850978258047) 0.00000011692 cs_h15_6 (-0.02562892359557) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1264979048539 0.126497904854 (pwl_7_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_7_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.6103306811647) 0.7921467412141 0.00000010788 cs_h15_7 (-0.07720556608205) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1097657600233 0.1097657600234 (pwl_8_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_8_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) 0.9749492864381 0.2224272664803 0.00000012241 cs_h15_8 0.10701603597362 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0968539492079 0.096853949208 (pwl_9_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_9_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) 0.0283504276599 (-0.9995980458421) 0.00000013136 cs_h15_9 0.00274583815785 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.086596432336 0.0865964323361 (pwl_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.9998243594199) (-0.0187416559615) 0.0000001527 cs_h15_10 (-0.08658123571177) (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (((34:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.086596432336 0.0865964323361 (pwl_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.9998243594199) (-0.0187416559615) 0.0000001527 cs_h15_10 225.00390625 (by norm_num) (by norm_num) (-0.48464053992048) (-0.0419681417225) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.4427718468273:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((34:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma bv_b2top_1p4375_0_10 : (0.629130140473:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((((46:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((46:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (((46:ℤ):ℝ)/32)) (pw1_hi (((46:ℤ):ℝ)/32)) 1 0 0 (cs_one (15:ℝ)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.3692065364848 0.3692065364849 (pwl_2_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_2_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.5632935954295) 0.826256815608 0.00000010987 cs_h15_2 (-0.20797171795738) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.2061285728248 0.2061285728249 (pwl_3_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_3_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.7170601161939) 0.6970113268357 0.0000001121 cs_h15_3 (-0.14780660148772) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1363134665831 0.1363134665832 (pwl_4_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_4_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.3654006440121) (-0.9308503474528) 0.00000011255 cs_h15_4 (-0.04980904381911) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0989078174865 0.0989078174866 (pwl_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) 0.5477092431889 0.8366687426487 0.00000015002 cs_h15_5 0.05417271102284 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0761040164432 0.0761040164433 (pwl_6_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_6_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.1719949813052) (-0.9850978258047) 0.00000011692 cs_h15_6 (-0.0130895177835) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0609777741581 0.0609777741582 (pwl_7_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_7_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.6103306811647) 0.7921467412141 0.00000010788 cs_h15_7 (-0.03721661301617) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0503278228734 0.0503278228735 (pwl_8_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_8_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) 0.9749492864381 0.2224272664803 0.00000012241 cs_h15_8 0.04906706883777 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0424889885348 0.0424889885349 (pwl_9_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_9_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) 0.0283504276599 (-0.9995980458421) 0.00000013136 cs_h15_9 0.00120457541444 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0365174127254 0.0365174127255 (pwl_10_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_10_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.9998243594199) (-0.0187416559615) 0.0000001527 cs_h15_10 (-0.03651100436216) (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0365174127254 0.0365174127255 (pwl_10_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_10_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.9998243594199) (-0.0187416559615) 0.0000001527 cs_h15_10 225.19140625 (by norm_num) (by norm_num) (-0.46800368232701) (-0.01709028362454) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.61203985684901:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((46:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma rb_b2top_1 : mainRemConst 10 (((34:ℤ):ℝ)/32) 15 ≤ 4.4182106 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (((34:ℤ):ℝ)/32))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (((34:ℤ):ℝ)/32) 1 0 (pw1_hi (((34:ℤ):ℝ)/32)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (((34:ℤ):ℝ)/32) 0.4788016403493 0.6931471808 (pwh_2_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (lg_2).2 0.23004169133414 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (((34:ℤ):ℝ)/32) 0.3112136713064 1.098612288908165 (pwh_3_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (lg_3).2 0.37561901733808 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (((34:ℤ):ℝ)/32) 0.2292510108012 1.3862943616 (pwh_4_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (lg_4).2 0.44057735663809 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (((34:ℤ):ℝ)/32) 0.1808607678805 1.60943791291421 (pwh_5_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 0.46848190996826 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (((34:ℤ):ℝ)/32) 0.1490096163206 1.791759469708165 (pwh_6_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (lg_6).2 0.47838076985091 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (((34:ℤ):ℝ)/32) 0.126497904854 1.945910149535424 (pwh_7_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (lg_7).2 0.47899270481397 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (((34:ℤ):ℝ)/32) 0.1097657600234 2.0794415424 (pwh_8_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (lg_8).2 0.47463561238314 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (((34:ℤ):ℝ)/32) 0.096853949208 2.19722457781633 (pwh_9_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (lg_9).2 0.46759109359311 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (((34:ℤ):ℝ)/32) 0.0865964323361 2.30258509371421 (pwh_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (lg_10).2 0.45912546126414 (by norm_num))
  exact mainRemConst_le 10 (by norm_num) (((34:ℤ):ℝ)/32) 15 (by norm_num) _ 0.0865964323361 2.30258509371421 4.4182106 c10 (pwh_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (lg_10).2 (by norm_num)
lemma pc_b2top_1 : ∀ x ∈ Set.Icc (((34:ℤ):ℝ)/32) (((46:ℤ):ℝ)/32), 0 < (I ^ ((0):ℤ) * riemannZeta ((x:ℂ) + ((15:ℝ):ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine horizontal_piece 10 (by norm_num) (15:ℝ) (((34:ℤ):ℝ)/32) (((46:ℤ):ℝ)/32) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.30258509371421 (lg_10).2 (by norm_num) 15 (by norm_num) (by norm_num) 4.4182106 rb_b2top_1 0.0865964323361 15.068723 15.196757 (pwh_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0.484739988549 0.629130140473 (by rw [hrot]; exact bv_b2top_1p0625_0_10) (by rw [hrot]; exact bv_b2top_1p4375_0_10) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2top_1p4375_0_5 : (0.649586118076:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((46:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((46:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (((46:ℤ):ℝ)/32)) (pw1_hi (((46:ℤ):ℝ)/32)) 1 0 0 (cs_one (15:ℝ)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.3692065364848 0.3692065364849 (pwl_2_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_2_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.5632935954295) 0.826256815608 0.00000010987 cs_h15_2 (-0.20797171795738) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.2061285728248 0.2061285728249 (pwl_3_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_3_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.7170601161939) 0.6970113268357 0.0000001121 cs_h15_3 (-0.14780660148772) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1363134665831 0.1363134665832 (pwl_4_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_4_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.3654006440121) (-0.9308503474528) 0.00000011255 cs_h15_4 (-0.04980904381911) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0989078174865 0.0989078174866 (pwl_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) 0.5477092431889 0.8366687426487 0.00000015002 cs_h15_5 0.05417271102284 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((46:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0989078174865 0.0989078174866 (pwl_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) 0.5477092431889 0.8366687426487 0.00000015002 cs_h15_5 225.19140625 (by norm_num) (by norm_num) (-0.01011821252958) (-0.00100077031816) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.64858534775863:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((46:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b2top_2_0_5 : (0.779210762387:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((64:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((64:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((64:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (((64:ℤ):ℝ)/32)) (pw1_hi (((64:ℤ):ℝ)/32)) 1 0 0 (cs_one (15:ℝ)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((64:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_2_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (-0.5632935954295) 0.826256815608 0.00000010987 cs_h15_2 (-0.14082342632488) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((64:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_3_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (-0.7170601161939) 0.6970113268357 0.0000001121 cs_h15_3 (-0.07967335869939) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((64:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_4_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (-0.3654006440121) (-0.9308503474528) 0.00000011255 cs_h15_4 (-0.02283754728514) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((64:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_5_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) 0.5477092431889 0.8366687426487 0.00000015002 cs_h15_5 0.02190836372675 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((64:ℤ):ℝ)/32) (15:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_5_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) 0.5477092431889 0.8366687426487 0.00000015002 cs_h15_5 226 (by norm_num) (by norm_num) (-0.0159182742504) (-0.00063673097001) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.77857403141734:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((64:ℤ):ℝ)/32):ℝ)):ℂ) + ((((15:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2top_2 : mainRemConst 5 (((46:ℤ):ℝ)/32) 15 ≤ 1.16152587 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (((46:ℤ):ℝ)/32))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (((46:ℤ):ℝ)/32) 1 0 (pw1_hi (((46:ℤ):ℝ)/32)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (((46:ℤ):ℝ)/32) 0.3692065364849 0.6931471808 (pwh_2_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (lg_2).2 0.17738639333534 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (((46:ℤ):ℝ)/32) 0.2061285728249 1.098612288908165 (pwh_3_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (lg_3).2 0.24878666687352 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (((46:ℤ):ℝ)/32) 0.1363134665832 1.3862943616 (pwh_4_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (lg_4).2 0.2619688636116 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (((46:ℤ):ℝ)/32) 0.0989078174866 1.60943791291421 (pwh_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 0.25619996967795 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (((46:ℤ):ℝ)/32) 15 (by norm_num) _ 0.0989078174866 1.60943791291421 1.16152587 c5 (pwh_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2top_2 : ∀ x ∈ Set.Icc (((46:ℤ):ℝ)/32) (((64:ℤ):ℝ)/32), 0 < (I ^ ((0):ℤ) * riemannZeta ((x:ℂ) + ((15:ℝ):ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine horizontal_piece 5 (by norm_num) (15:ℝ) (((46:ℤ):ℝ)/32) (((64:ℤ):ℝ)/32) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 15 (by norm_num) (by norm_num) 1.16152587 rb_b2top_2 0.0989078174866 15.132746 15.297059 (pwh_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0.649586118076 0.779210762387 (by rw [hrot]; exact bv_b2top_1p4375_0_5) (by rw [hrot]; exact bv_b2top_2_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)

def xL_b2top : List ℤ := [24, 34, 46, 64]
def zL_b2top : List ℤ := [-1, 0, 0]
noncomputable def xF_b2top (k : ℕ) : ℝ := ((xL_b2top.getD k 0 : ℤ) : ℝ) / 32
def zF_b2top (k : ℕ) : ℤ := zL_b2top.getD k 0

theorem side_b2top : ∫ t in (1 - 1/4:ℝ)..(2:ℝ), logDeriv zetaFactor ((t:ℂ) + ((15:ℝ):ℂ) * I) =
    log (I ^ ((-3):ℤ) * I ^ ((0):ℤ) * zetaFactor ((((2:ℝ)):ℂ) + ((15:ℝ):ℂ) * I)) -
      log (I ^ ((-3):ℤ) * I ^ ((-1):ℤ) * zetaFactor ((((1 - 1/4:ℝ)):ℂ) + ((15:ℝ):ℂ) * I)) -
      ((((0) - (-1) : ℤ)) : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  have h := horizontal_side (15:ℝ) (by norm_num) xF_b2top zF_b2top (-3) 2 (list_mono xL_b2top 32 (by norm_num) 3 (by decide)) (by decide) (fun t _ => u1_top t)
    (fun k hk => by interval_cases k; exacts [pc_b2top_0, pc_b2top_1, pc_b2top_2])
  have e0 : xF_b2top 0 = 1 - 1/4 := by norm_num [xF_b2top, xL_b2top]
  have e1 : xF_b2top (2 + 1) = 2 := by norm_num [xF_b2top, xL_b2top]
  have f0 : zF_b2top 0 = -1 := rfl
  have f1 : zF_b2top 2 = 0 := rfl
  rw [e0, e1, f0, f1] at h
  exact h

theorem nz_b2top : ∀ t ∈ Set.Icc (1 - 1/4:ℝ) (2:ℝ), riemannZeta ((t:ℂ) + ((15:ℝ):ℂ) * I) ≠ 0 := by
  have h := cover xF_b2top (fun t => riemannZeta ((t:ℂ) + ((15:ℝ):ℂ) * I) ≠ 0) 2 (list_mono xL_b2top 32 (by norm_num) 3 (by decide))
    (fun k hk t ht => by interval_cases k; exacts [zeta_ne_of_re_pos (pc_b2top_0 t ht), zeta_ne_of_re_pos (pc_b2top_1 t ht), zeta_ne_of_re_pos (pc_b2top_2 t ht)])
  have e0 : xF_b2top 0 = 1 - 1/4 := by norm_num [xF_b2top, xL_b2top]
  have e1 : xF_b2top (2 + 1) = 2 := by norm_num [xF_b2top, xL_b2top]
  rw [e0, e1] at h
  exact h

end Cert
end ZB
end RHV6Fresh
