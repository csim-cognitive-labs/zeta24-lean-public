/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Side_b2top_trig0
/-!
# Certificat (V2), côté b2top (b2), morceaux 0

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
lemma bv_b2top_0p75_0_10_c0 : (0.72916701026:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((((24:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((24:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((24:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (((24:ℤ):ℝ)/32)) (pw1_hi (((24:ℤ):ℝ)/32)) 1 0 0 (cs_one (22:ℝ)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((24:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_2_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.8966176905623) (-0.4428055068064) 0.00000014777 cs_h22_2 (-0.53313215639161) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((24:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_3_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) 0.5708374291683 0.8210631093044 0.00000012728 cs_h22_3 0.25042137954635 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((24:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_4_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) 0.6078464924715 0.7940545583208 0.00000011932 cs_h22_4 0.21490614618749 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((24:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_5_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.6598968542787) 0.7513562016082 0.00000014105 cs_h22_5 (-0.19735523353931) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (((24:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_6_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.1482516711606) (-0.9889496660586) 0.00000013151 cs_h22_6 (-0.03867110172132) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (((24:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_7_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) 0.3880569826655 0.9216353824613 0.00000013954 cs_h22_7 0.09017202366203 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (((24:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_8_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.1933941871387) (-0.981121138484) 0.00000015047 cs_h22_8 (-0.0406561513064) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (((24:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_9_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (-0.3482892589212) 0.9373871089991 0.00000015454 cs_h22_9 (-0.06702832887259) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (((24:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_10_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) 0.9243798572116 (-0.3814733012695) 0.00000012874 cs_h22_10 0.16438054381975 (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (((24:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (pwh_10_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) 0.9243798572116 (-0.3814733012695) 0.00000012874 cs_h22_10 484.0625 (by norm_num) (by norm_num) 0.64033869188756 0.1138701111235 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.84303712138439:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((24:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma bv_b2top_1p0625_0_10_c0 : (0.765498258139:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((((34:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((34:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((34:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (((34:ℤ):ℝ)/32)) (pw1_hi (((34:ℤ):ℝ)/32)) 1 0 0 (cs_one (22:ℝ)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((34:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.4788016403492 0.4788016403493 (pwl_2_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_2_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.8966176905623) (-0.4428055068064) 0.00000014777 cs_h22_2 (-0.42930209175995) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((34:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.3112136713063 0.3112136713064 (pwl_3_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_3_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) 0.5708374291683 0.8210631093044 0.00000012728 cs_h22_3 0.17765237243924 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((34:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.2292510108011 0.2292510108012 (pwl_4_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_4_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) 0.6078464924715 0.7940545583208 0.00000011932 cs_h22_4 0.13934939545676 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((34:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1808607678804 0.1808607678805 (pwl_5_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_5_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.6598968542787) 0.7513562016082 0.00000014105 cs_h22_5 (-0.11934947729719) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (((34:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1490096163205 0.1490096163206 (pwl_6_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_6_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.1482516711606) (-0.9889496660586) 0.00000013151 cs_h22_6 (-0.02209094423479) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (((34:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1264979048539 0.126497904854 (pwl_7_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_7_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) 0.3880569826655 0.9216353824613 0.00000013954 cs_h22_7 0.04908837761959 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (((34:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1097657600233 0.1097657600234 (pwl_8_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_8_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.1933941871387) (-0.981121138484) 0.00000015047 cs_h22_8 (-0.02122807645185) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (((34:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0968539492079 0.096853949208 (pwl_9_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_9_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (-0.3482892589212) 0.9373871089991 0.00000015454 cs_h22_9 (-0.03373320516106) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (((34:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.086596432336 0.0865964323361 (pwl_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) 0.9243798572116 (-0.3814733012695) 0.00000012874 cs_h22_10 0.08004798660936 (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (((34:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.086596432336 0.0865964323361 (pwl_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (pwh_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) 0.9243798572116 (-0.3814733012695) 0.00000012874 cs_h22_10 484.00390625 (by norm_num) (by norm_num) 0.63439194431258 0.05493607908024 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.82043433722011:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((34:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma rb_b2top_0 : mainRemConst 10 (((24:ℤ):ℝ)/32) 22 ≤ 7.6761576 := by
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
  exact mainRemConst_le 10 (by norm_num) (((24:ℤ):ℝ)/32) 22 (by norm_num) _ 0.1778279410039 2.30258509371421 7.6761576 c10 (pwh_10_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (lg_10).2 (by norm_num)
lemma pc_b2top_0 : ∀ x ∈ Set.Icc (((24:ℤ):ℝ)/32) (((34:ℤ):ℝ)/32), 0 < (I ^ ((0):ℤ) * riemannZeta ((x:ℂ) + ((22:ℝ):ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine horizontal_piece 10 (by norm_num) (22:ℝ) (((24:ℤ):ℝ)/32) (((34:ℤ):ℝ)/32) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.30258509371421 (lg_10).2 (by norm_num) 22 (by norm_num) (by norm_num) 7.6761576 rb_b2top_0 0.1778279410039 22.025643 22.096469 (pwh_10_24_32 (((24:ℤ):ℝ)/32) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0.72916701026 0.765498258139 (by rw [hrot]; exact bv_b2top_0p75_0_10_c0) (by rw [hrot]; exact bv_b2top_1p0625_0_10_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2top_1p4375_0_10_c0 : (0.80291956479:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((((46:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((46:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (((46:ℤ):ℝ)/32)) (pw1_hi (((46:ℤ):ℝ)/32)) 1 0 0 (cs_one (22:ℝ)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.3692065364848 0.3692065364849 (pwl_2_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_2_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.8966176905623) (-0.4428055068064) 0.00000014777 cs_h22_2 (-0.33103716664125) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.2061285728248 0.2061285728249 (pwl_3_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_3_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) 0.5708374291683 0.8210631093044 0.00000012728 cs_h22_3 0.11766587835339 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1363134665831 0.1363134665832 (pwl_4_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_4_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) 0.6078464924715 0.7940545583208 0.00000011932 cs_h22_4 0.08285764627424 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0989078174865 0.0989078174866 (pwl_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.6598968542787) 0.7513562016082 0.00000014105 cs_h22_5 (-0.06526897157393) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0761040164432 0.0761040164433 (pwl_6_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_6_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.1482516711606) (-0.9889496660586) 0.00000013151 cs_h22_6 (-0.0112825576282) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0609777741581 0.0609777741582 (pwl_7_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_7_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) 0.3880569826655 0.9216353824613 0.00000013954 cs_h22_7 0.02366284254061 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0503278228734 0.0503278228735 (pwl_8_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_8_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.1933941871387) (-0.981121138484) 0.00000015047 cs_h22_8 (-0.00973311596791) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0424889885348 0.0424889885349 (pwl_9_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_9_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.3482892589212) 0.9373871089991 0.00000015454 cs_h22_9 (-0.01479846489538) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0365174127254 0.0365174127255 (pwl_10_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_10_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) 0.9243798572116 (-0.3814733012695) 0.00000012874 cs_h22_10 0.03375595605959 (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0365174127254 0.0365174127255 (pwl_10_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_10_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) 0.9243798572116 (-0.3814733012695) 0.00000012874 cs_h22_10 484.19140625 (by norm_num) (by norm_num) 0.62716605643429 0.02290248173024 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.82582204652116:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((46:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma rb_b2top_1 : mainRemConst 10 (((34:ℤ):ℝ)/32) 22 ≤ 4.31590282 := by
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
  exact mainRemConst_le 10 (by norm_num) (((34:ℤ):ℝ)/32) 22 (by norm_num) _ 0.0865964323361 2.30258509371421 4.31590282 c10 (pwh_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (lg_10).2 (by norm_num)
lemma pc_b2top_1 : ∀ x ∈ Set.Icc (((34:ℤ):ℝ)/32) (((46:ℤ):ℝ)/32), 0 < (I ^ ((0):ℤ) * riemannZeta ((x:ℂ) + ((22:ℝ):ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine horizontal_piece 10 (by norm_num) (22:ℝ) (((34:ℤ):ℝ)/32) (((46:ℤ):ℝ)/32) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.30258509371421 (lg_10).2 (by norm_num) 22 (by norm_num) (by norm_num) 4.31590282 rb_b2top_1 0.0865964323361 22.046914 22.134621 (pwh_10_34_32 (((34:ℤ):ℝ)/32) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0.765498258139 0.80291956479 (by rw [hrot]; exact bv_b2top_1p0625_0_10_c0) (by rw [hrot]; exact bv_b2top_1p4375_0_10_c0) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2top_1p4375_0_5_c0 : (0.853440076819:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((46:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((46:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (((46:ℤ):ℝ)/32)) (pw1_hi (((46:ℤ):ℝ)/32)) 1 0 0 (cs_one (22:ℝ)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.3692065364848 0.3692065364849 (pwl_2_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_2_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.8966176905623) (-0.4428055068064) 0.00000014777 cs_h22_2 (-0.33103716664125) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.2061285728248 0.2061285728249 (pwl_3_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_3_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) 0.5708374291683 0.8210631093044 0.00000012728 cs_h22_3 0.11766587835339 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1363134665831 0.1363134665832 (pwl_4_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_4_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) 0.6078464924715 0.7940545583208 0.00000011932 cs_h22_4 0.08285764627424 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0989078174865 0.0989078174866 (pwl_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.6598968542787) 0.7513562016082 0.00000014105 cs_h22_5 (-0.06526897157393) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((46:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0989078174865 0.0989078174866 (pwl_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (pwh_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (-0.6598968542787) 0.7513562016082 0.00000014105 cs_h22_5 484.19140625 (by norm_num) (by norm_num) (-0.49766228452178) (-0.04922269040739) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.80421738641245:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((46:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b2top_2_0_5_c0 : (0.870608663827:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((((64:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((64:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (((64:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (((64:ℤ):ℝ)/32)) (pw1_hi (((64:ℤ):ℝ)/32)) 1 0 0 (cs_one (22:ℝ)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (((64:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_2_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (-0.8966176905623) (-0.4428055068064) 0.00000014777 cs_h22_2 (-0.22415445958308) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (((64:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_3_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) 0.5708374291683 0.8210631093044 0.00000012728 cs_h22_3 0.06342636687647 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (((64:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_4_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) 0.6078464924715 0.7940545583208 0.00000011932 cs_h22_4 0.03799039832196 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (((64:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_5_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (-0.6598968542787) 0.7513562016082 0.00000014105 cs_h22_5 (-0.02639587981315) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (((64:ℤ):ℝ)/32) (22:ℝ) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (pwh_5_64_32 (((64:ℤ):ℝ)/32) (by norm_num)) (-0.6598968542787) 0.7513562016082 0.00000014105 cs_h22_5 485 (by norm_num) (by norm_num) (-0.49355595062519) (-0.019742238025) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.8508664258022:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((((64:ℤ):ℝ)/32):ℝ)):ℂ) + ((((22:ℝ):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2top_2 : mainRemConst 5 (((46:ℤ):ℝ)/32) 22 ≤ 1.13236008 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (((46:ℤ):ℝ)/32))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (((46:ℤ):ℝ)/32) 1 0 (pw1_hi (((46:ℤ):ℝ)/32)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (((46:ℤ):ℝ)/32) 0.3692065364849 0.6931471808 (pwh_2_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (lg_2).2 0.17738639333534 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (((46:ℤ):ℝ)/32) 0.2061285728249 1.098612288908165 (pwh_3_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (lg_3).2 0.24878666687352 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (((46:ℤ):ℝ)/32) 0.1363134665832 1.3862943616 (pwh_4_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (lg_4).2 0.2619688636116 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (((46:ℤ):ℝ)/32) 0.0989078174866 1.60943791291421 (pwh_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 0.25619996967795 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (((46:ℤ):ℝ)/32) 22 (by norm_num) _ 0.0989078174866 1.60943791291421 1.13236008 c5 (pwh_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2top_2 : ∀ x ∈ Set.Icc (((46:ℤ):ℝ)/32) (((64:ℤ):ℝ)/32), 0 < (I ^ ((0):ℤ) * riemannZeta ((x:ℂ) + ((22:ℝ):ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine horizontal_piece 5 (by norm_num) (22:ℝ) (((46:ℤ):ℝ)/32) (((64:ℤ):ℝ)/32) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 22 (by norm_num) (by norm_num) 1.13236008 rb_b2top_2 0.0989078174866 22.090723 22.203604 (pwh_5_46_32 (((46:ℤ):ℝ)/32) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0.853440076819 0.870608663827 (by rw [hrot]; exact bv_b2top_1p4375_0_5_c0) (by rw [hrot]; exact bv_b2top_2_0_5_c0) (by rw [lt_min_iff]; constructor <;> norm_num)

end H22
end Cert
end ZB
end RHV6Fresh
