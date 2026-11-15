/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Side_b2left_trig0
import RHV6Fresh.Terminal.ZetaBox28.Side_b2left_trig1
import RHV6Fresh.Terminal.ZetaBox28.Side_b2left_trig2
/-!
# Certificat (V2), côté b2left (b2), morceaux 4

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
lemma bv_b2left_26p737_0_10_c4 : (1.694141003973:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((26737:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((26737:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((26737:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((26737:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((26737:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.950212306365 0.311603229817 0.00000015153 cs_b2left_v26p737_2 0.56499952764586 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((26737:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4542529484337) 0.8908727512022 0.00000013265 cs_b2left_v26p737_3 (-0.19927689177266) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((26737:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.805806913553 0.5921783667698 0.00000012373 cs_b2left_v26p737_4 0.28489572270494 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((26737:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5810682253309 0.8138548503946 0.00000012735 cs_b2left_v26p737_5 0.17377989442442 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((26737:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.709235497935) 0.7049716366235 0.0000001426 cs_b2left_v26p737_6 (-0.18500229410669) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((26737:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1903521799088) (-0.9817158690798) 0.00000011606 cs_b2left_v26p737_7 (-0.04423179758405) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((26737:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5811629540989 0.8137872085399 0.00000015455 cs_b2left_v26p737_8 0.12217442870485 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((26737:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5873085928033) (-0.8093630933075) 0.00000015429 cs_b2left_v26p737_9 (-0.11302762107727) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((26737:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2985384740017 0.9543976003431 0.00000016128 cs_b2left_v26p737_10 0.05308845346204 (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1 - 1/4:ℝ) (((26737:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2985384740017 0.9543976003431 0.00000016128 cs_b2left_v26p737_10 714.929669 (by norm_num) (by norm_num) (-0.20661309670905) (-0.03674158157218) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.65739942240144:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((26737:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma bv_b2left_27p158_0_10_c4 : (2.146654265605:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((27158:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((27158:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((27158:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((27158:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((27158:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9996858943456 0.0250621756132 0.00000011464 cs_b2left_v27p158_2 0.59441672099641 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((27158:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0090175509885) 0.9999593410604 0.00000010732 cs_b2left_v27p158_3 (-0.00395596858584) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((27158:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9987437747071 0.0501086068843 0.00000012927 cs_b2left_v27p158_4 0.35310920217769 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((27158:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9629171982817 0.2697970890378 0.00000013851 cs_b2left_v27p158_5 0.2879793703493 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((27158:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0340758751365) 0.9994192487307 0.00000012091 cs_b2left_v27p158_6 (-0.00888863599384) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((27158:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8472300095952) (-0.5312262331334) 0.00000014353 cs_b2left_v27p158_7 (-0.19686924420535) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((27158:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9971742329346 0.0751235593619 0.0000001439 cs_b2left_v27p158_8 0.20963002921324 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((27158:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.999837367102) (-0.0180343755785) 0.00000011973 cs_b2left_v27p158_9 (-0.19241881405614) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((27158:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9558530385196 0.2938451441709 0.00000013746 cs_b2left_v27p158_10 0.16997735329793 (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1 - 1/4:ℝ) (((27158:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9558530385196 0.2938451441709 0.00000013746 cs_b2left_v27p158_10 737.619464 (by norm_num) (by norm_num) 0.37297708792808 0.06632574758789 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.2129800131934:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((27158:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma rb_b2left_80 : mainRemConst 10 (1 - 1/4:ℝ) 26.738168 ≤ 7.597408 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  exact mainRemConst_le 10 (by norm_num) (1 - 1/4:ℝ) 26.738168 (by norm_num) _ 0.1778279410039 2.30258509371421 7.597408 c10 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 (by norm_num)
lemma pc_b2left_80 : ∀ y ∈ Set.Icc (((26737:ℤ):ℝ)/1000) (((27158:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 10 (by norm_num) (1 - 1/4:ℝ) (((26737:ℤ):ℝ)/1000) (((27158:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.30258509371421 (lg_10).2 (by norm_num) 26.738168 26.737 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 7.597408 rb_b2left_80 0.1778279410039 27.168355 27.214325 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.694141003973 2.146654265605 (by rw [hrot]; exact bv_b2left_26p737_0_10_c4) (by rw [hrot]; exact bv_b2left_27p158_0_10_c4) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_27p579_0_10_c4 : (2.349510803889:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((27579:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((27579:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((27579:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((27579:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((27579:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9646326293789 (-0.2635979710421) 0.00000013606 cs_b2left_v27p579_2 0.57357391220876 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((27579:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.438112744513 0.8989200315352 0.0000001339 cs_b2left_v27p579_3 0.1921962071915 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((27579:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.86103227018 (-0.5085503217073) 0.0000001555 cs_b2left_v27p579_4 0.30442082355474 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((27579:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9193421841372 (-0.3934589539785) 0.00000015002 cs_b2left_v27p579_5 0.27494739804847 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((27579:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.6595712699816 0.751642029037 0.00000015766 cs_b2left_v27p579_6 0.17204742955937 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((27579:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9666002403995) 0.2562888507181 0.00000014944 cs_b2left_v27p579_7 (-0.22460707694876) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((27579:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.696526989789 (-0.7175305934213) 0.00000013325 cs_b2left_v27p579_8 0.14642673419787 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((27579:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6161145249551) 0.7876565826082 0.00000015982 cs_b2left_v27p579_9 (-0.11857132636888) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((27579:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7831124864262 (-0.6218800797609) 0.00000012776 cs_b2left_v27p579_10 0.13925925831623 (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1 - 1/4:ℝ) (((27579:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7831124864262 (-0.6218800797609) 0.00000012776 cs_b2left_v27p579_10 760.663741 (by norm_num) (by norm_num) 0.61960204480581 0.11018255586963 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.4596933597593:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((27579:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma rb_b2left_81 : mainRemConst 10 (1 - 1/4:ℝ) 27.15915 ≤ 7.59176184 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  exact mainRemConst_le 10 (by norm_num) (1 - 1/4:ℝ) 27.15915 (by norm_num) _ 0.1778279410039 2.30258509371421 7.59176184 c10 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 (by norm_num)
lemma pc_b2left_81 : ∀ y ∈ Set.Icc (((27158:ℤ):ℝ)/1000) (((27579:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 10 (by norm_num) (1 - 1/4:ℝ) (((27158:ℤ):ℝ)/1000) (((27579:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.30258509371421 (lg_10).2 (by norm_num) 27.15915 27.158 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 7.59176184 rb_b2left_81 0.1778279410039 27.589197 27.634467 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 2.146654265605 2.349510803889 (by rw [hrot]; exact bv_b2left_27p158_0_10_c4) (by rw [hrot]; exact bv_b2left_27p579_0_10_c4) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_28_0_10_c4 : (2.255565134165:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((28000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((28000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((28000:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8480164376045 (-0.5299699251396) 0.00000014088 cs_b2left_v28_2 0.50423350685146 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.793180401478 0.6089867409979 0.00000015355 cs_b2left_v28_3 0.34796130396172 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4382636670103 (-0.8988464597353) 0.00000014629 cs_b2left_v28_4 0.15494955372397 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4695949379756 (-0.8828819820495) 0.00000011667 cs_b2left_v28_5 0.1404416087414 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9953746855837 0.0960689091184 0.00000013362 cs_b2left_v28_6 0.25964089377927 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4727309146966) 0.8812068328632 0.00000012239 cs_b2left_v28_7 (-0.10984760355891) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1047067973484) (-0.9945031355348) 0.0000001226 cs_b2left_v28_8 (-0.02201191840923) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2582703951848 0.9660726696119 0.00000012095 cs_b2left_v28_9 0.04970413745102 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0696766715148) (-0.9975696273676) 0.00000015222 cs_b2left_v28_10 (-0.01239048610046) (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1 - 1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0696766715148) (-0.9975696273676) 0.00000015222 cs_b2left_v28_10 784.0625 (by norm_num) (by norm_num) 0.3211860968118 0.05711586227513 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (2.31268099644024:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((28000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma rb_b2left_82 : mainRemConst 10 (1 - 1/4:ℝ) 27.580133 ≤ 7.5862908 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  exact mainRemConst_le 10 (by norm_num) (1 - 1/4:ℝ) 27.580133 (by norm_num) _ 0.1778279410039 2.30258509371421 7.5862908 c10 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 (by norm_num)
lemma pc_b2left_82 : ∀ y ∈ Set.Icc (((27579:ℤ):ℝ)/1000) (((28000:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 10 (by norm_num) (1 - 1/4:ℝ) (((27579:ℤ):ℝ)/1000) (((28000:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.30258509371421 (lg_10).2 (by norm_num) 27.580133 27.579 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 7.5862908 rb_b2left_82 0.1778279410039 28.010043 28.054635 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 2.349510803889 2.255565134165 (by rw [hrot]; exact bv_b2left_27p579_0_10_c4) (by rw [hrot]; exact bv_b2left_28_0_10_c4) (by rw [lt_min_iff]; constructor <;> norm_num)

end H28
end Cert
end ZB
end RHV6Fresh
