/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Side_b2left_trig0
import RHV6Fresh.Terminal.ZetaBox22.Side_b2left_trig1
/-!
# Certificat (V2), côté b2left (b2), morceaux 3

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
lemma bv_b2left_21p528_0_15_c3 : (0.415899688801:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((21528:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((21528:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((21528:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7067583815438) (-0.7074550092357) 0.00000011688 cs_b2left_v21p528_2 (-0.42024111745714) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.0888630559381 0.9960438530955 0.00000012691 cs_b2left_v21p528_3 0.0389833972029 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0009851730458) 0.9999995147168 0.00000014092 cs_b2left_v21p528_4 (-0.00034836109341) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9959112694076) 0.0903368306608 0.00000014615 cs_b2left_v21p528_5 (-0.29784698429173) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.6418515037107 (-0.7668289556246) 0.00000012081 cs_b2left_v21p528_6 0.16742528367942 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4968342930445) 0.8678454270484 0.00000014896 cs_b2left_v21p528_7 (-0.11544846548699) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7081509452412 (-0.7060610729632) 0.00000015778 cs_b2left_v21p528_8 0.14887036465878 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9842067144301) 0.1770230010957 0.00000015381 cs_b2left_v21p528_9 (-0.1894107001056) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7677778806255 0.640716104076 0.00000014006 cs_b2left_v21p528_10 0.13653233475331 (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2127507752509 (-0.9771064975887) 0.00000014144 cs_b2left_v21p528_11 0.03522300048143 (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9961309149905) 0.0878817370253 0.00000012478 cs_b2left_v21p528_12 (-0.15450073098553) (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2380506675827 0.9712527372746 0.00000011833 cs_b2left_v21p528_13 0.0347705590651 (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9651033954718 (-0.2618691200749) 0.00000014286 cs_b2left_v21p528_14 0.13334531220319 (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1784792553109) (-0.983943674924) 0.00000015209 cs_b2left_v21p528_15 (-0.02341637535324) (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1784792553109) (-0.983943674924) 0.00000015209 cs_b2left_v21p528_15 463.517284 (by norm_num) (by norm_num) 0.59480364359926 0.07803782846897 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.49393751727049:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((21528:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma bv_b2left_21p764_0_15_c3 : (0.568704390595:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((21764:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((21764:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((21764:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8125352297438) (-0.5829120863139) 0.00000012859 cs_b2left_v21p764_2 (-0.48313641466096) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3412561320868 0.9399703465074 0.00000012709 cs_b2left_v21p764_3 0.14970605331341 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3204270059887 0.9472732097094 0.00000014998 cs_b2left_v21p764_4 0.11328800137899 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8914380222289) 0.4531426402553 0.00000012819 cs_b2left_v21p764_5 (-0.26660219035266) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2706374460937 (-0.9626813453952) 0.00000015567 cs_b2left_v21p764_6 0.07059504167248 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0606750825222) 0.998157569906 0.00000014425 cs_b2left_v21p764_7 (-0.01409898596335) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2918186764315 (-0.9564736588562) 0.00000015412 cs_b2left_v21p764_8 0.06134728732908 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7670885046194) 0.6415412894291 0.00000015417 cs_b2left_v21p764_9 (-0.14762628121481) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.988467120106 0.1514356380427 0.00000012217 cs_b2left_v21p764_10 0.17577705099316 (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3443195990486) (-0.938852498377) 0.00000015724 cs_b2left_v21p764_11 (-0.0570055878297) (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7810609840343) 0.6244547535065 0.00000015562 cs_b2left_v21p764_12 (-0.12114321530306) (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.748426538861 0.663217698745 0.00000016581 cs_b2left_v21p764_13 0.10931797255559 (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.6311386761248 (-0.7756700145677) 0.00000015986 cs_b2left_v21p764_14 0.08720244416028 (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7301493311937) (-0.6832876071816) 0.00000012786 cs_b2left_v21p764_15 (-0.09579510625986) (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7301493311937) (-0.6832876071816) 0.00000012786 cs_b2left_v21p764_15 473.734196 (by norm_num) (by norm_num) 0.10001332386087 0.01312167922315 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.58182606981859:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((21764:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma rb_b2left_60 : mainRemConst 15 (1 - 1/4:ℝ) 21.529451 ≤ 12.72573362 := by
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
  have c11 := sum_ub_step c10 (remTerm_ub 11 (by norm_num) (1 - 1/4:ℝ) 0.1655600260762 2.397895273518535 (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_11).2 0.95195388246736 (by norm_num))
  have c12 := sum_ub_step c11 (remTerm_ub 12 (by norm_num) (1 - 1/4:ℝ) 0.1551008098504 2.484906650508165 (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_12).2 0.95771044130855 (by norm_num))
  have c13 := sum_ub_step c12 (remTerm_ub 13 (by norm_num) (1 - 1/4:ℝ) 0.1460637632397 2.564949358181702 (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_13).2 0.96094841680103 (by norm_num))
  have c14 := sum_ub_step c13 (remTerm_ub 14 (by norm_num) (1 - 1/4:ℝ) 0.138166887162 2.639057330335424 (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_14).2 0.96228036207181 (by norm_num))
  have c15 := sum_ub_step c14 (remTerm_ub 15 (by norm_num) (1 - 1/4:ℝ) 0.1311993114177 2.708050201822375 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 0.96215485975843 (by norm_num))
  exact mainRemConst_le 15 (by norm_num) (1 - 1/4:ℝ) 21.529451 (by norm_num) _ 0.1311993114177 2.708050201822375 12.72573362 c15 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 (by norm_num)
lemma pc_b2left_60 : ∀ y ∈ Set.Icc (((21528:ℤ):ℝ)/1000) (((21764:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 15 (by norm_num) (1 - 1/4:ℝ) (((21528:ℤ):ℝ)/1000) (((21764:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.708050201822375 (lg_15).2 (by norm_num) 21.529451 21.528 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 12.72573362 rb_b2left_60 0.1311993114177 21.776919 21.834244 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.415899688801 0.568704390595 (by rw [hrot]; exact bv_b2left_21p528_0_15_c3) (by rw [hrot]; exact bv_b2left_21p764_0_15_c3) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_22_0_15_c3 : (0.743333459409:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((22000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((22000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((22000:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8966176905623) (-0.4428055068064) 0.00000014777 cs_b2left_v22_2 (-0.53313215639161) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5708374291683 0.8210631093044 0.00000012728 cs_b2left_v22_3 0.25042137954635 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.6078464924715 0.7940545583208 0.00000011932 cs_b2left_v22_4 0.21490614618749 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6598968542787) 0.7513562016082 0.00000014105 cs_b2left_v22_5 (-0.19735523353931) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1482516711606) (-0.9889496660586) 0.00000013151 cs_b2left_v22_6 (-0.03867110172132) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3880569826655 0.9216353824613 0.00000013954 cs_b2left_v22_7 0.09017202366203 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1933941871387) (-0.981121138484) 0.00000015047 cs_b2left_v22_8 (-0.0406561513064) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3482892589212) 0.9373871089991 0.00000015454 cs_b2left_v22_9 (-0.06702832887259) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9243798572116 (-0.3814733012695) 0.00000012874 cs_b2left_v22_10 0.16438054381975 (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7940342395077) (-0.6078730348044) 0.00000015999 cs_b2left_v22_11 (-0.13146035588624) (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3049873755209) 0.9523563937787 0.00000014658 cs_b2left_v22_12 (-0.04730381167212) (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9928347214733 0.1194956728799 0.00000011763 cs_b2left_v22_13 0.14501715851184 (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.0601664670608 (-0.9981883570956) 0.00000013025 cs_b2left_v22_14 0.00831299546908 (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.993604693187) (-0.1129146280329) 0.00000015754 cs_b2left_v22_15 (-0.13036027223667) (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((22000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.993604693187) (-0.1129146280329) 0.00000015754 cs_b2left_v22_15 484.0625 (by norm_num) (by norm_num) (-0.42752224255738) (-0.05609062383923) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.68724283557028:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((22000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma rb_b2left_61 : mainRemConst 15 (1 - 1/4:ℝ) 21.765435 ≤ 12.71821125 := by
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
  have c11 := sum_ub_step c10 (remTerm_ub 11 (by norm_num) (1 - 1/4:ℝ) 0.1655600260762 2.397895273518535 (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_11).2 0.95195388246736 (by norm_num))
  have c12 := sum_ub_step c11 (remTerm_ub 12 (by norm_num) (1 - 1/4:ℝ) 0.1551008098504 2.484906650508165 (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_12).2 0.95771044130855 (by norm_num))
  have c13 := sum_ub_step c12 (remTerm_ub 13 (by norm_num) (1 - 1/4:ℝ) 0.1460637632397 2.564949358181702 (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_13).2 0.96094841680103 (by norm_num))
  have c14 := sum_ub_step c13 (remTerm_ub 14 (by norm_num) (1 - 1/4:ℝ) 0.138166887162 2.639057330335424 (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_14).2 0.96228036207181 (by norm_num))
  have c15 := sum_ub_step c14 (remTerm_ub 15 (by norm_num) (1 - 1/4:ℝ) 0.1311993114177 2.708050201822375 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 0.96215485975843 (by norm_num))
  exact mainRemConst_le 15 (by norm_num) (1 - 1/4:ℝ) 21.765435 (by norm_num) _ 0.1311993114177 2.708050201822375 12.71821125 c15 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 (by norm_num)
lemma pc_b2left_61 : ∀ y ∈ Set.Icc (((21764:ℤ):ℝ)/1000) (((22000:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 15 (by norm_num) (1 - 1/4:ℝ) (((21764:ℤ):ℝ)/1000) (((22000:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.708050201822375 (lg_15).2 (by norm_num) 21.765435 21.764 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 12.71821125 rb_b2left_61 0.1311993114177 22.012781 22.069493 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.568704390595 0.743333459409 (by rw [hrot]; exact bv_b2left_21p764_0_15_c3) (by rw [hrot]; exact bv_b2left_22_0_15_c3) (by rw [lt_min_iff]; constructor <;> norm_num)

end H22
end Cert
end ZB
end RHV6Fresh
