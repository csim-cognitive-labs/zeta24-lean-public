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
# Certificat (V2), côté b1left (b1), morceaux 9

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
lemma bv_b1left_27p685_0_15_c9 : (3.50013929767:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1/4:ℝ):ℝ)):ℂ) + ((((((27685:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((27685:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((27685:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.9426800075081 (-0.3336980722816) 0.00000013495 cs_b1left_v27p685_2 0.79269612556592 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.5395908174977 0.8419274016637 0.00000013133 cs_b1left_v27p685_3 0.41000025899539 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.7772912560252 (-0.6291409248386) 0.00000015783 cs_b1left_v27p685_4 0.54962780648972 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.8391969249861 (-0.5438276575294) 0.00000015893 cs_b1left_v27p685_5 0.56120470126756 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6389431042462 0.6389431042463 (pwl_6_1_4 (1/4:ℝ) (by norm_num)) (pwh_6_1_4 (1/4:ℝ) (by norm_num)) 0.7896109654655 0.6136077926629 0.00000016145 cs_b1left_v27p685_6 0.504516378264 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6147881529512 0.6147881529513 (pwl_7_1_4 (1/4:ℝ) (by norm_num)) (pwh_7_1_4 (1/4:ℝ) (by norm_num)) (-0.8936208725939) 0.4488226107887 0.00000012529 cs_b1left_v27p685_7 (-0.54938760272755) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_8_1_4 (1/4:ℝ) (by norm_num)) (pwh_8_1_4 (1/4:ℝ) (by norm_num)) 0.5227938132537 (-0.8524591654875) 0.00000013674 cs_b1left_v27p685_8 0.31085497989422 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5773502691896 0.5773502691897 (pwl_9_1_4 (1/4:ℝ) (by norm_num)) (pwh_9_1_4 (1/4:ℝ) (by norm_num)) (-0.4176834993443) 0.9085925898728 0.00000016265 cs_b1left_v27p685_9 (-0.24114977468855) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5623413251903 0.5623413251904 (pwl_10_1_4 (1/4:ℝ) (by norm_num)) (pwh_10_1_4 (1/4:ℝ) (by norm_num)) 0.6096200018451 (-0.7926937954535) 0.0000001477 cs_b1left_v27p685_10 0.34281443664227 (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5491004867761 0.5491004867762 (pwl_11_1_4 (1/4:ℝ) (by norm_num)) (pwh_11_1_4 (1/4:ℝ) (by norm_num)) (-0.916207665673) 0.4007037724114 0.0000001684 cs_b1left_v27p685_11 (-0.50309016767766) (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5372849659117 0.5372849659118 (pwl_12_1_4 (1/4:ℝ) (by norm_num)) (pwh_12_1_4 (1/4:ℝ) (by norm_num)) 0.9491102084021 0.3149441415662 0.00000014036 cs_b1left_v27p685_12 0.50994257055445 (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5266403878479 0.526640387848 (pwl_13_1_4 (1/4:ℝ) (by norm_num)) (pwh_13_1_4 (1/4:ℝ) (by norm_num)) (-0.3191081356506) (-0.9477183113983) 0.00000013926 cs_b1left_v27p685_13 (-0.16805530566443) (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5169731539571 0.5169731539572 (pwl_14_1_4 (1/4:ℝ) (by norm_num)) (pwh_14_1_4 (1/4:ℝ) (by norm_num)) (-0.6926272908766) 0.7212956646968 0.00000013736 cs_b1left_v27p685_14 (-0.35806978609274) (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5081327481546 0.5081327481547 (pwl_15_1_4 (1/4:ℝ) (by norm_num)) (pwh_15_1_4 (1/4:ℝ) (by norm_num)) 0.9106863201415 0.4130985673021 0.00000015131 cs_b1left_v27p685_15 0.46274946567473 (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5081327481546 0.5081327481547 (pwl_15_1_4 (1/4:ℝ) (by norm_num)) (pwh_15_1_4 (1/4:ℝ) (by norm_num)) 0.9106863201415 0.4130985673021 0.00000015131 cs_b1left_v27p685_15 767.021725 (by norm_num) (by norm_num) 0.24504381833013 0.12451478882642 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (3.62465408649733:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((27685:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma bv_b1left_28_0_15_c9 : (3.267361526619:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1/4:ℝ):ℝ)):ℂ) + ((((((28000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((28000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1/4:ℝ)) (pw1_hi (1/4:ℝ)) 1 0 0 (cs_one (((28000:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.8408964152537 0.8408964152538 (pwl_2_1_4 (1/4:ℝ) (by norm_num)) (pwh_2_1_4 (1/4:ℝ) (by norm_num)) 0.8480164376045 (-0.5299699251396) 0.00000014088 cs_b1left_v28_2 0.71309386399235 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7598356856515 0.7598356856516 (pwl_3_1_4 (1/4:ℝ) (by norm_num)) (pwh_3_1_4 (1/4:ℝ) (by norm_num)) 0.793180401478 0.6089867409979 0.00000015355 cs_b1left_v28_3 0.60268665752959 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.7071067811865 0.7071067811866 (pwl_4_1_4 (1/4:ℝ) (by norm_num)) (pwh_4_1_4 (1/4:ℝ) (by norm_num)) 0.4382636670103 (-0.8988464597353) 0.00000014629 cs_b1left_v28_4 0.30989910744799 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6687403049764 0.6687403049765 (pwl_5_1_4 (1/4:ℝ) (by norm_num)) (pwh_5_1_4 (1/4:ℝ) (by norm_num)) 0.4695949379756 (-0.8828819820495) 0.00000011667 cs_b1left_v28_5 0.31403698401524 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6389431042462 0.6389431042463 (pwl_6_1_4 (1/4:ℝ) (by norm_num)) (pwh_6_1_4 (1/4:ℝ) (by norm_num)) 0.9953746855837 0.0960689091184 0.00000013362 cs_b1left_v28_6 0.63598770611935 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.6147881529512 0.6147881529513 (pwl_7_1_4 (1/4:ℝ) (by norm_num)) (pwh_7_1_4 (1/4:ℝ) (by norm_num)) (-0.4727309146966) 0.8812068328632 0.00000012239 cs_b1left_v28_7 (-0.29062944113323) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_8_1_4 (1/4:ℝ) (by norm_num)) (pwh_8_1_4 (1/4:ℝ) (by norm_num)) (-0.1047067973484) (-0.9945031355348) 0.0000001226 cs_b1left_v28_8 (-0.06225910709634) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5773502691896 0.5773502691897 (pwl_9_1_4 (1/4:ℝ) (by norm_num)) (pwh_9_1_4 (1/4:ℝ) (by norm_num)) 0.2582703951848 0.9660726696119 0.00000012095 cs_b1left_v28_9 0.14911241235313 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5623413251903 0.5623413251904 (pwl_10_1_4 (1/4:ℝ) (by norm_num)) (pwh_10_1_4 (1/4:ℝ) (by norm_num)) (-0.0696766715148) (-0.9975696273676) 0.00000015222 cs_b1left_v28_10 (-0.03918215739409) (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5491004867761 0.5491004867762 (pwl_11_1_4 (1/4:ℝ) (by norm_num)) (pwh_11_1_4 (1/4:ℝ) (by norm_num)) (-0.3923401667244) 0.9198201963273 0.00000016247 cs_b1left_v28_11 (-0.21543426574258) (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5372849659117 0.5372849659118 (pwl_12_1_4 (1/4:ℝ) (by norm_num)) (pwh_12_1_4 (1/4:ℝ) (by norm_num)) 0.8950077275241 (-0.4460506335295) 0.00000013527 cs_b1left_v28_12 0.48087412369495 (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5266403878479 0.526640387848 (pwl_13_1_4 (1/4:ℝ) (by norm_num)) (pwh_13_1_4 (1/4:ℝ) (by norm_num)) (-0.9055809258975) (-0.4241735335066) 0.00000015013 cs_b1left_v28_13 (-0.47691556910694) (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5169731539571 0.5169731539572 (pwl_14_1_4 (1/4:ℝ) (by norm_num)) (pwh_14_1_4 (1/4:ℝ) (by norm_num)) 0.06612953302 0.9978110466729 0.00000016325 cs_b1left_v28_14 0.03418710885919 (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5081327481546 0.5081327481547 (pwl_15_1_4 (1/4:ℝ) (by norm_num)) (pwh_15_1_4 (1/4:ℝ) (by norm_num)) 0.9101369223696 (-0.4143075941128) 0.00000016489 cs_b1left_v28_15 0.46247029177462 (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1/4:ℝ) (((28000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5081327481546 0.5081327481547 (pwl_15_1_4 (1/4:ℝ) (by norm_num)) (pwh_15_1_4 (1/4:ℝ) (by norm_num)) 0.9101369223696 (-0.4143075941128) 0.00000016489 cs_b1left_v28_15 784.5625 (by norm_num) (by norm_num) 0.68991063844424 0.35056618869384 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (3.61792771531323:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1/4:ℝ):ℝ)):ℂ) + ((((((28000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma rb_b1left_180 : mainRemConst 15 (1/4:ℝ) 27.695157 ≤ 38.30666995 := by
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
  have c11 := sum_ub_step c10 (remTerm_ub 11 (by norm_num) (1/4:ℝ) 0.5491004867762 2.397895273518535 (pwh_11_1_4 (1/4:ℝ) (by norm_num)) (lg_11).2 3.15727384586623 (by norm_num))
  have c12 := sum_ub_step c11 (remTerm_ub 12 (by norm_num) (1/4:ℝ) 0.5372849659118 2.484906650508165 (pwh_12_1_4 (1/4:ℝ) (by norm_num)) (lg_12).2 3.31760628657033 (by norm_num))
  have c13 := sum_ub_step c12 (remTerm_ub 13 (by norm_num) (1/4:ℝ) 0.526640387848 2.564949358181702 (pwh_13_1_4 (1/4:ℝ) (by norm_num)) (lg_13).2 3.46474878985224 (by norm_num))
  have c14 := sum_ub_step c13 (remTerm_ub 14 (by norm_num) (1/4:ℝ) 0.5169731539572 2.639057330335424 (pwh_14_1_4 (1/4:ℝ) (by norm_num)) (lg_14).2 3.60052342489307 (by norm_num))
  have c15 := sum_ub_step c14 (remTerm_ub 15 (by norm_num) (1/4:ℝ) 0.5081327481547 2.708050201822375 (pwh_15_1_4 (1/4:ℝ) (by norm_num)) (lg_15).2 3.7264097483174 (by norm_num))
  exact mainRemConst_le 15 (by norm_num) (1/4:ℝ) 27.695157 (by norm_num) _ 0.5081327481547 2.708050201822375 38.30666995 c15 (pwh_15_1_4 (1/4:ℝ) (by norm_num)) (lg_15).2 (by norm_num)
lemma pc_b1left_180 : ∀ y ∈ Set.Icc (((27685:ℤ):ℝ)/1000) (((28000:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 15 (by norm_num) (1/4:ℝ) (((27685:ℤ):ℝ)/1000) (((28000:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.708050201822375 (lg_15).2 (by norm_num) 27.695157 27.685 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 38.30666995 rb_b1left_180 0.5081327481547 28.001117 28.027888 (pwh_15_1_4 (1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 3.50013929767 3.267361526619 (by rw [hrot]; exact bv_b1left_27p685_0_15_c9) (by rw [hrot]; exact bv_b1left_28_0_15_c9) (by rw [lt_min_iff]; constructor <;> norm_num)

end H28
end Cert
end ZB
end RHV6Fresh
