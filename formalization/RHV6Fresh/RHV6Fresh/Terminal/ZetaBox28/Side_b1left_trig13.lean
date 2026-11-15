/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 13

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

lemma cs_b1left_v24p947_59 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3703953680577:ℝ):ℂ) + (((-0.9288741956376):ℝ):ℂ) * I)‖ ≤ 0.0000001342 := by
  have hl := lg_59
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.722326580691682424 101.722326643059282212 (-1.1913617) 0.00000003419 0.3703953680577 (-0.9288741956376) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_60 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0398420248835):ℝ):ℂ) + (((-0.9992059913015):ℝ):ℂ) * I)‖ ≤ 0.00000015356 := by
  have hl := lg_60
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.141613761330439231 102.141613823697989125 (-1.6106489) 0.00000005355 (-0.0398420248835) (-0.9992059913015) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_61 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4369536247434):ℝ):ℂ) + (((-0.8994840353333):ℝ):ℂ) * I)‖ ≤ 0.00000015778 := by
  have hl := lg_61
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.553970257107275101 102.553970319474849942 (-2.0230054) 0.00000005777 (-0.4369536247434) (-0.8994840353333) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_62 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7564447911576):ℝ):ℂ) + (((-0.6540575493755):ℝ):ℂ) * I)‖ ≤ 0.00000014359 := by
  have hl := lg_62
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.959621471295570761 102.959621533663145602 (-2.4286566) 0.00000004358 (-0.7564447911576) (-0.6540575493755) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_63 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9511750196617):ℝ):ℂ) + (((-0.3086520399495):ℝ):ℂ) * I)‖ ≤ 0.00000012839 := by
  have hl := lg_63
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.35878199335010725 103.358782043244207038 (-2.8278171) 0.00000002838 (-0.9511750196617) (-0.3086520399495) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_64 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9968733240612):ℝ):ℂ) + ((0.0790162974368:ℝ):ℂ) * I)‖ ≤ 0.0000001804 := by
  have hl := lg_64
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 103.7516562416646 103.7516563165056 3.0624939 0.00000008039 (-0.9968733240612) 0.0790162974368 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_65 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8934258646644):ℝ):ℂ) + ((0.4492106679939:ℝ):ℂ) * I)‖ ≤ 0.00000013241 := by
  have hl := lg_65
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.138439189662141823 104.138439252029716664 2.675711 0.0000000324 (-0.8934258646644) 0.4492106679939 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_66 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6624143851845):ℝ):ℂ) + ((0.7491376257287:ℝ):ℂ) * I)‖ ≤ 0.00000015724 := by
  have hl := lg_66
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.519316816908910059 104.5193168792764849 2.2948334 0.00000005723 (-0.6624143851845) 0.7491376257287 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_67 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3418521422512):ℝ):ℂ) + ((0.9397537511689:ℝ):ℂ) * I)‖ ≤ 0.00000017855 := by
  have hl := lg_67
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.894466743522089439 104.894466805889689227 1.9196834 0.00000007854 (-0.3418521422512) 0.9397537511689 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_68 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0207033475017:ℝ):ℂ) + ((0.9997856627308:ℝ):ℂ) * I)‖ ≤ 0.00000013995 := by
  have hl := lg_68
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.264058682119178998 105.264058756960203945 1.5500915 0.00000003994 0.0207033475017 0.9997856627308 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_69 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3754674066969:ℝ):ℂ) + ((0.9268355984253:ℝ):ℂ) * I)‖ ≤ 0.00000017809 := by
  have hl := lg_69
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.62825493776348091 105.628255000131080698 1.1858953 0.00000007808 0.3754674066969 0.9268355984253 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_70 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6771311084296:ℝ):ℂ) + ((0.735862393384:ℝ):ℂ) * I)‖ ≤ 0.00000015109 := by
  have hl := lg_70
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.987210770981044557 105.987210833348619398 0.8269394 0.00000005108 0.6771311084296 0.735862393384 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_71 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8901713132103:ℝ):ℂ) + ((0.4556259794364:ℝ):ℂ) * I)‖ ≤ 0.00000016194 := by
  have hl := lg_71
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.341074860125370889 106.341074922492970677 0.4730753 0.00000006193 0.8901713132103 0.4556259794364 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_72 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9923019696408:ℝ):ℂ) + ((0.1238418388387:ℝ):ℂ) * I)‖ ≤ 0.000000179 := by
  have hl := lg_72
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.689989638669234616 106.68998970103678451 0.1241606 0.00000007899 0.9923019696408 0.1238418388387 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_73 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9759102140937:ℝ):ℂ) + (((-0.2181725327067):ℝ):ℂ) * I)‖ ≤ 0.00000017616 := by
  have hl := lg_73
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.034091645904595861 107.034091708272170702 (-0.2199415) 0.00000007615 0.9759102140937 (-0.2181725327067) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_74 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8475939945433:ℝ):ℂ) + (((-0.5306452868105):ℝ):ℂ) * I)‖ ≤ 0.00000017433 := by
  have hl := lg_74
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.373511847740114574 107.373511910107689415 (-0.5593617) 0.00000007432 0.8475939945433 (-0.5306452868105) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_75 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6261227447104:ℝ):ℂ) + (((-0.7797245081158):ℝ):ℂ) * I)‖ ≤ 0.0000001763 := by
  have hl := lg_75
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.708375935966011154 107.708375998333585995 (-0.8942257) 0.00000007629 0.6261227447104 (-0.7797245081158) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_76 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3392710957859:ℝ):ℂ) + (((-0.9406886432631):ℝ):ℂ) * I)‖ ≤ 0.00000014803 := by
  have hl := lg_76
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.038804607698785041 108.038804670066359882 (-1.2246544) 0.00000004802 0.3392710957859 (-0.9406886432631) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_77 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0200313869323:ℝ):ℂ) + (((-0.9997993516388):ℝ):ℂ) * I)‖ ≤ 0.00000016689 := by
  have hl := lg_77
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.364913826559515385 108.364913888927115173 (-1.5507636) 0.00000006688 0.0200313869323 (-0.9997993516388) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_78 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2973048058741):ℝ):ℂ) + (((-0.9547826204967):ℝ):ℂ) * I)‖ ≤ 0.00000015507 := by
  have hl := lg_78
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.686815067000937208 108.686815129368512049 (-1.8726649) 0.00000005506 (-0.2973048058741) (-0.9547826204967) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_79 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5807657945371):ℝ):ℂ) + (((-0.8140706921914):ℝ):ℂ) * I)‖ ≤ 0.000000179 := by
  have hl := lg_79
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 109.004615543070458471 109.004615605438058259 (-2.1904654) 0.00000007899 (-0.5807657945371) (-0.8140706921914) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_80 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8036907091677):ℝ):ℂ) + (((-0.5950472619438):ℝ):ℂ) * I)‖ ≤ 0.0000001691 := by
  have hl := lg_80
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 109.318418416300171923 109.31841849114119687 (-2.5042682) 0.00000006909 (-0.8036907091677) (-0.5950472619438) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_81 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((81:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9468752720148):ℝ):ℂ) + (((-0.3216010246431):ℝ):ℂ) * I)‖ ≤ 0.00000016353 := by
  have hl := lg_81
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((81:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 109.628323035673869232 109.62832308556796902 (-2.8141728) 0.00000006352 (-0.9468752720148) (-0.3216010246431) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_82 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((82:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997727828521):ℝ):ℂ) + (((-0.0213162386877):ℝ):ℂ) * I)‖ ≤ 0.0000001754 := by
  have hl := lg_82
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((82:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 109.93442502259215726 109.934425097433207154 (-3.1202748) 0.00000007539 (-0.9997727828521) (-0.0213162386877) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_83 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((83:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9607581463874):ℝ):ℂ) + ((0.2773874256604:ℝ):ℂ) * I)‖ ≤ 0.00000014942 := by
  have hl := lg_83
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((83:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 110.236816603792543028 110.236816678633617869 2.8605189 0.00000004941 (-0.9607581463874) 0.2773874256604 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_84 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((84:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8365482116726):ℝ):ℂ) + ((0.5478933194349:ℝ):ℂ) * I)‖ ≤ 0.00000018093 := by
  have hl := lg_84
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((84:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 110.535586648319839942 110.535586710687414783 2.5617488 0.00000008092 (-0.8365482116726) 0.5478933194349 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_85 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((85:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6409369466836):ℝ):ℂ) + ((0.7675935319947:ℝ):ℂ) * I)‖ ≤ 0.00000017249 := by
  have hl := lg_85
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((85:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 110.830820856754750921 110.830820931595800815 2.2665146 0.00000007248 (-0.6409369466836) 0.7675935319947 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_86 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((86:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3930416913579):ℝ):ℂ) + ((0.919520651672:ℝ):ℂ) * I)‖ ≤ 0.00000016204 := by
  have hl := lg_86
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((86:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 111.12260196721194966 111.122602029579549448 1.9747335 0.00000006203 (-0.3930416913579) 0.919520651672 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_87 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((87:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.115272548872):ℝ):ℂ) + ((0.9933339013021:ℝ):ℂ) * I)‖ ≤ 0.0000001368 := by
  have hl := lg_87
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((87:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 111.411009803651592632 111.41100986601919242 1.6863257 0.00000003679 (-0.115272548872) 0.9933339013021 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_88 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((88:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1687706819734:ℝ):ℂ) + ((0.9856553438734:ℝ):ℂ) * I)‖ ≤ 0.00000015737 := by
  have hl := lg_88
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((88:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 111.696121471878642751 111.696121546719692645 1.401214 0.00000005736 0.1687706819734 0.9856553438734 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_89 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((89:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4362908145811:ℝ):ℂ) + ((0.8998057152031:ℝ):ℂ) * I)‖ ≤ 0.00000015245 := by
  have hl := lg_89
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((89:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 111.978011476798509302 111.978011551639584143 1.119324 0.00000005244 0.4362908145811 0.8998057152031 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_90 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((90:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6670280639727:ℝ):ℂ) + ((0.7450325911481:ℝ):ℂ) * I)‖ ≤ 0.00000014645 := by
  have hl := lg_90
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((90:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 112.256751813304806539 112.25675187567238138 0.8405837 0.00000004644 0.6670280639727 0.7450325911481 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_91 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((91:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.844629610797:ℝ):ℂ) + ((0.5353511189537:ℝ):ℂ) * I)‖ ≤ 0.0000001526 := by
  have hl := lg_91
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((91:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 112.532412076651542534 112.532412139019142322 0.5649234 0.00000005259 0.844629610797 0.5353511189537 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_92 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((92:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9575905956886:ℝ):ℂ) + ((0.2881323498824:ℝ):ℂ) * I)‖ ≤ 0.00000013836 := by
  have hl := lg_92
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((92:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 112.805059592733213602 112.805059667574288443 0.2922759 0.00000003835 0.9575905956886 0.2881323498824 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_93 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((93:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997451729355:ℝ):ℂ) + ((0.0225740823088:ℝ):ℂ) * I)‖ ≤ 0.00000015642 := by
  have hl := lg_93
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((93:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 113.074759523269938069 113.074759585637537857 0.022576 0.00000005641 0.9997451729355 0.0225740823088 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_94 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((94:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9703215326773:ℝ):ℂ) + (((-0.2418183682494):ℝ):ℂ) * I)‖ ≤ 0.00000014 := by
  have hl := lg_94
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((94:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 113.341574894380577563 113.341574969221677351 (-0.2442394) 0.00000003999 0.9703215326773 (-0.2418183682494) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_95 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((95:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8736065811893:ℝ):ℂ) + (((-0.4866328608949):ℝ):ℂ) * I)‖ ≤ 0.00000014691 := by
  have hl := lg_95
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((95:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 113.605566782334356964 113.605566844701956752 (-0.5082313) 0.0000000469 0.8736065811893 (-0.4866328608949) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_96 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((96:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7182873128466:ℝ):ℂ) + (((-0.6957466034438):ℝ):ℂ) * I)‖ ≤ 0.00000013926 := by
  have hl := lg_96
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((96:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 113.866794293638967308 113.866794368479992255 (-0.7694588) 0.00000003925 0.7182873128466 (-0.6957466034438) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_97 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((97:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5165501367974:ℝ):ℂ) + (((-0.8562569451833):ℝ):ℂ) * I)‖ ≤ 0.00000018743 := by
  have hl := lg_97
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((97:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 114.12531474181473337 114.125314816655783264 (-1.0279793) 0.00000008742 0.5165501367974 (-0.8562569451833) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_98 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((98:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2830264591684:ℝ):ℂ) + (((-0.959112101587):ℝ):ℂ) * I)‖ ≤ 0.00000017128 := by
  have hl := lg_98
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((98:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 114.381183657970445268 114.381183720338045056 (-1.2838482) 0.00000007127 0.2830264591684 (-0.959112101587) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_99 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((99:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0336705614567:ℝ):ℂ) + (((-0.999432985893):ℝ):ℂ) * I)‖ ≤ 0.00000016036 := by
  have hl := lg_99
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((99:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 114.634454868883277367 114.634454931250877155 (-1.5371194) 0.00000006035 0.0336705614567 (-0.999432985893) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_100 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((100:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2153485821993):ℝ):ℂ) + (((-0.976537243603):ℝ):ℂ) * I)‖ ≤ 0.00000013831 := by
  have hl := lg_100
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((100:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 114.885180590935743846 114.88518066577679374 (-1.7878451) 0.0000000383 (-0.2153485821993) (-0.976537243603) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_101 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((101:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4486727618473):ℝ):ℂ) + (((-0.8936961188076):ℝ):ℂ) * I)‖ ≤ 0.00000014035 := by
  have hl := lg_101
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((101:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 115.133411494729700995 115.133411569570800783 (-2.036076) 0.00000004034 (-0.4486727618473) (-0.8936961188076) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_102 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((102:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6526409605336):ℝ):ℂ) + (((-0.7576673258209):ℝ):ℂ) * I)‖ ≤ 0.00000017972 := by
  have hl := lg_102
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((102:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 115.379196734093546306 115.3791968089345962 (-2.2818612) 0.00000007971 (-0.6526409605336) (-0.7576673258209) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_103 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((103:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8159971884012):ℝ):ℂ) + (((-0.5780558696748):ℝ):ℂ) * I)‖ ≤ 0.00000017608 := by
  have hl := lg_103
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((103:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 115.622584030455542014 115.622584105296616855 (-2.5252485) 0.00000007607 (-0.8159971884012) (-0.5780558696748) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_104 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((104:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.930394599519):ℝ):ℂ) + (((-0.3665595299888):ℝ):ℂ) * I)‖ ≤ 0.00000016759 := by
  have hl := lg_104
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((104:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 115.8636197219706699 115.863619796811719794 (-2.7662842) 0.00000006758 (-0.930394599519) (-0.3665595299888) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_105 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((105:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9906875295893):ℝ):ℂ) + (((-0.1361551258743):ℝ):ℂ) * I)‖ ≤ 0.00000015611 := by
  have hl := lg_105
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((105:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 116.102348822955411865 116.102348885323011653 (-3.0050133) 0.0000000561 (-0.9906875295893) (-0.1361551258743) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_106 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((106:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9950154544849):ℝ):ℂ) + ((0.0997208346346:ℝ):ℂ) * I)‖ ≤ 0.00000018035 := by
  have hl := lg_106
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((106:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 116.338815041904573118 116.338815116745647959 3.0417058 0.00000008034 (-0.9950154544849) 0.0997208346346 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_107 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((107:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9446950782599):ℝ):ℂ) + ((0.3279500097903:ℝ):ℂ) * I)‖ ≤ 0.00000014202 := by
  have hl := lg_107
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((107:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 116.573060894411981704 116.573060969253106439 2.8074599 0.00000004201 (-0.9446950782599) 0.3279500097903 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_108 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((108:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.843945732945):ℝ):ℂ) + ((0.5364285598044:ℝ):ℂ) * I)‖ ≤ 0.00000014578 := by
  have hl := lg_108
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((108:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 116.805127690643601924 116.805127753011176765 2.5753931 0.00000004577 (-0.843945732945) 0.5364285598044 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_109 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((109:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6994794730404):ℝ):ℂ) + ((0.7146526896133:ℝ):ℂ) * I)‖ ≤ 0.00000015088 := by
  have hl := lg_109
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((109:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 117.035055585546116005 117.03505564791374074 2.3454652 0.00000005087 (-0.6994794730404) 0.7146526896133 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_110 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((110:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5199913921207):ℝ):ℂ) + ((0.8541715004103:ℝ):ℂ) * I)‖ ≤ 0.00000018496 := by
  have hl := lg_110
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((110:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 117.262883646514214674 117.262883721355289515 2.1176372 0.00000008495 (-0.5199913921207) 0.8541715004103 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_111 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((111:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3155864017494):ℝ):ℂ) + ((0.9488968453046:ℝ):ℂ) * I)‖ ≤ 0.00000013671 := by
  have hl := lg_111
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((111:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 117.488649899714481882 117.48864996208208167 1.8918709 0.0000000367 (-0.3155864017494) 0.9488968453046 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_112 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((112:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0971795610175):ℝ):ℂ) + ((0.9952668651774:ℝ):ℂ) * I)‖ ≤ 0.00000014173 := by
  have hl := lg_112
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((112:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 117.712391303289572634 117.712391378130622528 1.6681295 0.00000004172 (-0.0971795610175) 0.9952668651774 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_113 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((113:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1240986690261:ℝ):ℂ) + ((0.9922698828171:ℝ):ℂ) * I)‖ ≤ 0.00000016192 := by
  have hl := lg_113
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((113:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 117.934143874507583649 117.934143949348683437 1.4463769 0.00000006191 0.1240986690261 0.9922698828171 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_114 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((114:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3374608664022:ℝ):ℂ) + ((0.9413395581017:ℝ):ℂ) * I)‖ ≤ 0.00000017675 := by
  have hl := lg_114
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((114:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 118.153942659673152349 118.153942722040752137 1.2265781 0.00000007674 0.3374608664022 0.9413395581017 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_115 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((115:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5329619991795:ℝ):ℂ) + ((0.8461391773406:ℝ):ℂ) * I)‖ ≤ 0.00000016906 := by
  have hl := lg_115
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((115:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 118.371821767368785525 118.371821842209885313 1.008699 0.00000006905 0.5329619991795 0.8461391773406 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_116 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((116:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7019203114368:ℝ):ℂ) + ((0.7122554853369:ℝ):ℂ) * I)‖ ≤ 0.00000017781 := by
  have hl := lg_116
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((116:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 118.587814458621325324 118.587814533462400165 0.7927063 0.0000000778 0.7019203114368 0.7122554853369 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_117 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((117:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.837246726337:ℝ):ℂ) + ((0.5468253096172:ℝ):ℂ) * I)‖ ≤ 0.00000014495 := by
  have hl := lg_117
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((117:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 118.801953118975304516 118.801953181342904304 0.5785677 0.00000004494 0.837246726337 0.5468253096172 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_118 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((118:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9336763077026:ℝ):ℂ) + ((0.3581180705226:ℝ):ℂ) * I)‖ ≤ 0.00000014879 := by
  have hl := lg_118
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((118:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 119.014269287635782424 119.014269362476882212 0.3662515 0.00000004878 0.9336763077026 0.3581180705226 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_119 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((119:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9878990198457:ℝ):ℂ) + ((0.1550984416035:ℝ):ℂ) * I)‖ ≤ 0.00000018219 := by
  have hl := lg_119
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((119:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 119.224793743744151632 119.224793818585226473 0.1557271 0.00000008218 0.9878990198457 0.1550984416035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_120 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((120:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9985939368886:ℝ):ℂ) + (((-0.0530108404887):ℝ):ℂ) * I)‖ ≤ 0.00000016815 := by
  have hl := lg_120
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((120:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 119.433556468274539231 119.433556543115589125 (-0.0530357) 0.00000006814 0.9985939368886 (-0.0530108404887) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_2 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0339709894865:ℝ):ℂ) + ((0.9994228193678:ℝ):ℂ) * I)‖ ≤ 0.00000011332 := by
  have hl := lg_2
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.3127371223531 17.3127371348416 1.5368188 0.00000001331 0.0339709894865 0.9994228193678 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_3 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6717003124054):ℝ):ℂ) + (((-0.7408229817541):ℝ):ℂ) * I)‖ ≤ 0.00000011136 := by
  have hl := lg_3
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.440039127570712228 27.440039140059237205 (-2.3072979) 0.00000001135 (-0.6717003124054) (-0.7408229817541) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_4 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9976919434948):ℝ):ℂ) + ((0.0679027639309:ℝ):ℂ) * I)‖ ≤ 0.00000012662 := by
  have hl := lg_4
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.6254742447062 34.6254742696832 3.0736376 0.00000002661 (-0.9976919434948) 0.0679027639309 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_5 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8010352190944):ℝ):ℂ) + (((-0.59861722137):ℝ):ℂ) * I)‖ ≤ 0.00000011721 := by
  have hl := lg_5
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.198930725881198193 40.19893075085822317 (-2.4998189) 0.0000000172 (-0.8010352190944) (-0.59861722137) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_6 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7175770688374:ℝ):ℂ) + (((-0.6964791097217):ℝ):ℂ) * I)‖ ≤ 0.00000012466 := by
  have hl := lg_6
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.752776249923812228 44.752776274900837205 (-0.7704791) 0.00000002465 0.7175770688374 (-0.6964791097217) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_7 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0915599602031):ℝ):ℂ) + ((0.9957995650166:ℝ):ℂ) * I)‖ ≤ 0.00000014752 := by
  have hl := lg_7
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.602997779969235294 48.602997804946285248 1.6624847 0.00000004751 (-0.0915599602031) 0.9957995650166 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_8 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1017561474079):ℝ):ℂ) + (((-0.9948093719222):ℝ):ℂ) * I)‖ ≤ 0.0000001471 := by
  have hl := lg_8
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.9382113670593 51.9382114045248 (-1.6727289) 0.00000004709 (-0.1017561474079) (-0.9948093719222) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_9 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0976373734777):ℝ):ℂ) + ((0.9952220572817:ℝ):ℂ) * I)‖ ≤ 0.00000011552 := by
  have hl := lg_9
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.880078255141424456 54.88007828011847441 1.6685895 0.00000001551 (-0.0976373734777) 0.9952220572817 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_10 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5710597521251:ℝ):ℂ) + (((-0.8209084964251):ℝ):ℂ) * I)‖ ≤ 0.0000001211 := by
  have hl := lg_10
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.511667848234298193 57.51166788569982317 (-0.9630001) 0.00000002109 0.5710597521251 (-0.8209084964251) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_11 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9796733269812):ℝ):ℂ) + ((0.2005995316031:ℝ):ℂ) * I)‖ ≤ 0.0000001626 := by
  have hl := lg_11
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.892230209206898741 59.892230246672448695 2.9396228 0.00000006259 (-0.9796733269812) 0.2005995316031 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_12 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7204539185301:ℝ):ℂ) + ((0.6935028127373:ℝ):ℂ) * I)‖ ≤ 0.00000013796 := by
  have hl := lg_12
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.065513372276912228 62.065513409742437205 0.7663397 0.00000003795 0.7204539185301 0.6935028127373 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_13 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3315153728369:ℝ):ℂ) + (((-0.943449817199):ℝ):ℂ) * I)‖ ≤ 0.00000014752 := by
  have hl := lg_13
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.0647400818388209 64.064740119304370854 (-1.232887) 0.00000004751 0.3315153728369 (-0.943449817199) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_14 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9983351905616):ℝ):ℂ) + (((-0.0576788239253):ℝ):ℂ) * I)‖ ≤ 0.00000016801 := by
  have hl := lg_14
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.915734902322335294 65.915734939787885248 (-3.0838818) 0.000000068 (-0.9983351905616) (-0.0576788239253) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_15 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0945862191775:ℝ):ℂ) + ((0.9955166734624:ℝ):ℂ) * I)‖ ≤ 0.00000012554 := by
  have hl := lg_15
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.638969853451910421 67.638969890917460375 1.4760685 0.00000002553 0.0945862191775 0.9955166734624 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_16 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9907784302066:ℝ):ℂ) + (((-0.135492074445):ℝ):ℂ) * I)‖ ≤ 0.00000016041 := by
  have hl := lg_16
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.2509484894124 69.2509485393664 (-0.1359101) 0.0000000604 0.9907784302066 (-0.135492074445) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_17 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0792517765026):ℝ):ℂ) + (((-0.9968546312882):ℝ):ℂ) * I)‖ ≤ 0.00000013952 := by
  have hl := lg_17
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.765169668521472018 70.765169718475496995 (-1.6501313) 0.00000003951 (-0.0792517765026) (-0.9968546312882) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_18 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9979644718591):ℝ):ℂ) + (((-0.063772347946):ℝ):ℂ) * I)‖ ≤ 0.000000136 := by
  have hl := lg_18
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.192815377494524456 72.19281541496007441 (-3.077777) 0.00000003599 (-0.9979644718591) (-0.063772347946) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_19 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2803656091201):ℝ):ℂ) + ((0.9598932884551:ℝ):ℂ) * I)‖ ≤ 0.00000012301 := by
  have hl := lg_19
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.543252363162183131 73.543252400627758062 1.8549713 0.000000023 (-0.2803656091201) 0.9598932884551 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_20 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8398341487758:ℝ):ℂ) + ((0.5428430735949:ℝ):ℂ) * I)‖ ≤ 0.0000001344 := by
  have hl := lg_20
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.824404970587398193 74.82440502054142317 0.5738187 0.00000003439 0.8398341487758 0.5428430735949 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_21 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7992120568686:ℝ):ℂ) + (((-0.6010491561893):ℝ):ℂ) * I)‖ ≤ 0.00000015887 := by
  have hl := lg_21
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.043036907539947522 76.043036945005522453 (-0.6448132) 0.00000005886 0.7992120568686 (-0.6010491561893) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_22 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2337642149131):ℝ):ℂ) + (((-0.972293315736):ℝ):ℂ) * I)‖ ≤ 0.00000015461 := by
  have hl := lg_22
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.204967331559998741 77.204967381514048695 (-1.8067437) 0.0000000546 (-0.2337642149131) (-0.972293315736) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_23 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9748883149879):ℝ):ℂ) + (((-0.2226943488397):ℝ):ℂ) * I)‖ ≤ 0.00000016911 := by
  have hl := lg_23
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.315239005291694582 78.315239055245769513 (-2.9170153) 0.0000000691 (-0.9748883149879) (-0.2226943488397) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_24 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6686280038514):ℝ):ℂ) + ((0.7435970632316:ℝ):ℂ) * I)‖ ≤ 0.00000015126 := by
  have hl := lg_24
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.378250494630012228 79.378250544584037205 2.3031585 0.00000005125 (-0.6686280038514) 0.7435970632316 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_25 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2833148513773:ℝ):ℂ) + ((0.9590269521703:ℝ):ℂ) * I)‖ ≤ 0.00000014159 := by
  have hl := lg_25
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.397861451762396386 80.39786150171644634 1.2835475 0.00000004158 0.2833148513773 0.9590269521703 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_26 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9541671814824:ℝ):ℂ) + ((0.2992741047634:ℝ):ℂ) * I)‖ ≤ 0.00000016083 := by
  have hl := lg_26
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.3774772041919209 81.377477254145970854 0.3039318 0.00000006082 0.9541671814824 0.2992741047634 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_27 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8028664262617:ℝ):ℂ) + (((-0.5961589566398):ℝ):ℂ) * I)‖ ≤ 0.00000012686 := by
  have hl := lg_27
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.320117382712136684 82.320117420177711615 (-0.6387084) 0.00000002685 0.8028664262617 (-0.5961589566398) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_28 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0237309988374:ℝ):ℂ) + (((-0.9997183801921):ℝ):ℂ) * I)‖ ≤ 0.00000016867 := by
  have hl := lg_28
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.228472024675435294 83.228472074629485248 (-1.5470631) 0.00000006866 0.0237309988374 (-0.9997183801921) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_29 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.753087695295):ℝ):ℂ) + (((-0.6579201495324):ℝ):ℂ) * I)‖ ≤ 0.00000017375 := by
  have hl := lg_29
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.104947919601526084 84.104947969555601015 (-2.423539) 0.00000007374 (-0.753087695295) (-0.6579201495324) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_30 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9917288928734):ℝ):ℂ) + ((0.1283503120875:ℝ):ℂ) * I)‖ ≤ 0.00000012526 := by
  have hl := lg_30
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 84.951706975805010421 84.951707025759060375 3.0128873 0.00000002525 (-0.9917288928734) 0.1283503120875 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_31 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5835550412507):ℝ):ℂ) + ((0.8120735889192:ℝ):ℂ) * I)‖ ≤ 0.00000012991 := by
  have hl := lg_31
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.770698380454831651 85.770698430408906582 2.1938959 0.0000000299 (-0.5835550412507) 0.8120735889192 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_32 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1690715946799:ℝ):ℂ) + ((0.9856037722495:ℝ):ℂ) * I)‖ ≤ 0.00000017371 := by
  have hl := lg_32
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.5636856117655 86.563685674208 1.4009087 0.0000000737 0.1690715946799 0.9856037722495 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_33 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8066556231403:ℝ):ℂ) + ((0.5910217471939:ℝ):ℂ) * I)‖ ≤ 0.00000016375 := by
  have hl := lg_33
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.332269336777610969 87.3322693867316859 0.6323249 0.00000006374 0.8066556231403 0.5910217471939 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_34 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9935870048359:ℝ):ℂ) + (((-0.1130701721112):ℝ):ℂ) * I)‖ ≤ 0.00000015282 := by
  have hl := lg_34
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.077906790874572018 88.077906853317096995 (-0.1133125) 0.00000005281 0.9935870048359 (-0.1130701721112) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_35 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.669445521462:ℝ):ℂ) + (((-0.7428611537794):ℝ):ℂ) * I)‖ ≤ 0.00000015531 := by
  have hl := lg_35
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.801928505850433487 88.801928555804508418 (-0.8373342) 0.0000000553 0.669445521462 (-0.7428611537794) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_36 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0298336994426:ℝ):ℂ) + (((-0.9995548761211):ℝ):ℂ) * I)‖ ≤ 0.0000001493 := by
  have hl := lg_36
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.505552499847624456 89.50555254980167441 (-1.5409582) 0.00000004929 0.0298336994426 (-0.9995548761211) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_37 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6087674614166):ℝ):ℂ) + (((-0.7933487114174):ℝ):ℂ) * I)‖ ≤ 0.0000001276 := by
  have hl := lg_37
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.189896678144147834 90.189896728098222765 (-2.2253024) 0.00000002759 (-0.6087674614166) (-0.7933487114174) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_38 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.96886355192):ℝ):ℂ) + (((-0.2475952695315):ℝ):ℂ) * I)‖ ≤ 0.00000013497 := by
  have hl := lg_38
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.855989485515283131 90.855989535469358062 (-2.8913952) 0.00000003496 (-0.96886355192) (-0.2475952695315) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_39 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9216082833928):ℝ):ℂ) + ((0.3881213364868:ℝ):ℂ) * I)‖ ≤ 0.00000015168 := by
  have hl := lg_39
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.504779209409533128 91.504779259363608059 2.7430004 0.00000005167 (-0.9216082833928) 0.3881213364868 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_40 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5139997580479):ℝ):ℂ) + ((0.857790329113:ℝ):ℂ) * I)‖ ≤ 0.0000001477 := by
  have hl := lg_40
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.137142092940498193 92.13714215538302317 2.1106375 0.00000004769 (-0.5139997580479) 0.857790329113 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_41 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0768304380302:ℝ):ℂ) + ((0.9970441734407:ℝ):ℂ) * I)‖ ≤ 0.00000013237 := by
  have hl := lg_41
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.75388947761019466 92.753889540052744614 1.4938901 0.00000003236 0.0768304380302 0.9970441734407 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_42 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6278522666388:ℝ):ℂ) + ((0.7783325325827:ℝ):ℂ) * I)‖ ≤ 0.00000017217 := by
  have hl := lg_42
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.355774029893047522 93.355774079847122453 0.8920056 0.00000007216 0.6278522666388 0.7783325325827 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_43 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.954061628082:ℝ):ℂ) + ((0.2996104300945:ℝ):ℂ) * I)‖ ≤ 0.000000144 := by
  have hl := lg_43
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.94349526370746306 93.943495313661562968 0.3042843 0.00000004399 0.954061628082 0.2996104300945 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_44 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9637909251789:ℝ):ℂ) + (((-0.2666590567424):ℝ):ℂ) * I)‖ ≤ 0.0000001538 := by
  have hl := lg_44
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.517704453913098741 94.517704516355648695 (-0.2699249) 0.00000005379 0.9637909251789 (-0.2666590567424) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_45 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6739680374604:ℝ):ℂ) + (((-0.7387605054967):ℝ):ℂ) * I)‖ ≤ 0.00000012669 := by
  have hl := lg_45
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.079008981022622649 95.07900903097669758 (-0.8312294) 0.00000002668 0.6739680374604 (-0.7387605054967) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_46 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.18944779523:ℝ):ℂ) + (((-0.9818907947844):ℝ):ℂ) * I)‖ ≤ 0.00000018006 := by
  have hl := lg_46
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.627976127644794582 95.627976190087369513 (-1.3801966) 0.00000008005 0.18944779523 (-0.9818907947844) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_47 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3396649760217):ℝ):ℂ) + (((-0.9405464922384):ℝ):ℂ) * I)‖ ≤ 0.00000017021 := by
  have hl := lg_47
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.165136615448787433 96.165136677891387341 (-1.917357) 0.0000000702 (-0.3396649760217) (-0.9405464922384) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_48 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7658818236856):ℝ):ℂ) + (((-0.6429813621793):ℝ):ℂ) * I)‖ ≤ 0.00000017175 := by
  have hl := lg_48
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.690987616983112228 96.690987679425637205 (-2.443208) 0.00000007174 (-0.7658818236856) (-0.6429813621793) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_49 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9832335641565):ℝ):ℂ) + (((-0.1823506456521):ℝ):ℂ) * I)‖ ≤ 0.00000014777 := by
  have hl := lg_49
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.205995559938470588 97.205995609892570496 (-2.958216) 0.00000004776 (-0.9832335641565) (-0.1823506456521) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_50 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9488489344794):ℝ):ℂ) + ((0.3157304219377:ℝ):ℂ) * I)‖ ≤ 0.00000014077 := by
  have hl := lg_50
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.710598574115496386 97.71059863655804634 2.8203663 0.00000004076 (-0.9488489344794) 0.3157304219377 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_51 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6852593720703):ℝ):ℂ) + ((0.728299109548:ℝ):ℂ) * I)‖ ≤ 0.00000014368 := by
  have hl := lg_51
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.205208796092184246 98.2052088585347342 2.3257561 0.00000004367 (-0.6852593720703) 0.728299109548 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_52 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.266687366256):ℝ):ℂ) + ((0.9637830921312:ℝ):ℂ) * I)‖ ≤ 0.00000017413 := by
  have hl := lg_52
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.6902143265450209 98.690214388987570854 1.8407506 0.00000007412 (-0.266687366256) 0.9637830921312 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_53 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2043626059035:ℝ):ℂ) + ((0.9788952575778:ℝ):ℂ) * I)‖ ≤ 0.00000013991 := by
  have hl := lg_53
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.165981092328044938 99.165981154770619869 1.3649838 0.0000000399 0.2043626059035 0.9788952575778 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_54 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.623089032162:ℝ):ℂ) + ((0.782150917662:ℝ):ℂ) * I)‖ ≤ 0.00000014016 := by
  have hl := lg_54
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.632854505065236684 99.632854555019311615 0.8981104 0.00000004015 0.623089032162 0.782150917662 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_55 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9048351725523:ℝ):ℂ) + ((0.4257620350762:ℝ):ℂ) * I)‖ ≤ 0.0000001798 := by
  have hl := lg_55
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.091160935088096934 100.091160997530671865 0.4398039 0.00000007979 0.9048351725523 0.4257620350762 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_56 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999475276177:ℝ):ℂ) + (((-0.0102441208184):ℝ):ℂ) * I)‖ ≤ 0.00000016786 := by
  have hl := lg_56
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.541209147028535294 100.541209209471085248 (-0.0102443) 0.00000006785 0.9999475276177 (-0.0102441208184) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_57 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8994326753646:ℝ):ℂ) + (((-0.4370593352011):ℝ):ℂ) * I)‖ ≤ 0.00000012583 := by
  have hl := lg_57
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.983291490732895359 100.983291540686995267 (-0.4523266) 0.00000002582 0.8994326753646 (-0.4370593352011) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_58 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6319572766047:ℝ):ℂ) + (((-0.7750032261523):ℝ):ℂ) * I)‖ ≤ 0.00000017293 := by
  have hl := lg_58
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.417685041954626084 101.417685104397201015 (-0.8867202) 0.00000007292 0.6319572766047 (-0.7750032261523) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_59 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2542851903831:ℝ):ℂ) + (((-0.9671292788205):ℝ):ℂ) * I)‖ ≤ 0.00000015155 := by
  have hl := lg_59
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.844652703969862184 101.844652766412462092 (-1.3136878) 0.00000005154 0.2542851903831 (-0.9671292788205) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_60 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1619662356923):ℝ):ℂ) + (((-0.986796300406):ℝ):ℂ) * I)‖ ≤ 0.00000014574 := by
  have hl := lg_60
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.264444098158110421 102.264444160600660375 (-1.7334792) 0.00000004573 (-0.1619662356923) (-0.986796300406) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_61 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5442839099062):ℝ):ℂ) + (((-0.8389010820168):ℝ):ℂ) * I)‖ ≤ 0.00000014189 := by
  have hl := lg_61
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.677296472993482591 102.677296535436057522 (-2.1463316) 0.00000004188 (-0.5442839099062) (-0.8389010820168) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_62 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8314288139454):ℝ):ℂ) + (((-0.5556312871663):ℝ):ℂ) * I)‖ ≤ 0.00000015039 := by
  have hl := lg_62
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.083435502807931651 103.083435565250506582 (-2.5524706) 0.00000005038 (-0.8314288139454) (-0.5556312871663) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_63 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9821020162139):ℝ):ℂ) + (((-0.1883497528809):ℝ):ℂ) * I)‖ ≤ 0.00000017021 := by
  have hl := lg_63
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.48307603511065975 103.483076085064759658 (-2.9521111) 0.0000000702 (-0.9821020162139) (-0.1883497528809) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_64 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9792913713453):ℝ):ℂ) + ((0.2024559450564:ℝ):ℂ) * I)‖ ≤ 0.00000018701 := by
  have hl := lg_64
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 103.8764227341186 103.8764228090496 2.9377275 0.000000087 (-0.9792913713453) 0.2024559450564 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_65 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8303207934015):ℝ):ℂ) + ((0.5572857256224:ℝ):ℂ) * I)‖ ≤ 0.00000014812 := by
  have hl := lg_65
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.263670807720019093 104.263670870162594024 2.5504794 0.00000004811 (-0.8303207934015) 0.5572857256224 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_66 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5632777311948):ℝ):ℂ) + ((0.8262676306927:ℝ):ℂ) * I)‖ ≤ 0.00000016294 := by
  have hl := lg_66
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.645006459130710969 104.6450065215732859 2.1691437 0.00000006293 (-0.5632777311948) 0.8262676306927 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_67 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2209089753124):ℝ):ℂ) + ((0.9752944297111:ℝ):ℂ) * I)‖ ≤ 0.00000016247 := by
  have hl := lg_67
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.020607522064826549 105.020607584507426457 1.7935427 0.00000006246 (-0.2209089753124) 0.9752944297111 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_68 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.146758043893:ℝ):ℂ) + ((0.9891724200323:ℝ):ℂ) * I)‖ ≤ 0.00000016612 := by
  have hl := lg_68
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.390643913227672018 105.390643988158696995 1.4235063 0.00000006611 0.146758043893 0.9891724200323 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_69 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4898557004391:ℝ):ℂ) + ((0.8718035287536:ℝ):ℂ) * I)‖ ≤ 0.00000017327 := by
  have hl := lg_69
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.75527813286240681 105.755278195305006718 1.0588721 0.00000007326 0.4898557004391 0.8718035287536 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_70 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7651741154805:ℝ):ℂ) + ((0.6438234020277:ℝ):ℂ) * I)‖ ≤ 0.00000016861 := by
  have hl := lg_70
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.114665628203533487 106.114665690646108418 0.6994846 0.0000000686 0.7651741154805 0.6438234020277 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_71 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9410095202007:ℝ):ℂ) + ((0.338380086429:ℝ):ℂ) * I)‖ ≤ 0.00000016567 := by
  have hl := lg_71
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.468955256397618499 106.468955318840218407 0.3451949 0.00000006566 0.9410095202007 0.338380086429 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_72 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999914326961:ℝ):ℂ) + (((-0.0041393881788):ℝ):ℂ) * I)‖ ≤ 0.00000016261 := by
  have hl := lg_72
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.818289622200724456 106.81828968464327441 (-0.0041394) 0.0000000626 0.9999914326961 (-0.0041393881788) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_73 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9398329922583:ℝ):ℂ) + (((-0.3416342293489):ℝ):ℂ) * I)‖ ≤ 0.0000001695 := by
  have hl := lg_73
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.162805429100055751 107.162805491542630682 (-0.3486552) 0.00000006949 0.9398329922583 (-0.3416342293489) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_74 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7722103728823:ℝ):ℂ) + (((-0.6353669333644):ℝ):ℂ) * I)‖ ≤ 0.0000001409 := by
  have hl := lg_74
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.502633800497247834 107.502633862939822765 (-0.6884836) 0.00000004089 0.7722103728823 (-0.6353669333644) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_75 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5201665321201:ℝ):ℂ) + (((-0.8540648563558):ℝ):ℂ) * I)‖ ≤ 0.00000014273 := by
  have hl := lg_75
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.837900579333108614 107.837900641775683545 (-1.0237504) 0.00000004272 0.5201665321201 (-0.8540648563558) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_76 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2145391089323:ℝ):ℂ) + (((-0.9767153990485):ℝ):ℂ) * I)‖ ≤ 0.00000014827 := by
  have hl := lg_76
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.168726607868383131 108.168726670310958062 (-1.3545764) 0.00000004826 0.2145391089323 (-0.9767153990485) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_77 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1100580684935):ℝ):ℂ) + (((-0.9939251589325):ℝ):ℂ) * I)‖ ≤ 0.00000013289 := by
  have hl := lg_77
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.495227989176134035 108.495228051618733943 (-1.6810778) 0.00000003288 (-0.1100580684935) (-0.9939251589325) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_78 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.419205259235):ℝ):ℂ) + (((-0.9078914861513):ℝ):ℂ) * I)‖ ≤ 0.00000017217 := by
  have hl := lg_78
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.817516331762633128 108.817516394205208059 (-2.0033661) 0.00000007216 (-0.419205259235) (-0.9078914861513) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_79 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6821891432597):ℝ):ℂ) + (((-0.7311757468609):ℝ):ℂ) * I)‖ ≤ 0.00000014346 := by
  have hl := lg_79
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 109.135698978605477261 109.135699041048077169 (-2.3215488) 0.00000004345 (-0.6821891432597) (-0.7311757468609) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p977_80 : ‖exp (-((((((24977:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8747563060257):ℝ):ℂ) + (((-0.484563107321):ℝ):ℂ) * I)‖ ≤ 0.00000016819 := by
  have hl := lg_80
  refine (ecis_approx ((((24977:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 109.449879215293598193 109.44987929022462317 (-2.635729) 0.00000006818 (-0.8747563060257) (-0.484563107321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_2 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0623560463334:ℝ):ℂ) + ((0.9980539682229:ℝ):ℂ) * I)‖ ≤ 0.00000014773 := by
  have hl := lg_2
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.3411561567454 17.3411561692544 1.5083998 0.00000004772 0.0623560463334 0.9980539682229 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_3 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7043767088361):ℝ):ℂ) + (((-0.7098263534307):ℝ):ℂ) * I)‖ ≤ 0.0000001152 := by
  have hl := lg_3
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.485082231395446952 27.48508224390447197 (-2.352341) 0.00000001519 (-0.7043767088361) (-0.7098263534307) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_4 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9922234343319):ℝ):ℂ) + ((0.1244694979872:ℝ):ℂ) * I)‖ ≤ 0.0000001296 := by
  have hl := lg_4
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.6823123134908 34.6823123385088 3.0167995 0.00000002959 (-0.9922234343319) 0.1244694979872 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_5 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8387641243035):ℝ):ℂ) + (((-0.5444949436994):ℝ):ℂ) * I)‖ ≤ 0.00000016223 := by
  have hl := lg_5
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.264917680269680762 40.26491770528770578 (-2.5658058) 0.00000006222 (-0.8387641243035) (-0.5444949436994) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_6 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6645227873853:ℝ):ℂ) + (((-0.7472680008174):ℝ):ℂ) * I)‖ ≤ 0.00000016213 := by
  have hl := lg_6
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.826238388140846952 44.82623841315887197 (-0.8439413) 0.00000006212 0.6645227873853 (-0.7472680008174) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_7 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0119056919242):ℝ):ℂ) + ((0.9999291247381:ℝ):ℂ) * I)‖ ≤ 0.00000016139 := by
  have hl := lg_7
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.682780096059187596 48.682780121077237632 1.5827023 0.00000006138 (-0.0119056919242) 0.9999291247381 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_8 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1860983999974):ℝ):ℂ) + (((-0.9825311117301):ℝ):ℂ) * I)‖ ≤ 0.00000015034 := by
  have hl := lg_8
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.0234684702362 52.0234685077632 (-1.757986) 0.00000005033 (-0.1860983999974) (-0.9825311117301) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_9 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0077068969096):ℝ):ℂ) + ((0.9999703014289:ℝ):ℂ) * I)‖ ≤ 0.00000012321 := by
  have hl := lg_9
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.970164462790893904 54.97016448780894394 1.5785033 0.0000000232 (-0.0077068969096) 0.9999703014289 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_10 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4911332375664:ℝ):ℂ) + (((-0.8710844637333):ℝ):ℂ) * I)‖ ≤ 0.00000012762 := by
  have hl := lg_10
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.606073837015080762 57.60607387454210578 (-1.0574061) 0.00000002761 0.4911332375664 (-0.8710844637333) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_11 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9552526548261):ℝ):ℂ) + ((0.2957910837559:ℝ):ℂ) * I)‖ ≤ 0.00000015645 := by
  have hl := lg_11
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.990543915359658594 59.99054395288670863 2.8413091 0.00000005644 (-0.9552526548261) 0.2957910837559 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_12 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7872508072617:ℝ):ℂ) + ((0.616632926842:ℝ):ℂ) * I)‖ ≤ 0.00000012692 := by
  have hl := lg_12
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.167394544886246952 62.16739458241327197 0.6644585 0.00000002691 0.7872508072617 0.616632926842 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_13 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2306506665456:ℝ):ℂ) + (((-0.9730366231659):ℝ):ℂ) * I)‖ ≤ 0.00000016635 := by
  have hl := lg_13
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.1699030054627706 64.169903042989820636 (-1.33805) 0.00000006634 0.2306506665456 (-0.9730366231659) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_14 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9987256224909):ℝ):ℂ) + ((0.0504691035014:ℝ):ℂ) * I)‖ ≤ 0.00000012619 := by
  have hl := lg_14
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.023936252804587596 66.023936290331637632 3.0911021 0.00000002618 (-0.9987256224909) 0.0504691035014 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_15 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2043091579178:ℝ):ℂ) + ((0.9789064143169:ℝ):ℂ) * I)‖ ≤ 0.00000016733 := by
  have hl := lg_15
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.749999911665127714 67.74999994919217775 1.3650384 0.00000006732 0.2043091579178 0.9789064143169 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_16 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9690146898121:ℝ):ℂ) + (((-0.2470030990258):ℝ):ℂ) * I)‖ ≤ 0.00000015201 := by
  have hl := lg_16
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.3646246269816 69.3646246770176 (-0.2495863) 0.000000052 0.9690146898121 (-0.2470030990258) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_17 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1942538692284):ℝ):ℂ) + (((-0.9809512904772):ℝ):ℂ) * I)‖ ≤ 0.00000016341 := by
  have hl := lg_17
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.881331415585145812 70.88133146562117083 (-1.7662931) 0.0000000634 (-0.1942538692284) (-0.9809512904772) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_18 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.998504893333):ℝ):ℂ) + ((0.0546623949969:ℝ):ℂ) * I)‖ ≤ 0.00000016663 := by
  have hl := lg_18
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.311320619536293904 72.31132065706334394 3.086903 0.00000006662 (-0.998504893333) 0.0546623949969 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_19 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1627261194207):ℝ):ℂ) + ((0.9866712776085:ℝ):ℂ) * I)‖ ≤ 0.00000012489 := by
  have hl := lg_19
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.663974361276033854 73.663974398803108908 1.7342493 0.00000002488 (-0.1627261194207) 0.9866712776085 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_20 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.900014432604:ℝ):ℂ) + ((0.4358600934985:ℝ):ℂ) * I)‖ ≤ 0.00000015766 := by
  have hl := lg_20
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.947229993760480762 74.94723004379650578 0.4509937 0.00000005765 0.900014432604 0.4358600934985 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_21 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.71816213641:ℝ):ℂ) + (((-0.6958758120721):ℝ):ℂ) * I)‖ ≤ 0.00000015872 := by
  have hl := lg_21
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.167862327454634548 76.167862364981709602 (-0.7696387) 0.00000005871 0.71816213641 (-0.6958758120721) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_22 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3547812371168):ℝ):ℂ) + (((-0.9349493428991):ℝ):ℂ) * I)‖ ≤ 0.000000136 := by
  have hl := lg_22
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.331700072105058594 77.33170012214110863 (-1.9334764) 0.00000003599 (-0.3547812371168) (-0.9349493428991) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_23 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9953934235):ℝ):ℂ) + (((-0.0958745637276):ℝ):ℂ) * I)‖ ≤ 0.000000132 := by
  have hl := lg_23
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.443794268102158588 78.443794318138233642 (-3.0455706) 0.00000003199 (-0.9953934235) (-0.0958745637276) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_24 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5663430917575):ℝ):ℂ) + ((0.8241695835257:ℝ):ℂ) * I)‖ ≤ 0.00000015835 := by
  have hl := lg_24
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.508550701631646952 79.50855075166767197 2.1728583 0.00000005834 (-0.5663430917575) 0.8241695835257 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_25 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4070506103889:ℝ):ℂ) + ((0.9134056057317:ℝ):ℂ) * I)‖ ≤ 0.00000013281 := by
  have hl := lg_25
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.529835360539361524 80.52983541057541156 1.1515736 0.0000000328 0.4070506103889 0.9134056057317 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_26 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.985525526627:ℝ):ℂ) + ((0.1695270962609:ℝ):ℂ) * I)‖ ≤ 0.00000013114 := by
  have hl := lg_26
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.5110591622081706 81.511059212244220636 0.1703498 0.00000003113 0.985525526627 0.1695270962609 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_27 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7152338312968:ℝ):ℂ) + (((-0.6988852313281):ℝ):ℂ) * I)‖ ≤ 0.00000013839 := by
  have hl := lg_27
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.455246694186340856 82.45524673171341591 (-0.7738377) 0.00000003838 0.7152338312968 (-0.6988852313281) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_28 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.112647463357):ℝ):ℂ) + (((-0.9936350180015):ℝ):ℂ) * I)‖ ≤ 0.00000016627 := by
  have hl := lg_28
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.365092409549987596 83.365092459586037632 (-1.6836834) 0.00000006626 (-0.112647463357) (-0.9936350180015) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_29 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8364656346505):ℝ):ℂ) + (((-0.5480193810285):ℝ):ℂ) * I)‖ ≤ 0.00000014476 := by
  have hl := lg_29
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.243007048588340456 84.24300709862441551 (-2.5615981) 0.00000004475 (-0.8364656346505) (-0.5480193810285) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_30 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9642615199165):ℝ):ℂ) + ((0.2649522994051:ℝ):ℂ) * I)‖ ≤ 0.00000013212 := by
  have hl := lg_30
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.091156068410527714 85.09115611844657775 2.8734382 0.00000003211 (-0.9642615199165) 0.2649522994051 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_31 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4638234210888):ℝ):ℂ) + ((0.8859276686302:ℝ):ℂ) * I)‖ ≤ 0.00000014473 := by
  have hl := lg_31
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.911491855796091534 85.911491905832166588 2.0531024 0.00000004472 (-0.4638234210888) 0.8859276686302 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_32 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3069463480417:ℝ):ℂ) + ((0.951726819746:ℝ):ℂ) * I)‖ ≤ 0.00000014577 := by
  have hl := lg_32
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.705780783727 86.705780846272 1.2588135 0.00000004576 0.3069463480417 0.951726819746 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_33 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8828180276162:ℝ):ℂ) + ((0.4697151584906:ℝ):ℂ) * I)‖ ≤ 0.00000015377 := by
  have hl := lg_33
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.475626146755105546 87.4756261967911806 0.4889681 0.00000005376 0.8828180276162 0.4697151584906 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_34 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9669294248247:ℝ):ℂ) + (((-0.2550440891459):ℝ):ℂ) * I)‖ ≤ 0.00000013438 := by
  have hl := lg_34
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.222487572330545812 88.22248763487557083 (-0.2578933) 0.00000003437 0.9669294248247 (-0.2550440891459) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_35 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5544424197761:ℝ):ℂ) + (((-0.8322220876381):ℝ):ℂ) * I)‖ ≤ 0.00000012587 := by
  have hl := lg_35
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.947697776328868358 88.947697826364943412 (-0.9831035) 0.00000002586 0.5544424197761 (-0.8322220876381) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_36 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1168188307761):ℝ):ℂ) + (((-0.9931532413357):ℝ):ℂ) * I)‖ ≤ 0.00000012582 := by
  have hl := lg_36
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.652476776281693904 89.65247682631774394 (-1.6878825) 0.00000002581 (-0.1168188307761) (-0.9931532413357) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_37 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7191329111905):ℝ):ℂ) + (((-0.694872546598):ℝ):ℂ) * I)‖ ≤ 0.00000016206 := by
  have hl := lg_37
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.337944312519929956 90.33794436255600501 (-2.37335) 0.00000006205 (-0.7191329111905) (-0.694872546598) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_38 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9948981404515):ℝ):ℂ) + (((-0.1008845362386):ℝ):ℂ) * I)‖ ≤ 0.00000016756 := by
  have hl := lg_38
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 91.005130518021433854 91.005130568057508908 (-3.0405362) 0.00000006755 (-0.9948981404515) (-0.1008845362386) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_39 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8531519916187):ℝ):ℂ) + ((0.5216624187357:ℝ):ℂ) * I)‖ ≤ 0.00000017085 := by
  have hl := lg_39
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.654985236858217552 91.654985286894292606 2.5927943 0.00000007084 (-0.8531519916187) 0.5216624187357 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_40 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.378890461702):ℝ):ℂ) + ((0.9254415259909:ℝ):ℂ) * I)‖ ≤ 0.0000001572 := by
  have hl := lg_40
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.288386150505880762 92.28838621305090578 1.9593934 0.00000005719 (-0.378890461702) 0.9254415259909 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_41 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2271622189381:ℝ):ℂ) + ((0.973856933172:ℝ):ℂ) * I)‖ ≤ 0.00000017542 := by
  have hl := lg_41
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.90614593229178244 92.906145994836832476 1.3416336 0.00000007541 0.2271622189381 0.973856933172 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_42 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7393033670819:ℝ):ℂ) + ((0.6733725056916:ℝ):ℂ) * I)‖ ≤ 0.00000012656 := by
  have hl := lg_42
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.509018484200034548 93.509018534236109602 0.7387611 0.00000002655 0.7393033670819 0.6733725056916 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_43 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.988759852344:ℝ):ℂ) + ((0.1495123887601:ℝ):ℂ) * I)‖ ≤ 0.0000001393 := by
  have hl := lg_43
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.09770446840826804 94.097704518444368112 0.1500751 0.00000003929 0.988759852344 0.1495123887601 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_44 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9110071052703:ℝ):ℂ) + (((-0.4123906572014):ℝ):ℂ) * I)‖ ≤ 0.00000017886 := by
  have hl := lg_44
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.672856228850458594 94.67285629139550863 (-0.4250767) 0.00000007885 0.9110071052703 (-0.4123906572014) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_45 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5509429581982:ℝ):ℂ) + (((-0.8345429029186):ℝ):ℂ) * I)‖ ≤ 0.00000016465 := by
  have hl := lg_45
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.235082143060574666 95.23508219309664972 (-0.9873026) 0.00000006464 0.5509429581982 (-0.8345429029186) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_46 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0336191905568:ℝ):ℂ) + (((-0.9994347152396):ℝ):ℂ) * I)‖ ≤ 0.00000017971 := by
  have hl := lg_46
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.784950424847558588 95.784950487392633642 (-1.5371708) 0.0000000797 0.0336191905568 (-0.9994347152396) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_47 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4832969328647):ℝ):ℂ) + (((-0.875456495023):ℝ):ℂ) * I)‖ ≤ 0.00000014064 := by
  have hl := lg_47
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.322992667065610922 96.322992729610710994 (-2.0752131) 0.00000004063 (-0.4832969328647) (-0.875456495023) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_48 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.857880687078):ℝ):ℂ) + (((-0.5138489336952):ℝ):ℂ) * I)‖ ≤ 0.00000014933 := by
  have hl := lg_48
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.849706858377046952 96.84970692092207197 (-2.6019273) 0.00000004932 (-0.857880687078) (-0.5138489336952) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_49 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.999716506139):ℝ):ℂ) + (((-0.0238098030756):ℝ):ℂ) * I)‖ ≤ 0.00000013448 := by
  have hl := lg_49
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.365560192118375192 97.365560242154475264 (-3.1177806) 0.00000003447 (-0.999716506139) (-0.0238098030756) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_50 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8862460226476):ℝ):ℂ) + ((0.463214839183:ℝ):ℂ) * I)‖ ≤ 0.00000016497 := by
  have hl := lg_50
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.870991517284761524 97.87099157982981156 2.6599734 0.00000006496 (-0.8862460226476) 0.463214839183 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_51 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5594771703889):ℝ):ℂ) + ((0.8288457611669:ℝ):ℂ) * I)‖ ≤ 0.00000016791 := by
  have hl := lg_51
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.366413646980592764 98.3664137095256428 2.1645512 0.0000000679 (-0.5594771703889) 0.8288457611669 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_52 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1077437157434):ℝ):ℂ) + ((0.9941787021041:ℝ):ℂ) * I)‖ ≤ 0.00000016664 := by
  have hl := lg_52
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.8522153189535706 98.852215381498620636 1.6787496 0.00000006663 (-0.1077437157434) 0.9941787021041 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_53 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3603047141344:ℝ):ℂ) + ((0.9328346654003:ℝ):ℂ) * I)‖ ≤ 0.00000015416 := by
  have hl := lg_53
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.328763060730393092 99.328763123275468146 1.2022018 0.00000005415 0.3603047141344 0.9328346654003 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_54 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7421243994092:ℝ):ℂ) + ((0.6702621694542:ℝ):ℂ) * I)‖ ≤ 0.00000016396 := by
  have hl := lg_54
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.796402850931740856 99.79640290096781591 0.734562 0.00000006395 0.7421243994092 0.6702621694542 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_55 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9622884061642:ℝ):ℂ) + ((0.2720312911447:ℝ):ℂ) * I)‖ ≤ 0.00000014332 := by
  have hl := lg_55
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.255461595629339356 100.25546165817441441 0.2755033 0.00000004331 0.9622884061642 0.2720312911447 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_56 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9846771047988:ℝ):ℂ) + (((-0.1743874975023):ℝ):ℂ) * I)‖ ≤ 0.00000014859 := by
  have hl := lg_56
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.706248566295387596 100.706248628840437632 (-0.1752837) 0.00000004858 0.9846771047988 (-0.1743874975023) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_57 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8149857634734:ℝ):ℂ) + (((-0.57948097927):ℝ):ℂ) * I)‖ ≤ 0.00000012785 := by
  have hl := lg_57
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.149056592671480806 101.149056642707580878 (-0.6180917) 0.00000002784 0.8149857634734 (-0.57948097927) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_58 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4947942280635:ℝ):ℂ) + (((-0.8690101678778):ℝ):ℂ) * I)‖ ≤ 0.00000015302 := by
  have hl := lg_58
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.584163205333740456 101.58416326787881551 (-1.0531983) 0.00000005301 0.4947942280635 (-0.8690101678778) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_59 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0898082613977:ℝ):ℂ) + (((-0.995959073549):ℝ):ℂ) * I)‖ ≤ 0.00000017577 := by
  have hl := lg_59
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.011831739116707856 102.011831801661807928 (-1.4808669) 0.00000007576 0.0898082613977 (-0.995959073549) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_60 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3245642231657):ℝ):ℂ) + (((-0.9458636609146):ℝ):ℂ) * I)‖ ≤ 0.00000017284 := by
  have hl := lg_60
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.432312225155927714 102.43231228770097775 (-1.9013473) 0.00000007283 (-0.3245642231657) (-0.9458636609146) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_61 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6772960323296):ℝ):ℂ) + (((-0.7357105983811):ℝ):ℂ) * I)‖ ≤ 0.00000014906 := by
  have hl := lg_61
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.845842301371299494 102.845842363916374548 (-2.3148774) 0.00000004905 (-0.6772960323296) (-0.7357105983811) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_62 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9131258170057):ℝ):ℂ) + (((-0.4076778657038):ℝ):ℂ) * I)‖ ≤ 0.00000016023 := by
  have hl := lg_62
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.252648012541491534 103.252648075086566588 (-2.7216831) 0.00000006022 (-0.9131258170057) (-0.4076778657038) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_63 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998076718764):ℝ):ℂ) + (((-0.0196116959142):ℝ):ℂ) * I)‖ ≤ 0.00000015604 := by
  have hl := lg_63
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.6529445588500815 103.652944608886181572 (-3.1219797) 0.00000005603 (-0.9998076718764) (-0.0196116959142) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_64 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9307347317888):ℝ):ℂ) + ((0.3656950353519:ℝ):ℂ) * I)‖ ≤ 0.0000001816 := by
  have hl := lg_64
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.0469369404724 104.0469370155264 2.7672132 0.00000008159 (-0.9307347317888) 0.3656950353519 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_65 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7232750207711):ℝ):ℂ) + ((0.6905600946338:ℝ):ℂ) * I)‖ ≤ 0.00000013634 := by
  have hl := lg_65
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.434820685732451362 104.434820748277526416 2.3793295 0.00000003633 (-0.7232750207711) 0.6905600946338 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_66 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4137520360321):ℝ):ℂ) + ((0.9103896158655:ℝ):ℂ) * I)‖ ≤ 0.00000014401 := by
  have hl := lg_66
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.816782303500505546 104.8167823660455806 1.9973679 0.000000044 (-0.4137520360321) 0.9103896158655 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_67 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.050332696963):ℝ):ℂ) + ((0.9987325065382:ℝ):ℂ) * I)‖ ≤ 0.00000015991 := by
  have hl := lg_67
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.192999919406567266 105.192999981951667338 1.6211503 0.0000000599 (-0.050332696963) 0.9987325065382 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_68 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3148416612594:ℝ):ℂ) + ((0.949144208398:ℝ):ℂ) * I)‖ ≤ 0.00000018209 := by
  have hl := lg_68
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.563643729075945812 105.56364380412997083 1.2505065 0.00000008208 0.3148416612594 0.949144208398 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_69 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6330776572387:ℝ):ℂ) + ((0.7740882894768:ℝ):ℂ) * I)‖ ≤ 0.00000014 := by
  have hl := lg_69
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.92887649949760554 105.928876562042705612 0.8852737 0.00000003999 0.6330776572387 0.7740882894768 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_70 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8651753942268:ℝ):ℂ) + ((0.5014693781523:ℝ):ℂ) * I)‖ ≤ 0.00000017358 := by
  have hl := lg_70
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.288853933074268358 106.288853995619343412 0.5252963 0.00000007357 0.8651753942268 0.5014693781523 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_71 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9855127584426:ℝ):ℂ) + ((0.1696013058523:ℝ):ℂ) * I)‖ ≤ 0.00000017181 := by
  have hl := lg_71
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.643725131303023566 106.643725193848123638 0.1704251 0.0000000718 0.9855127584426 0.1696013058523 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_72 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9839361731444:ℝ):ℂ) + (((-0.1785206071522):ℝ):ℂ) * I)‖ ≤ 0.00000017353 := by
  have hl := lg_72
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.993632933027093904 106.99363299557214394 (-0.1794827) 0.00000007352 0.9839361731444 (-0.1785206071522) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_73 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8655423381552:ℝ):ℂ) + (((-0.5008357623621):ℝ):ℂ) * I)‖ ≤ 0.00000015593 := by
  have hl := lg_73
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.338714266133850934 107.338714328678925988 (-0.5245641) 0.00000005592 0.8655423381552 (-0.5008357623621) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_74 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6486779413201:ℝ):ℂ) + (((-0.7610630252776):ℝ):ℂ) * I)‖ ≤ 0.0000001528 := by
  have hl := lg_74
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.679100469265329956 107.67910053181040501 (-0.8649503) 0.00000005279 0.6486779413201 (-0.7610630252776) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_75 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3616424010556:ℝ):ℂ) + (((-0.9323168848405):ℝ):ℂ) * I)‖ ≤ 0.00000013244 := by
  have hl := lg_75
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.014917591934808476 108.01491765447988353 (-1.2007674) 0.00000003243 0.3616424010556 (-0.9323168848405) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_76 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0386501974663:ℝ):ℂ) + (((-0.9992528019654):ℝ):ℂ) * I)‖ ≤ 0.0000001473 := by
  have hl := lg_76
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.346286674766833854 108.346286737311908908 (-1.5321365) 0.00000004729 0.0386501974663 (-0.9992528019654) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_77 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2843970730252):ℝ):ℂ) + (((-0.9587065791227):ℝ):ℂ) * I)‖ ≤ 0.00000015193 := by
  have hl := lg_77
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.67332401141884619 108.673324073963946262 (-1.8591738) 0.00000005192 (-0.2843970730252) (-0.9587065791227) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_78 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5738464263733):ℝ):ℂ) + (((-0.8189629289098):ℝ):ℂ) * I)‖ ≤ 0.00000013411 := by
  have hl := lg_78
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.996141393603617552 108.996141456148692606 (-2.1819912) 0.0000000341 (-0.5738464263733) (-0.8189629289098) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_79 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8015600178634):ℝ):ℂ) + (((-0.5979143230539):ℝ):ℂ) * I)‖ ≤ 0.00000018101 := by
  have hl := lg_79
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 109.314846340503336274 109.314846403048436346 (-2.5006961) 0.000000081 (-0.8015600178634) (-0.5979143230539) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p018_80 : ‖exp (-((((((25018:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9472666961906):ℝ):ℂ) + (((-0.3204462608486):ℝ):ℂ) * I)‖ ≤ 0.00000016027 := by
  have hl := lg_80
  refine (ecis_approx ((((25018:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 109.629542307251280762 109.62954238230530578 (-2.8153921) 0.00000006026 (-0.9472666961906) (-0.3204462608486) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_2 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0906908449477:ℝ):ℂ) + ((0.9958790943898:ℝ):ℂ) * I)‖ ≤ 0.00000013042 := by
  have hl := lg_2
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.3695751911377 17.3695752036672 1.4799807 0.00000003041 0.0906908449477 0.9958790943898 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_3 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7356242504512):ℝ):ℂ) + (((-0.6773898154812):ℝ):ℂ) * I)‖ ≤ 0.00000011905 := by
  have hl := lg_3
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.530125335220181676 27.530125347749706735 (-2.3973841) 0.00000001904 (-0.7356242504512) (-0.6773898154812) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_4 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9835503411395):ℝ):ℂ) + ((0.1806342329009:ℝ):ℂ) * I)‖ ≤ 0.00000016082 := by
  have hl := lg_4
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.7391503822754 34.7391504073344 2.9599614 0.00000006081 (-0.9835503411395) 0.1806342329009 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_5 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8728421970641):ℝ):ℂ) + (((-0.4880025603767):ℝ):ℂ) * I)‖ ≤ 0.00000011665 := by
  have hl := lg_5
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.330904634658163331 40.33090465971718839 (-2.6317928) 0.00000001664 (-0.8728421970641) (-0.4880025603767) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_6 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6078839711696:ℝ):ℂ) + (((-0.7940258670819):ℝ):ℂ) * I)‖ ≤ 0.00000012391 := by
  have hl := lg_6
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.899700526357881676 44.899700551416906735 (-0.9174034) 0.0000000239 0.6078839711696 (-0.7940258670819) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_7 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0678242188793:ℝ):ℂ) + ((0.9976972864217:ℝ):ℂ) * I)‖ ≤ 0.0000001453 := by
  have hl := lg_7
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.762562412149139898 48.762562437208190016 1.50292 0.00000004529 0.0678242188793 0.9976972864217 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_8 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2690887647211):ℝ):ℂ) + (((-0.9631153807823):ℝ):ℂ) * I)‖ ≤ 0.00000015358 := by
  have hl := lg_8
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.1087255734131 52.1087256110016 (-1.8432431) 0.00000005357 (-0.2690887647211) (-0.9631153807823) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_9 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0822860828732:ℝ):ℂ) + ((0.9966087499943:ℝ):ℂ) * I)‖ ≤ 0.0000001309 := by
  have hl := lg_9
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.060250670440363352 55.06025069549941347 1.4884171 0.00000003089 0.0822860828732 0.9966087499943 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_10 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.406832751577:ℝ):ℂ) + (((-0.913502661323):ℝ):ℂ) * I)‖ ≤ 0.00000013884 := by
  have hl := lg_10
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.700479825795863331 57.70047986338438839 (-1.1518121) 0.00000003883 0.406832751577 (-0.913502661323) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_11 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9216063427746):ℝ):ℂ) + ((0.3881259445234:ℝ):ℂ) * I)‖ ≤ 0.0000001503 := by
  have hl := lg_11
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.088857621512418447 60.088857659100968565 2.7429954 0.00000005029 (-0.9216063427746) 0.3881259445234 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_12 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8458832724071:ℝ):ℂ) + ((0.5333680619064:ℝ):ℂ) * I)‖ ≤ 0.00000015432 := by
  have hl := lg_12
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.269275717495581676 62.269275755084106735 0.5625773 0.00000005431 0.8458832724071 0.5333680619064 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_13 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1272375845281:ℝ):ℂ) + (((-0.9918722685323):ℝ):ℂ) * I)‖ ≤ 0.00000014272 := by
  have hl := lg_13
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.2750659290867203 64.275065966675270418 (-1.4432129) 0.00000004271 0.1272375845281 (-0.9918722685323) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_14 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9874348499982):ℝ):ℂ) + ((0.1580266326546:ℝ):ℂ) * I)‖ ≤ 0.00000016191 := by
  have hl := lg_14
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.132137603286839898 66.132137640875390016 2.9829008 0.0000000619 (-0.9874348499982) 0.1580266326546 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_15 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.311515929452:ℝ):ℂ) + ((0.9502409303422:ℝ):ℂ) * I)‖ ≤ 0.00000012851 := by
  have hl := lg_15
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.861029969878345007 67.861030007466895125 1.2540084 0.0000000285 0.311515929452 0.9502409303422 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_16 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9347425857687:ℝ):ℂ) + (((-0.3553256229862):ℝ):ℂ) * I)‖ ≤ 0.00000013571 := by
  have hl := lg_16
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.4783007645508 69.4783008146688 (-0.3632624) 0.0000000357 0.9347425857687 (-0.3553256229862) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_17 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3066376358906):ℝ):ℂ) + (((-0.9518263288298):ℝ):ℂ) * I)‖ ≤ 0.00000013381 := by
  have hl := lg_17
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.997493162648819606 70.997493212766844665 (-1.8824548) 0.0000000338 (-0.3066376358906) (-0.9518263288298) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_18 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9850392248701):ℝ):ℂ) + ((0.1723302791359:ℝ):ℂ) * I)‖ ≤ 0.00000012459 := by
  have hl := lg_18
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.429825861578063352 72.42982589916661347 2.9683978 0.00000002458 (-0.9850392248701) 0.1723302791359 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_19 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0427179703881):ℝ):ℂ) + ((0.9990871708743:ℝ):ℂ) * I)‖ ≤ 0.00000012678 := by
  have hl := lg_19
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.784696359389884577 73.784696396978459754 1.6135273 0.00000002677 (-0.0427179703881) 0.9990871708743 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_20 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.946634209074:ℝ):ℂ) + ((0.3223099039912:ℝ):ℂ) * I)‖ ≤ 0.00000016924 := by
  have hl := lg_20
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.070055016933563331 75.07005506705158839 0.3281686 0.00000006923 0.946634209074 0.3223099039912 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_21 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6259368405967:ℝ):ℂ) + (((-0.779873753619):ℝ):ℂ) * I)‖ ≤ 0.0000001388 := by
  have hl := lg_21
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.292687747369321574 76.292687784957896751 (-0.8944641) 0.00000003879 0.6259368405967 (-0.779873753619) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_22 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.470107765821):ℝ):ℂ) + (((-0.8826090235827):ℝ):ℂ) * I)‖ ≤ 0.00000017352 := by
  have hl := lg_22
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.458432812650118447 77.458432862768168565 (-2.0602092) 0.00000007351 (-0.470107765821) (-0.8826090235827) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_23 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9994708400837):ℝ):ℂ) + ((0.0325275146829:ℝ):ℂ) * I)‖ ≤ 0.00000016244 := by
  have hl := lg_23
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.572349530912622594 78.572349581030697771 3.1090594 0.00000006243 (-0.9994708400837) 0.0325275146829 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_24 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.454456322843):ℝ):ℂ) + ((0.8907690220385:ℝ):ℂ) * I)‖ ≤ 0.00000016543 := by
  have hl := lg_24
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.638850908633281676 79.638850958751306735 2.0425581 0.00000006542 (-0.454456322843) 0.8907690220385 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_25 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5237070081516:ℝ):ℂ) + ((0.8518984502937:ℝ):ℂ) * I)‖ ≤ 0.00000012611 := by
  have hl := lg_25
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.661809269316326662 80.66180931943437678 1.0195997 0.0000000261 0.5237070081516 0.8518984502937 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_26 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9993241405863:ℝ):ℂ) + ((0.0367595163388:ℝ):ℂ) * I)‖ ≤ 0.00000017313 := by
  have hl := lg_26
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.6446411202244203 81.644641170342470418 0.0367678 0.00000007312 0.9993241405863 0.0367595163388 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_27 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6145609792462:ℝ):ℂ) + (((-0.7888693192081):ℝ):ℂ) * I)‖ ≤ 0.00000014993 := by
  have hl := lg_27
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.590376005660545028 82.590376043249120205 (-0.908967) 0.00000004992 0.6145609792462 (-0.7888693192081) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_28 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2469267139364):ℝ):ℂ) + (((-0.9690341572635):ℝ):ℂ) * I)‖ ≤ 0.00000015122 := by
  have hl := lg_28
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.501712794424539898 83.501712844542590016 (-1.8203038) 0.00000005121 (-0.2469267139364) (-0.9690341572635) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_29 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9039255830413):ℝ):ℂ) + (((-0.4276897709818):ℝ):ℂ) * I)‖ ≤ 0.00000013437 := by
  have hl := lg_29
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.381066177575154828 84.381066227693230005 (-2.6996572) 0.00000003436 (-0.9039255830413) (-0.4276897709818) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_30 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9180734342607):ℝ):ℂ) + ((0.3964103545126:ℝ):ℂ) * I)‖ ≤ 0.00000013951 := by
  have hl := lg_30
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.230605161016045007 85.230605211134095125 2.7339891 0.0000000395 (-0.9180734342607) 0.3964103545126 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_31 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3349126955545):ℝ):ℂ) + ((0.9422491636262:ℝ):ℂ) * I)‖ ≤ 0.00000016939 := by
  have hl := lg_31
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.052285331137351417 86.052285381255426594 1.9123089 0.00000006938 (-0.3349126955545) 0.9422491636262 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_32 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4386339545449:ℝ):ℂ) + ((0.8986658188227:ℝ):ℂ) * I)‖ ≤ 0.00000014484 := by
  have hl := lg_32
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.8478759556885 86.847876018336 1.1167183 0.00000004483 0.4386339545449 0.8986658188227 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_33 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9408685371564:ℝ):ℂ) + ((0.3387718934462:ℝ):ℂ) * I)‖ ≤ 0.0000001438 := by
  have hl := lg_33
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.618982956732600123 87.6189830068506753 0.3456113 0.00000004379 0.9408685371564 0.3387718934462 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_34 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9200947160807:ℝ):ℂ) + (((-0.3916959451416):ℝ):ℂ) * I)‖ ≤ 0.00000014674 := by
  have hl := lg_34
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.367068353786519606 88.367068416434044665 (-0.4024741) 0.00000004673 0.9200947160807 (-0.3916959451416) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_35 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4276789900815:ℝ):ℂ) + (((-0.9039306839813):ℝ):ℂ) * I)‖ ≤ 0.00000015372 := by
  have hl := lg_35
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.093467046807303229 89.093467096925378406 (-1.1288728) 0.00000005371 0.4276789900815 (-0.9039306839813) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_36 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2609541551904):ℝ):ℂ) + (((-0.9653511945855):ℝ):ℂ) * I)‖ ≤ 0.00000014781 := by
  have hl := lg_36
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.799401052715763352 89.79940110283381347 (-1.8348068) 0.0000000478 (-0.2609541551904) (-0.9653511945855) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_37 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8137651662946):ℝ):ℂ) + (((-0.5811938179908):ℝ):ℂ) * I)‖ ≤ 0.00000015363 := by
  have hl := lg_37
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.485991946895712078 90.485991997013787255 (-2.5213977) 0.00000005362 (-0.8137651662946) (-0.5811938179908) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_38 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9988441554997):ℝ):ℂ) + ((0.0480661257753:ℝ):ℂ) * I)‖ ≤ 0.00000015718 := by
  have hl := lg_38
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.154271550527584577 91.154271600645659754 3.093508 0.00000005717 (-0.9988441554997) 0.0480661257753 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_39 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7654832211009):ℝ):ℂ) + ((0.6434558556537:ℝ):ℂ) * I)‖ ≤ 0.0000001434 := by
  have hl := lg_39
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.805191264306901976 91.805191314424977153 2.4425883 0.00000004339 (-0.7654832211009) 0.6434558556537 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_40 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2351307362188):ℝ):ℂ) + ((0.9719637528653:ℝ):ℂ) * I)‖ ≤ 0.00000016304 := by
  have hl := lg_40
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.439630208071263331 92.43963027071878839 1.8081494 0.00000006303 (-0.2351307362188) 0.9719637528653 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_41 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3722379883363:ℝ):ℂ) + ((0.9281373174479:ℝ):ℂ) * I)‖ ≤ 0.00000014194 := by
  have hl := lg_41
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.05840238697337022 93.058402449620920338 1.1893772 0.00000004193 0.3722379883363 0.9281373174479 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_42 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8334267084501:ℝ):ℂ) + ((0.5526300042904:ℝ):ℂ) * I)‖ ≤ 0.0000001692 := by
  have hl := lg_42
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.662262938507021574 93.662262988625096751 0.5855166 0.00000006919 0.8334267084501 0.5526300042904 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_43 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999914546208:ℝ):ℂ) + (((-0.0041340882242):ℝ):ℂ) * I)‖ ≤ 0.0000001346 := by
  have hl := lg_43
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.25191367310907302 94.251913723227173256 (-0.0041341) 0.00000003459 0.9999914546208 (-0.0041340882242) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_44 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8363374594314:ℝ):ℂ) + (((-0.5482149705652):ℝ):ℂ) * I)‖ ≤ 0.00000015876 := by
  have hl := lg_44
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.828008003787818447 94.828008066435368565 (-0.5802284) 0.00000005875 0.8363374594314 (-0.5482149705652) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_45 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4145248563754:ℝ):ℂ) + (((-0.9100379901119):ℝ):ℂ) * I)‖ ≤ 0.00000014754 := by
  have hl := lg_45
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.391155305098526683 95.39115535521660186 (-1.1433757) 0.00000004753 0.4145248563754 (-0.9100379901119) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_46 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1230362207899):ℝ):ℂ) + (((-0.992402180758):ℝ):ℂ) * I)‖ ≤ 0.00000017702 := by
  have hl := lg_46
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.941924722050322594 95.941924784697897771 (-1.6941451) 0.00000007701 (-0.1230362207899) (-0.992402180758) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_47 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6149107400763):ℝ):ℂ) + (((-0.7885967167859):ℝ):ℂ) * I)‖ ≤ 0.00000017365 := by
  have hl := lg_47
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.480848718682434411 96.480848781330034647 (-2.2330691) 0.00000007364 (-0.6149107400763) (-0.7885967167859) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_48 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9283132721707):ℝ):ℂ) + (((-0.3717989625524):ℝ):ℂ) * I)‖ ≤ 0.00000015474 := by
  have hl := lg_48
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.008426099770981676 97.008426162418506735 (-2.7606465) 0.00000005473 (-0.9283132721707) (-0.3717989625524) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_49 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9907997640178):ℝ):ℂ) + ((0.1353359789797:ℝ):ℂ) * I)‖ ≤ 0.00000015956 := by
  have hl := lg_49
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.525124824298279796 97.525124874416380032 3.0058401 0.00000005955 (-0.9907997640178) 0.1353359789797 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_50 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8008924261061):ℝ):ℂ) + ((0.5988082512427:ℝ):ℂ) * I)‖ ≤ 0.00000015443 := by
  have hl := lg_50
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.031384460454026662 98.03138452310157678 2.4995804 0.00000005442 (-0.8008924261061) 0.5988082512427 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_51 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4191873736914):ℝ):ℂ) + ((0.9078997443187:ℝ):ℂ) * I)‖ ≤ 0.00000014566 := by
  have hl := lg_51
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.527618497869001282 98.5276185605165514 2.0033464 0.00000004565 (-0.4191873736914) 0.9078997443187 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_52 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0540214169907:ℝ):ℂ) + ((0.9985397771277:ℝ):ℂ) * I)‖ ≤ 0.00000015915 := by
  have hl := lg_52
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.0142163113621203 99.014216374009670418 1.5167486 0.00000005914 0.0540214169907 0.9985397771277 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_53 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5067204527213:ℝ):ℂ) + ((0.8621104237822:ℝ):ℂ) * I)‖ ≤ 0.00000017692 := by
  have hl := lg_53
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.491545029132741246 99.491545091780316423 1.0394199 0.00000007691 0.5067204527213 0.8621104237822 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_54 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8413535176847:ℝ):ℂ) + ((0.5404852063467:ℝ):ℂ) * I)‖ ≤ 0.00000013206 := by
  have hl := lg_54
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.959951196798245028 99.959951246916320205 0.5710137 0.00000003205 0.8413535176847 0.5404852063467 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_55 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9938233598511:ℝ):ℂ) + ((0.1109735527692:ℝ):ℂ) * I)‖ ≤ 0.00000015872 := by
  have hl := lg_55
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.419762256170581778 100.419762318818156955 0.1112026 0.00000005871 0.9938233598511 0.1109735527692 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_56 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.942646866642:ℝ):ℂ) + (((-0.333791678761):ℝ):ℂ) * I)‖ ≤ 0.00000013335 := by
  have hl := lg_56
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.871287985562239898 100.871288048209790016 (-0.3403231) 0.00000003334 0.942646866642 (-0.333791678761) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_57 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7081958492932:ℝ):ℂ) + (((-0.7060160331351):ℝ):ℂ) * I)‖ ≤ 0.00000012987 := by
  have hl := lg_57
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.314821694610066253 101.314821744728166489 (-0.7838568) 0.00000002986 0.7081958492932 (-0.7060160331351) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_58 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3439495269709:ℝ):ℂ) + (((-0.9389881377826):ℝ):ℂ) * I)‖ ≤ 0.00000014618 := by
  have hl := lg_58
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.750641368712854828 101.750641431360430005 (-1.2196765) 0.00000004617 0.3439495269709 (-0.9389881377826) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_59 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0771727650326):ℝ):ℂ) + (((-0.9970177352168):ℝ):ℂ) * I)‖ ≤ 0.00000014062 := by
  have hl := lg_59
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.179010774263553528 102.179010836911153764 (-1.6480459) 0.00000004061 (-0.0771727650326) (-0.9970177352168) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p059_60 : ‖exp (-((((((25059:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4780376341081):ℝ):ℂ) + (((-0.8783393537642):ℝ):ℂ) * I)‖ ≤ 0.00000016273 := by
  have hl := lg_60
  refine (ecis_approx ((((25059:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.600180352153745007 102.600180414801295125 (-2.0692155) 0.00000006272 (-0.4780376341081) (-0.8783393537642) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_2 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1189523031719:ℝ):ℂ) + ((0.9928999695689:ℝ):ℂ) * I)‖ ≤ 0.00000011656 := by
  have hl := lg_2
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.39799422553 17.39799423808 1.4515617 0.00000001655 0.1189523031719 0.9928999695689 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_3 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7653795504296):ℝ):ℂ) + (((-0.6435791666503):ℝ):ℂ) * I)‖ ≤ 0.00000012289 := by
  have hl := lg_3
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.5751684390449164 27.5751684515949415 (-2.4424272) 0.00000002288 (-0.7653795504296) (-0.6435791666503) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_4 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9717006990306):ℝ):ℂ) + ((0.2362154762587:ℝ):ℂ) * I)‖ ≤ 0.0000001331 := by
  have hl := lg_4
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.79598845106 34.79598847616 2.9031234 0.00000003309 (-0.9717006990306) 0.2362154762587 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_5 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9031210457357):ℝ):ℂ) + (((-0.429386046151):ℝ):ℂ) * I)‖ ≤ 0.00000015405 := by
  have hl := lg_5
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.3968915890466459 40.396891614146671 (-2.6977798) 0.00000005404 (-0.9031210457357) (-0.429386046151) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_6 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5479660746783:ℝ):ℂ) + (((-0.8365005564861):ℝ):ℂ) * I)‖ ≤ 0.00000013943 := by
  have hl := lg_6
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.9731626645749164 44.9731626896749415 (-0.9908655) 0.00000003942 0.5479660746783 (-0.8365005564861) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_7 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1471226428691:ℝ):ℂ) + ((0.9891182578212:ℝ):ℂ) * I)‖ ≤ 0.00000012921 := by
  have hl := lg_7
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.8423447282390922 48.8423447533391424 1.4231377 0.0000000292 0.1471226428691 0.9891182578212 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_8 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.35012436876):ℝ):ℂ) + (((-0.9367032221563):ℝ):ℂ) * I)‖ ≤ 0.00000015682 := by
  have hl := lg_8
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.19398267659 52.19398271424 (-1.9285002) 0.00000005681 (-0.35012436876) (-0.9367032221563) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_9 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1716117195256:ℝ):ℂ) + ((0.9851646652826:ℝ):ℂ) * I)‖ ≤ 0.00000013859 := by
  have hl := lg_9
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.1503368780898328 55.150336903189883 1.3983309 0.00000003858 0.1716117195256 0.9851646652826 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_10 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3189090637833:ℝ):ℂ) + (((-0.9477853180108):ℝ):ℂ) * I)‖ ≤ 0.00000015005 := by
  have hl := lg_10
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.7948858145766459 57.794885852226671 (-1.2462181) 0.00000005004 0.3189090637833 (-0.9477853180108) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_11 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8790593402138):ℝ):ℂ) + ((0.4767123622138:ℝ):ℂ) * I)‖ ≤ 0.00000014415 := by
  have hl := lg_11
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.1871713276651783 60.1871713653152285 2.6446817 0.00000004414 (-0.8790593402138) 0.4767123622138 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_12 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8957432037226:ℝ):ℂ) + ((0.4445718310743:ℝ):ℂ) * I)‖ ≤ 0.00000015597 := by
  have hl := lg_12
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.3711568901049164 62.3711569277549415 0.4606962 0.00000005596 0.8957432037226 0.4445718310743 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_13 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0224186484503:ℝ):ℂ) + (((-0.9997486705175):ℝ):ℂ) * I)‖ ≤ 0.0000001191 := by
  have hl := lg_13
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.38022885271067 64.3802288903607202 (-1.5483758) 0.00000001909 0.0224186484503 (-0.9997486705175) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_14 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9645949107781):ℝ):ℂ) + ((0.263735962378:ℝ):ℂ) * I)‖ ≤ 0.00000012522 := by
  have hl := lg_14
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.2403389537690922 66.2403389914191424 2.8746994 0.00000002521 (-0.9645949107781) 0.263735962378 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_15 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4148864727308:ℝ):ℂ) + ((0.9098731860787:ℝ):ℂ) * I)‖ ≤ 0.0000001509 := by
  have hl := lg_15
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.9720600280915623 67.9720600657416125 1.1429783 0.00000005089 0.4148864727308 0.9098731860787 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_16 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8884045007149:ℝ):ℂ) + (((-0.4590614807513):ℝ):ℂ) * I)‖ ≤ 0.00000017336 := by
  have hl := lg_16
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.59197690212 69.59197695232 (-0.4769385) 0.00000007335 0.8884045007149 (-0.4590614807513) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_17 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4148885166783):ℝ):ℂ) + (((-0.9098722540692):ℝ):ℂ) * I)‖ ≤ 0.00000016928 := by
  have hl := lg_17
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.1136549097124934 71.1136549599125185 (-1.9986166) 0.00000006927 (-0.4148885166783) (-0.9098722540692) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_18 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9577563568076):ℝ):ℂ) + ((0.2875808769177:ℝ):ℂ) * I)‖ ≤ 0.00000015513 := by
  have hl := lg_18
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.5483311036198328 72.548331141269883 2.8498926 0.00000005512 (-0.9577563568076) 0.2875808769177 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_19 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0779119861307:ℝ):ℂ) + ((0.9969602411416:ℝ):ℂ) * I)‖ ≤ 0.00000012867 := by
  have hl := lg_19
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.9054183575037353 73.9054183951538106 1.4928053 0.00000002866 0.0779119861307 0.9969602411416 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_20 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9789909810503:ℝ):ℂ) + ((0.2039035532358:ℝ):ℂ) * I)‖ ≤ 0.00000014606 := by
  have hl := lg_20
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.1928800401066459 75.192880090306671 0.2053436 0.00000004605 0.9789909810503 0.2039035532358 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_21 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5239712418501:ℝ):ℂ) + (((-0.8517359553959):ℝ):ℂ) * I)‖ ≤ 0.00000011889 := by
  have hl := lg_21
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.4175131672840086 76.4175132049340839 (-1.0192895) 0.00000001888 0.5239712418501 (-0.8517359553959) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_22 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5778938172732):ℝ):ℂ) + (((-0.8161119628745):ℝ):ℂ) * I)‖ ≤ 0.00000013297 := by
  have hl := lg_22
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.5851655531951783 77.5851656033952285 (-2.1869419) 0.00000003296 (-0.5778938172732) (-0.8161119628745) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
