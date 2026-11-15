/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b2left (b2), angles 2

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

lemma cs_b2left_v24p228_11 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0232553301639:ℝ):ℂ) + (((-0.99972955824):ℝ):ℂ) * I)‖ ≤ 0.00000012221 := by
  have hl := lg_11
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.096206650465017524 58.09620668680706598 (-1.5475389) 0.0000000222 0.0232553301639 (-0.99972955824) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p228_12 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8707563758927):ℝ):ℂ) + ((0.491714687348:ℝ):ℂ) * I)‖ ≤ 0.00000015673 := by
  have hl := lg_12
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.204318292169797392 60.20431832851182162 2.6275348 0.00000005672 (-0.8707563758927) 0.491714687348 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p228_13 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7723524216234:ℝ):ℂ) + ((0.6351942512433:ℝ):ℂ) * I)‖ ≤ 0.00000015813 := by
  have hl := lg_13
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.1435930136842276 62.143593050026276056 0.68826 0.00000005812 0.7723524216234 0.6351942512433 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p228_14 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.44714277138:ℝ):ℂ) + (((-0.8944625995549):ℝ):ℂ) * I)‖ ≤ 0.00000012759 := by
  have hl := lg_14
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.939080963024604216 63.939080999366652672 (-1.1072279) 0.00000002758 0.44714277138 (-0.8944625995549) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p228_15 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9349048528872):ℝ):ℂ) + (((-0.3548984585471):ℝ):ℂ) * I)‖ ≤ 0.0000001184 := by
  have hl := lg_15
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.610640253410453044 65.6106402897525015 (-2.7787872) 0.00000001839 (-0.9349048528872) (-0.3548984585471) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_2 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3160915496795):ℝ):ℂ) + ((0.9487286926299:ℝ):ℂ) * I)‖ ≤ 0.00000010957 := by
  have hl := lg_2
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.9571526188592 16.9571526310912 1.8924033 0.00000000956 (-0.3160915496795) 0.9487286926299 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_3 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1720531017775):ℝ):ℂ) + (((-0.9850876763862):ℝ):ℂ) * I)‖ ≤ 0.00000010715 := by
  have hl := lg_3
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.876451023617324096 26.87645103584934856 (-1.7437098) 0.00000000714 (-0.1720531017775) (-0.9850876763862) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_4 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8001722601264):ℝ):ℂ) + (((-0.5997702510753):ℝ):ℂ) * I)‖ ≤ 0.0000001263 := by
  have hl := lg_4
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.9143052377184 33.9143052621824 (-2.4983787) 0.00000002629 (-0.8001722601264) (-0.5997702510753) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_5 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1031968225971):ℝ):ℂ) + (((-0.994660955203):ℝ):ℂ) * I)‖ ≤ 0.00000015847 := by
  have hl := lg_5
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.373289077069208976 39.37328910153323344 (-1.6741772) 0.00000005846 (-0.1031968225971) (-0.994660955203) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_6 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9889654749131:ℝ):ℂ) + ((0.1481461758867:ℝ):ℂ) * I)‖ ≤ 0.0000001167 := by
  have hl := lg_6
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.833603642476524096 43.83360366694054856 0.1486935 0.00000001669 0.9889654749131 0.1481461758867 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_7 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8865992900707):ℝ):ℂ) + ((0.4625383213786:ℝ):ℂ) * I)‖ ≤ 0.00000014081 := by
  have hl := lg_7
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.604745873770563808 47.604745898234612736 2.6607366 0.0000000408 (-0.8865992900707) 0.4625383213786 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_8 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8219469359248:ℝ):ℂ) + (((-0.5695640741162):ℝ):ℂ) * I)‖ ≤ 0.00000013585 := by
  have hl := lg_8
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.8714578565776 50.8714578932736 (-0.6059754) 0.00000003584 0.8219469359248 (-0.5695640741162) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_9 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9407954578417):ℝ):ℂ) + ((0.3389747871498:ℝ):ℂ) * I)‖ ≤ 0.0000001174 := by
  have hl := lg_9
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.752902047234648192 53.75290207169869712 2.7957657 0.00000001739 (-0.9407954578417) 0.3389747871498 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_10 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9762830312178:ℝ):ℂ) + ((0.2164981361496:ℝ):ℂ) * I)‖ ≤ 0.00000016802 := by
  have hl := lg_10
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.330441695928408976 56.33044173262443344 0.2182261 0.00000006801 0.9762830312178 0.2164981361496 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_11 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5164035777821):ℝ):ℂ) + (((-0.8563453420477):ℝ):ℂ) * I)‖ ≤ 0.00000012997 := by
  have hl := lg_11
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.662109934661391312 58.66210997135744024 (-2.1134422) 0.00000002996 (-0.5164035777821) (-0.8563453420477) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_12 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4531541573119):ℝ):ℂ) + ((0.8914321677538:ℝ):ℂ) * I)‖ ≤ 0.00000012625 := by
  have hl := lg_12
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.790756261335724096 60.79075629803174856 2.0410968 0.00000002624 (-0.4531541573119) 0.8914321677538 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_13 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9965631121939:ℝ):ℂ) + ((0.0828369688866:ℝ):ℂ) * I)‖ ≤ 0.00000012678 := by
  have hl := lg_13
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.7489210618611088 62.748921098557157728 0.082932 0.00000002677 0.9965631121939 0.0828369688866 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_14 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1585768263452):ℝ):ℂ) + (((-0.98734664133):ℝ):ℂ) * I)‖ ≤ 0.00000015754 := by
  have hl := lg_14
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.561898492629763808 64.561898529325812736 (-1.7300454) 0.00000005753 (-0.1585768263452) (-0.98734664133) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_15 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9620729136837):ℝ):ℂ) + ((0.2727924275268:ℝ):ℂ) * I)‖ ≤ 0.00000015842 := by
  have hl := lg_15
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.249740100686533072 66.249740137382582 2.8652983 0.00000005841 (-0.9620729136837) 0.2727924275268 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_16 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2805512986751:ℝ):ℂ) + ((0.9598390327611:ℝ):ℂ) * I)‖ ≤ 0.0000001454 := by
  have hl := lg_16
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.8286104754368 67.8286105243648 1.2864279 0.00000004539 0.2805512986751 0.9598390327611 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_17 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9807182365422:ℝ):ℂ) + (((-0.1954270721102):ℝ):ℂ) * I)‖ ≤ 0.00000015544 := by
  have hl := lg_17
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.311731223554041376 69.31173127248206584 (-0.1966929) 0.00000005543 0.9807182365422 (-0.1954270721102) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_18 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0242176053399):ℝ):ℂ) + (((-0.9997067107864):ℝ):ℂ) * I)‖ ≤ 0.00000012383 := by
  have hl := lg_18
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.710054666093848192 70.71005470278989712 (-1.5950163) 0.00000002382 (-0.0242176053399) (-0.9997067107864) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_19 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9750442951881):ℝ):ℂ) + (((-0.2220104099482):ℝ):ℂ) * I)‖ ≤ 0.00000012499 := by
  have hl := lg_19
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.032755167249855792 72.032755203945929184 (-2.9177168) 0.00000002498 (-0.9750442951881) (-0.2220104099482) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p464_20 : ‖exp (-((((((24464:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5139927241499):ℝ):ℂ) + ((0.8577945438822:ℝ):ℂ) * I)‖ ≤ 0.00000017138 := by
  have hl := lg_20
  refine (ecis_approx ((((24464:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.287594314787608976 73.28759436371563344 2.1106293 0.00000007137 (-0.5139927241499) 0.8577945438822 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_2 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1573674055379):ℝ):ℂ) + ((0.9875401256018:ℝ):ℂ) * I)‖ ≤ 0.00000014424 := by
  have hl := lg_2
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.12073535341 17.12073536576 1.7288206 0.00000004423 (-0.1573674055379) 0.9875401256018 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_3 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4188567796162):ℝ):ℂ) + (((-0.9080523102585):ℝ):ℂ) * I)‖ ≤ 0.00000010733 := by
  have hl := lg_3
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.1357235236816508 27.1357235360316755 (-2.0029823) 0.00000000732 (-0.4188567796162) (-0.9080523102585) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_4 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9504710281254):ℝ):ℂ) + (((-0.3108131665319):ℝ):ℂ) * I)‖ ≤ 0.00000012909 := by
  have hl := lg_4
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.24147070682 34.24147073152 (-2.8255442) 0.00000002908 (-0.9504710281254) (-0.3108131665319) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_5 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.464622516155):ℝ):ℂ) + (((-0.8855088466395):ℝ):ℂ) * I)‖ ≤ 0.00000011881 := by
  have hl := lg_5
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.7531164242809623 39.753116448980987 (-2.0540046) 0.0000000188 (-0.464622516155) (-0.8855088466395) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_6 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9626524972282:ℝ):ℂ) + (((-0.2707400405931):ℝ):ℂ) * I)‖ ≤ 0.00000015155 := by
  have hl := lg_6
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.2564588770916508 44.2564589017916755 (-0.2741617) 0.00000005154 0.9626524972282 (-0.2707400405931) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_7 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5897146530439):ℝ):ℂ) + ((0.807611681425:ℝ):ℂ) * I)‖ ≤ 0.0000001361 := by
  have hl := lg_7
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.0639806688249234 48.0639806935249728 2.2015018 0.00000003609 (-0.5897146530439) 0.807611681425 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_8 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4565136333669:ℝ):ℂ) + (((-0.8897164169274):ℝ):ℂ) * I)‖ ≤ 0.00000013986 := by
  have hl := lg_8
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.36220606023 51.36220609728 (-1.0967236) 0.00000003985 0.4565136333669 (-0.8897164169274) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_9 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.649117990876):ℝ):ℂ) + ((0.7606877374484:ℝ):ℂ) * I)‖ ≤ 0.00000011727 := by
  have hl := lg_9
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.2714470473633016 54.271447072063351 2.2772207 0.00000001726 (-0.649117990876) 0.7606877374484 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_10 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9475919575567:ℝ):ℂ) + (((-0.3194831481844):ℝ):ℂ) * I)‖ ≤ 0.00000015014 := by
  have hl := lg_10
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.8738517776909623 56.873851814740987 (-0.325184) 0.00000005013 0.9475919575567 (-0.3194831481844) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_11 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.895052616354):ℝ):ℂ) + (((-0.4459605518955):ℝ):ℂ) * I)‖ ≤ 0.00000014577 := by
  have hl := lg_11
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.2280132188577651 59.2280132559078145 (-2.6793455) 0.00000004576 (-0.895052616354) (-0.4459605518955) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_12 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1158766270958:ℝ):ℂ) + ((0.9932636141996:ℝ):ℂ) * I)‖ ≤ 0.00000014131 := by
  have hl := lg_12
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.3771942305016508 61.3771942675516755 1.4546588 0.0000000413 0.1158766270958 0.9932636141996 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_13 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8666261151167:ℝ):ℂ) + (((-0.4989580910233):ℝ):ℂ) * I)‖ ≤ 0.00000016177 := by
  have hl := lg_13
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.35424911003799 63.3542491470880394 (-0.5223961) 0.00000006176 0.8666261151167 (-0.4989580910233) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_14 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7047471422101):ℝ):ℂ) + (((-0.7094585720972):ℝ):ℂ) * I)‖ ≤ 0.00000014958 := by
  have hl := lg_14
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.1847160222349234 65.1847160592849728 (-2.352863) 0.00000004957 (-0.7047471422101) (-0.7094585720972) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_15 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6094780574028):ℝ):ℂ) + ((0.7928029373884:ℝ):ℂ) * I)‖ ≤ 0.00000013103 := by
  have hl := lg_15
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.8888399479626131 66.8888399850126625 2.2261984 0.00000003102 (-0.6094780574028) 0.7928029373884 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_16 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8067903551309:ℝ):ℂ) + ((0.5908378143516:ℝ):ℂ) * I)‖ ≤ 0.00000016535 := by
  have hl := lg_16
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.48294141364 68.48294146304 0.6320969 0.00000006534 0.8067903551309 0.5908378143516 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_17 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6483880053641:ℝ):ℂ) + (((-0.7613100514902):ℝ):ℂ) * I)‖ ≤ 0.00000014295 := by
  have hl := lg_17
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.9803695725059198 69.9803696219059445 (-0.8653312) 0.00000004294 0.6483880053641 (-0.7613100514902) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_18 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6490596442173):ℝ):ℂ) + (((-0.7607375225607):ℝ):ℂ) * I)‖ ≤ 0.00000015886 := by
  have hl := lg_18
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.3921824007733016 71.392182437823351 (-2.277144) 0.00000005885 (-0.6490596442173) (-0.7607375225607) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_19 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8911096225933):ℝ):ℂ) + ((0.4537881007859:ℝ):ℂ) * I)‖ ≤ 0.00000012002 := by
  have hl := lg_19
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.7276427661490941 72.7276428031991682 2.6705809 0.00000002001 (-0.8911096225933) 0.4537881007859 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p7_20 : ‖exp (-((((((24700:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1663824390227:ℝ):ℂ) + ((0.9860612982897:ℝ):ℂ) * I)‖ ≤ 0.00000015507 := by
  have hl := lg_20
  refine (ecis_approx ((((24700:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.9945871311009623 73.994587180500987 1.4036365 0.00000005506 0.1663824390227 0.9860612982897 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_2 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0353298193165):ℝ):ℂ) + ((0.9993757070626:ℝ):ℂ) * I)‖ ≤ 0.00000011723 := by
  have hl := lg_2
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.2434224043231 17.2434224167616 1.6061335 0.00000001722 (-0.0353298193165) 0.9993757070626 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_3 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5864267673179):ℝ):ℂ) + (((-0.8100022509611):ℝ):ℂ) * I)‖ ≤ 0.00000013 := by
  have hl := lg_3
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.330177898729895828 27.330177911168420705 (-2.1974367) 0.00000002999 (-0.5864267673179) (-0.8100022509611) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_4 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9975036069785):ℝ):ℂ) + (((-0.0706155332355):ℝ):ℂ) * I)‖ ≤ 0.00000012727 := by
  have hl := lg_4
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.4868448086462 34.4868448335232 (-3.0709183) 0.00000002726 (-0.9975036069785) (-0.0706155332355) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_5 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6947546855017):ℝ):ℂ) + (((-0.7192467775044):ℝ):ℂ) * I)‖ ≤ 0.0000001165 := by
  have hl := lg_5
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.037986934689777293 40.03798695956680217 (-2.3388751) 0.00000001649 (-0.6947546855017) (-0.7192467775044) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_6 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8302149240146:ℝ):ℂ) + (((-0.557443432057):ℝ):ℂ) * I)‖ ≤ 0.00000014722 := by
  have hl := lg_6
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.573600303052995828 44.573600327930020705 (-0.5913032) 0.00000004721 0.8302149240146 (-0.557443432057) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_7 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2823849862662):ℝ):ℂ) + ((0.9593011620601:ℝ):ℂ) * I)‖ ≤ 0.00000013257 := by
  have hl := lg_7
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.408406765115693094 48.408406789992742848 1.8570757 0.00000003256 (-0.2823849862662) 0.9593011620601 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_8 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1058130709132:ℝ):ℂ) + (((-0.9943860387313):ℝ):ℂ) * I)‖ ≤ 0.00000014448 := by
  have hl := lg_8
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.7302672129693 51.7302672502848 (-1.4647848) 0.00000004447 0.1058130709132 (-0.9943860387313) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_9 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3122073813252):ℝ):ℂ) + ((0.950013974131:ℝ):ℂ) * I)‖ ≤ 0.00000015774 := by
  have hl := lg_9
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.660355797459791656 54.66035582233684141 1.888312 0.00000005773 (-0.3122073813252) 0.950013974131 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_10 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7433433143422:ℝ):ℂ) + (((-0.6689100963678):ℝ):ℂ) * I)‖ ≤ 0.00000012562 := by
  have hl := lg_10
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.281409339012877293 57.28140937632840217 (-0.7327416) 0.00000002561 0.7433433143422 (-0.6689100963678) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_11 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9992849180696):ℝ):ℂ) + (((-0.0378107381509):ℝ):ℂ) * I)‖ ≤ 0.00000015472 := by
  have hl := lg_11
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.652440682005045441 59.652440719320595195 (-3.1037729) 0.00000005471 (-0.9992849180696) (-0.0378107381509) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_12 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5277640808001:ℝ):ℂ) + ((0.8493910024348:ℝ):ℂ) * I)‖ ≤ 0.00000016443 := by
  have hl := lg_12
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.817022707376095828 61.817022744691620705 1.0148303 0.00000006442 0.5277640808001 0.8493910024348 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_13 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5600152663674:ℝ):ℂ) + (((-0.8284822879431):ℝ):ℂ) * I)‖ ≤ 0.00000012564 := by
  have hl := lg_13
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.8082451461706509 63.808245183486200654 (-0.9763921) 0.00000002563 0.5600152663674 (-0.8284822879431) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_14 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.948725664238):ℝ):ℂ) + (((-0.3161006387468):ℝ):ℂ) * I)‖ ≤ 0.00000013497 := by
  have hl := lg_14
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.651829169438793094 65.651829206754342848 (-2.8199761) 0.00000003496 (-0.948725664238) (-0.3161006387468) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_15 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1751687574216):ℝ):ℂ) + ((0.9845384230301:ℝ):ℂ) * I)‖ ≤ 0.00000014557 := by
  have hl := lg_15
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.368164833419673121 67.368164870735222875 1.7468735 0.00000004556 (-0.1751687574216) 0.9845384230301 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_16 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9900268938738:ℝ):ℂ) + ((0.1408784916396:ℝ):ℂ) * I)‖ ≤ 0.0000001617 := by
  have hl := lg_16
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.9736896172924 68.9736896670464 0.1413487 0.00000006169 0.9900268938738 0.1408784916396 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_17 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2025746076025:ℝ):ℂ) + (((-0.9792668320507):ℝ):ℂ) * I)‖ ≤ 0.00000014477 := by
  have hl := lg_17
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.481848334219828618 70.481848383973853495 (-1.36681) 0.00000004476 0.2025746076025 (-0.9792668320507) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_18 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9383906542053):ℝ):ℂ) + (((-0.3455763011611):ℝ):ℂ) * I)‖ ≤ 0.00000016014 := by
  have hl := lg_18
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.903778201782891656 71.90377823909844141 (-2.7887398) 0.00000006013 (-0.9383906542053) (-0.3455763011611) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_19 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5468681534992):ℝ):ℂ) + ((0.8372187424323:ℝ):ℂ) * I)‖ ≤ 0.00000012085 := by
  have hl := lg_19
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.248808465323522831 73.248808502639097462 2.1494152 0.00000002084 (-0.5468681534992) 0.8372187424323 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p877_20 : ‖exp (-((((((24877:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6422303155331:ℝ):ℂ) + ((0.7665117232047:ℝ):ℂ) * I)‖ ≤ 0.00000014283 := by
  have hl := lg_20
  refine (ecis_approx ((((24877:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.524831743335977293 74.52483179309000217 0.8733919 0.00000004282 0.6422303155331 0.7665117232047 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_2 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0561287133145:ℝ):ℂ) + ((0.9984235411595:ℝ):ℂ) * I)‖ ≤ 0.0000001231 := by
  have hl := lg_2
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.3349178321227 17.3349178446272 1.5146381 0.00000002309 0.0561287133145 0.9984235411595 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_3 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.697323984534):ℝ):ℂ) + (((-0.71675606769):ℝ):ℂ) * I)‖ ≤ 0.00000010793 := by
  have hl := lg_3
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.475194720799773476 27.475194733304298485 (-2.3424535) 0.00000000792 (-0.697323984534) (-0.71675606769) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_4 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.993699134879):ℝ):ℂ) + ((0.1120804572013:ℝ):ℂ) * I)‖ ≤ 0.00000014619 := by
  have hl := lg_4
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.6698356642454 34.6698356892544 3.0292762 0.00000004618 (-0.993699134879) 0.1120804572013 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_5 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8307894552999):ℝ):ℂ) + (((-0.5565868134439):ℝ):ℂ) * I)‖ ≤ 0.00000012101 := by
  have hl := lg_5
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.250432739062452881 40.25043276407147789 (-2.5513209) 0.000000021 (-0.8307894552999) (-0.5565868134439) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_6 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6764862332484:ℝ):ℂ) + (((-0.7364552778176):ℝ):ℂ) * I)‖ ≤ 0.00000012769 := by
  have hl := lg_6
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.810112552922473476 44.810112577931498485 (-0.8278154) 0.00000002768 0.6764862332484 (-0.7364552778176) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_7 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0294149297331):ℝ):ℂ) + ((0.9995672873341:ℝ):ℂ) * I)‖ ≤ 0.00000015273 := by
  have hl := lg_7
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.665266904722368798 48.665266929731418816 1.6002155 0.00000005272 (-0.0294149297331) 0.9995672873341 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_8 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.167678912569):ℝ):ℂ) + (((-0.9858416618702):ℝ):ℂ) * I)‖ ≤ 0.00000016108 := by
  have hl := lg_8
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.0047534963681 52.0047535338816 (-1.7392711) 0.00000006107 (-0.167678912569) (-0.9858416618702) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_9 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0274785140019):ℝ):ℂ) + ((0.999622394341:ℝ):ℂ) * I)‖ ≤ 0.00000012303 := by
  have hl := lg_9
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.950389441599546952 54.95038946660859697 1.5982783 0.00000002302 (-0.0274785140019) 0.999622394341 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_10 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5090782341141:ℝ):ℂ) + (((-0.8607202516214):ℝ):ℂ) * I)‖ ≤ 0.0000001441 := by
  have hl := lg_10
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.585350571185152881 57.58535060869867789 (-1.0366828) 0.00000004409 0.5090782341141 (-0.8607202516214) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_11 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9614132133718):ℝ):ℂ) + ((0.2751084021186:ℝ):ℂ) * I)‖ ≤ 0.00000012364 := by
  have hl := lg_11
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.968962857911491797 59.968962895425041815 2.8628902 0.00000002363 (-0.9614132133718) 0.2751084021186 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_12 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7732645882316:ℝ):ℂ) + ((0.6340834933879:ℝ):ℂ) * I)‖ ≤ 0.00000015078 := by
  have hl := lg_12
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.145030385045173476 62.145030422558698485 0.6868227 0.00000005077 0.7732645882316 0.6340834933879 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_13 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2530493788226:ℝ):ℂ) + (((-0.9674533641874):ℝ):ℂ) * I)‖ ≤ 0.00000012699 := by
  have hl := lg_13
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.1468184612526353 64.146818498766185318 (-1.3149654) 0.00000002698 0.2530493788226 (-0.9674533641874) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_14 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996425325012):ℝ):ℂ) + ((0.0267358671211:ℝ):ℂ) * I)‖ ≤ 0.00000014215 := by
  have hl := lg_14
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.000184736845068798 66.000184774358618816 3.1148536 0.00000004214 (-0.9996425325012) 0.0267358671211 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_15 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1803924445884:ℝ):ℂ) + ((0.9835947163011:ℝ):ℂ) * I)‖ ≤ 0.00000011913 := by
  have hl := lg_15
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.725627459862226357 67.725627497375776375 1.3894109 0.00000001912 0.1803924445884 0.9835947163011 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_16 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.974875921455:ℝ):ℂ) + (((-0.2227485976775):ℝ):ℂ) * I)‖ ≤ 0.0000001505 := by
  have hl := lg_16
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.3396713284908 69.3396713785088 (-0.224633) 0.00000005049 0.974875921455 (-0.2227485976775) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_17 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1691801543715):ℝ):ℂ) + (((-0.9855851436411):ℝ):ℂ) * I)‖ ≤ 0.00000016656 := by
  have hl := lg_17
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.855832495497997906 70.855832545516022915 (-1.7407941) 0.00000006655 (-0.1691801543715) (-0.9855851436411) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_18 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9995888641133):ℝ):ℂ) + ((0.0286723232597:ℝ):ℂ) * I)‖ ≤ 0.0000001251 := by
  have hl := lg_18
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.285307273722246952 72.28530731123579697 3.1129164 0.00000002509 (-0.9995888641133) 0.0286723232597 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_19 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.188812714256):ℝ):ℂ) + ((0.9820131154595:ℝ):ℂ) * I)‖ ≤ 0.00000016184 := by
  have hl := lg_19
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.637474410470554427 73.637474447984129454 1.7607493 0.00000006183 (-0.188812714256) 0.9820131154595 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p009_20 : ‖exp (-((((((25009:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8879372678289:ℝ):ℂ) + ((0.4599645729842:ℝ):ℂ) * I)‖ ≤ 0.00000016719 := by
  have hl := lg_20
  refine (ecis_approx ((((25009:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.920268403307852881 74.92026845332587789 0.4779553 0.00000006718 0.8879372678289 0.4599645729842 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_2 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.147117697276:ℝ):ℂ) + ((0.989118993422:ℝ):ℂ) * I)‖ ≤ 0.00000015097 := by
  have hl := lg_2
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.4264132599223 17.4264132724928 1.4231427 0.00000005096 0.147117697276 0.989118993422 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_3 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.793582249019):ℝ):ℂ) + (((-0.6084629931188):ℝ):ℂ) * I)‖ ≤ 0.00000012674 := by
  have hl := lg_3
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.620211542869651124 27.620211555440176265 (-2.4874703) 0.00000002673 (-0.793582249019) (-0.6084629931188) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_4 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9567127371115):ℝ):ℂ) + ((0.2910339128451:ℝ):ℂ) * I)‖ ≤ 0.00000012325 := by
  have hl := lg_4
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.8528265198446 34.8528265449856 2.8462853 0.00000002324 (-0.9567127371115) 0.2910339128451 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_5 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9294688385487):ℝ):ℂ) + (((-0.3689006343289):ℝ):ℂ) * I)‖ ≤ 0.00000012551 := by
  have hl := lg_5
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.462878543435128469 40.46287856857615361 (-2.7637667) 0.0000000255 (-0.9294688385487) (-0.3689006343289) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_6 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4850922227918:ℝ):ℂ) + (((-0.8744629982949):ℝ):ℂ) * I)‖ ≤ 0.00000014748 := by
  have hl := lg_6
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.046624802791951124 45.046624827932976265 (-1.0643277) 0.00000004747 0.4850922227918 (-0.8744629982949) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_7 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2254850961771:ℝ):ℂ) + ((0.9742466173418:ℝ):ℂ) * I)‖ ≤ 0.00000011312 := by
  have hl := lg_7
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.922127044329044502 48.922127069470094784 1.3433554 0.00000001311 0.2254850961771 0.9742466173418 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_8 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4286165394021):ℝ):ℂ) + (((-0.9034865035777):ℝ):ℂ) * I)‖ ≤ 0.00000016006 := by
  have hl := lg_8
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.2792397797669 52.2792398174784 (-2.0137573) 0.00000006005 (-0.4286165394021) (-0.9034865035777) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_9 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2595455788794:ℝ):ℂ) + ((0.9657308592378:ℝ):ℂ) * I)‖ ≤ 0.00000014628 := by
  have hl := lg_9
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.240423085739302248 55.24042311088035253 1.3082447 0.00000004627 0.2595455788794 0.9657308592378 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_10 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2281452115957:ℝ):ℂ) + (((-0.9736271167269):ℝ):ℂ) * I)‖ ≤ 0.00000016127 := by
  have hl := lg_10
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.889291803357428469 57.88929184106895361 (-1.3406241) 0.00000006126 0.2281452115957 (-0.9736271167269) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_11 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8280225576249):ℝ):ℂ) + ((0.5606947868519:ℝ):ℂ) * I)‖ ≤ 0.00000013799 := by
  have hl := lg_11
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.285485033817938153 60.285485071529488435 2.546368 0.00000003798 (-0.8280225576249) 0.5606947868519 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_12 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9363136114419:ℝ):ℂ) + ((0.3511649484625:ℝ):ℂ) * I)‖ ≤ 0.00000012864 := by
  have hl := lg_12
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.473038062714251124 62.473038100425776265 0.358815 0.00000002863 0.9363136114419 0.3511649484625 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_13 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0826479923295):ℝ):ℂ) + (((-0.9965788023852):ℝ):ℂ) * I)‖ ≤ 0.00000014227 := by
  have hl := lg_13
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.4853917763346197 64.485391814046169982 (-1.6535387) 0.00000004226 (-0.0826479923295) (-0.9965788023852) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_14 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9304729853175):ℝ):ℂ) + ((0.3663605101998:ℝ):ℂ) * I)‖ ≤ 0.000000163 := by
  have hl := lg_14
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.348540304251344502 66.348540341962894784 2.7664981 0.00000006299 (-0.9304729853175) 0.3663605101998 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_15 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5131475933129:ℝ):ℂ) + ((0.8583003830112:ℝ):ℂ) * I)‖ ≤ 0.00000014506 := by
  have hl := lg_15
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.083090086304779593 68.083090124016329875 1.0319483 0.00000004505 0.5131475933129 0.8583003830112 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_16 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8305985270129:ℝ):ℂ) + (((-0.5568716970039):ℝ):ℂ) * I)‖ ≤ 0.0000001393 := by
  have hl := lg_16
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.7056530396892 69.7056530899712 (-0.5906147) 0.00000003929 0.8305985270129 (-0.5568716970039) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_17 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5175472795209):ℝ):ℂ) + (((-0.8556546110747):ℝ):ℂ) * I)‖ ≤ 0.0000001281 := by
  have hl := lg_17
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.229816656776167194 71.229816707058192335 (-2.1147783) 0.00000002809 (-0.5175472795209) (-0.8556546110747) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_18 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9170389475799):ℝ):ℂ) + ((0.3987976535577:ℝ):ℂ) * I)‖ ≤ 0.00000014051 := by
  have hl := lg_18
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.666836345661602248 72.66683638337315253 2.7313873 0.0000000405 (-0.9170389475799) 0.3987976535577 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_19 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1974078471904:ℝ):ℂ) + ((0.980321448234:ℝ):ℂ) * I)‖ ≤ 0.00000013055 := by
  have hl := lg_19
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.026140355617586023 74.026140393329161446 1.3720833 0.00000003054 0.1974078471904 0.980321448234 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_20 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9965972718398:ℝ):ℂ) + ((0.0824249826293:ℝ):ℂ) * I)‖ ≤ 0.00000012742 := by
  have hl := lg_20
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.315705063279728469 75.31570511356175361 0.0825186 0.00000002741 0.9965972718398 0.0824249826293 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_21 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4138520431027:ℝ):ℂ) + (((-0.9103441582279):ℝ):ℂ) * I)‖ ≤ 0.00000013877 := by
  have hl := lg_21
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.542338587198695626 76.542338624910271049 (-1.1441149) 0.00000003876 0.4138520431027 (-0.9103441582279) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_22 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6764106299038):ℝ):ℂ) + (((-0.736524717666):ℝ):ℂ) * I)‖ ≤ 0.00000015788 := by
  have hl := lg_22
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.711898293740238153 77.711898344022288435 (-2.3136746) 0.00000005787 (-0.6764106299038) (-0.736524717666) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_23 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9583456840742):ℝ):ℂ) + ((0.2856108359091:ℝ):ℂ) * I)‖ ≤ 0.00000013682 := by
  have hl := lg_23
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.829460056533550606 78.829460106815626029 2.8519489 0.00000003681 (-0.9583456840742) 0.2856108359091 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_24 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2095955201261):ℝ):ℂ) + ((0.9777881764176:ℝ):ℂ) * I)‖ ≤ 0.00000017071 := by
  have hl := lg_24
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.899451322636551124 79.899451372918576265 1.7819576 0.0000000707 (-0.2095955201261) 0.9777881764176 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_25 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7278246487831:ℝ):ℂ) + ((0.685763283228:ℝ):ℂ) * I)‖ ≤ 0.00000014383 := by
  have hl := lg_25
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.925757086870256938 80.92575713715230722 0.7556519 0.00000004382 0.7278246487831 0.685763283228 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_26 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9735760167289:ℝ):ℂ) + (((-0.2283631748999):ℝ):ℂ) * I)‖ ≤ 0.00000015709 := by
  have hl := lg_26
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.9118050362569197 81.911805086538969982 (-0.2303961) 0.00000005708 0.9735760167289 (-0.2283631748999) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_27 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3816406325408:ℝ):ℂ) + (((-0.9243107851766):ℝ):ℂ) * I)‖ ≤ 0.00000016474 := by
  have hl := lg_27
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.860634628608953372 82.860634666320528795 (-1.1792257) 0.00000006473 0.3816406325408 (-0.9243107851766) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_28 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4992632625716):ℝ):ℂ) + (((-0.8664503417047):ℝ):ℂ) * I)‖ ≤ 0.00000012918 := by
  have hl := lg_28
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.774953564173644502 83.774953614455694784 (-2.0935446) 0.00000002917 (-0.4992632625716) (-0.8664503417047) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_29 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9862838064862):ℝ):ℂ) + (((-0.1650583311815):ℝ):ℂ) * I)‖ ≤ 0.0000001578 := by
  have hl := lg_29
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.657184435548783572 84.657184485830858995 (-2.9757755) 0.00000005779 (-0.9862838064862) (-0.1650583311815) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p141_30 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7734680552159):ℝ):ℂ) + ((0.6338352842184:ℝ):ℂ) * I)‖ ≤ 0.0000001543 := by
  have hl := lg_30
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.509503346227079593 85.509503396509129875 2.4550909 0.00000005429 (-0.7734680552159) 0.6338352842184 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_2 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2368760550244:ℝ):ℂ) + ((0.9715398780061:ℝ):ℂ) * I)‖ ≤ 0.00000013383 := by
  have hl := lg_2
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.5179086877219 17.5179087003584 1.3316472 0.00000003382 0.2368760550244 0.9715398780061 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_3 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8731808068366):ℝ):ℂ) + (((-0.4873964284663):ℝ):ℂ) * I)‖ ≤ 0.00000014887 := by
  have hl := lg_3
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.765228364939528772 27.765228377576054045 (-2.6324871) 0.00000004886 (-0.8731808068366) (-0.4873964284663) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_4 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.88777951511):ℝ):ℂ) + ((0.4602689783677:ℝ):ℂ) * I)‖ ≤ 0.00000015765 := by
  have hl := lg_4
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.0358173754438 35.0358174007168 2.6632945 0.00000005764 (-0.88777951511) 0.4602689783677 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_5 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9863558427996):ℝ):ℂ) + (((-0.1646273094109):ℝ):ℂ) * I)‖ ≤ 0.00000013002 := by
  have hl := lg_5
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.675324347807804057 40.67532437308082933 (-2.9762125) 0.00000003001 (-0.9863558427996) (-0.1646273094109) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_6 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2666894418487:ℝ):ℂ) + (((-0.9637825177946):ℝ):ℂ) * I)‖ ≤ 0.00000012769 := by
  have hl := lg_6
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.283137052661428772 45.283137077934454045 (-1.3008399) 0.00000002768 0.2666894418487 (-0.9637825177946) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_7 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4655898815282:ℝ):ℂ) + ((0.8850006001233:ℝ):ℂ) * I)‖ ≤ 0.00000015179 := by
  have hl := lg_7
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.178987183935720206 49.178987209208770752 1.0864953 0.00000005178 0.4655898815282 0.8850006001233 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_8 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6574633710139):ℝ):ℂ) + (((-0.7534865066856):ℝ):ℂ) * I)‖ ≤ 0.00000014365 := by
  have hl := lg_8
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.5537260631657 52.5537261010752 (-2.2882436) 0.00000004364 (-0.6574633710139) (-0.7534865066856) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_9 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5248895341681:ℝ):ℂ) + ((0.8511703571676:ℝ):ℂ) * I)‖ ≤ 0.00000013475 := by
  have hl := lg_9
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.530456729879057544 55.53045675515210809 1.018211 0.00000003474 0.5248895341681 0.8511703571676 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_10 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0737020846529):ℝ):ℂ) + (((-0.9972803029828):ℝ):ℂ) * I)‖ ≤ 0.0000001291 := by
  have hl := lg_10
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.193233035529704057 58.19323307343922933 (-1.6445653) 0.00000002909 (-0.0737020846529) (-0.9972803029828) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_11 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6123656663257):ℝ):ℂ) + ((0.7905746585189:ℝ):ℂ) * I)‖ ≤ 0.00000016209 := by
  have hl := lg_11
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.602007209724384509 60.602007247633935055 2.2298458 0.00000006208 (-0.6123656663257) 0.7905746585189 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_12 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9995254926643:ℝ):ℂ) + ((0.0308024270826:ℝ):ℂ) * I)‖ ≤ 0.00000013143 := by
  have hl := lg_12
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.801045740383328772 62.801045778292854045 0.0308073 0.00000003142 0.9995254926643 0.0308024270826 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_13 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4089614264499):ℝ):ℂ) + (((-0.9125516706864):ℝ):ℂ) * I)‖ ≤ 0.00000015755 := by
  have hl := lg_13
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.8239650914166041 64.823965129326154646 (-1.992112) 0.00000005754 (-0.4089614264499) (-0.9125516706864) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_14 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7495262806778):ℝ):ℂ) + ((0.6619745875331:ℝ):ℂ) * I)‖ ≤ 0.00000013061 := by
  have hl := lg_14
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.696895871657620206 66.696895909567170752 2.4181425 0.0000000306 (-0.7495262806778) 0.6619745875331 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_15 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7810282950076:ℝ):ℂ) + ((0.6244956384135:ℝ):ℂ) * I)‖ ≤ 0.00000016624 := by
  have hl := lg_15
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.440552712747332829 68.440552750656883375 0.6744856 0.00000006623 0.7810282950076 0.6244956384135 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_16 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5763048591451:ℝ):ℂ) + (((-0.8172347944904):ℝ):ℂ) * I)‖ ≤ 0.0000001281 := by
  have hl := lg_16
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.0716347508876 70.0716348014336 (-0.9565964) 0.00000002809 0.5763048591451 (-0.8172347944904) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_17 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7943678421257):ℝ):ℂ) + (((-0.607437018422):ℝ):ℂ) * I)‖ ≤ 0.00000016094 := by
  have hl := lg_17
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.603800818054336482 71.603800868600361755 (-2.4887625) 0.00000006093 (-0.7943678421257) (-0.607437018422) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_18 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7026121827843):ℝ):ℂ) + ((0.7115729903382:ℝ):ℂ) * I)‖ ≤ 0.00000016857 := by
  have hl := lg_18
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.048365417600957544 73.04836545551050809 2.3498582 0.00000006856 (-0.7026121827843) 0.7115729903382 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_19 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5541811579516:ℝ):ℂ) + ((0.8323960861101:ℝ):ℂ) * I)‖ ≤ 0.00000015253 := by
  have hl := lg_19
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.414806300764617619 74.414806338674193438 0.9834174 0.00000005252 0.5541811579516 0.8323960861101 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_20 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9514393248383:ℝ):ℂ) + (((-0.3078363382566):ℝ):ℂ) * I)‖ ≤ 0.00000016292 := by
  have hl := lg_20
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.711141723251604057 75.71114177379762933 (-0.3129181) 0.00000006291 0.9514393248383 (-0.3078363382566) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_21 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0248018833462:ℝ):ℂ) + (((-0.999692385978):ℝ):ℂ) * I)‖ ≤ 0.00000013729 := by
  have hl := lg_21
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.944215548875248978 76.944215586784824797 (-1.5459919) 0.00000003728 0.0248018833462 (-0.999692385978) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_22 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9131295268364):ℝ):ℂ) + (((-0.407669556242):ℝ):ℂ) * I)‖ ≤ 0.00000016185 := by
  have hl := lg_22
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.119915897446284509 78.119915947992335055 (-2.7216922) 0.00000006184 (-0.9131295268364) (-0.407669556242) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_23 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7625640151953):ℝ):ℂ) + ((0.6469127628144:ℝ):ℂ) * I)‖ ≤ 0.00000015013 := by
  have hl := lg_23
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.243345292898946918 79.243345343445022737 2.4380637 0.00000005012 (-0.7625640151953) 0.6469127628144 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_24 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2068378693485:ℝ):ℂ) + ((0.9783752326195:ℝ):ℂ) * I)‖ ≤ 0.00000016524 := by
  have hl := lg_24
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.318954428105228772 80.318954478651254045 1.3624545 0.00000006523 0.2068378693485 0.9783752326195 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_25 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9457957002049:ℝ):ℂ) + ((0.3247622106618:ℝ):ℂ) * I)‖ ≤ 0.00000015284 := by
  have hl := lg_25
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.350648695615608114 81.35064874616165866 0.3307603 0.00000005283 0.9457957002049 0.3247622106618 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_26 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7897071694602:ℝ):ℂ) + (((-0.6134839741208):ℝ):ℂ) * I)‖ ≤ 0.00000013636 := by
  have hl := lg_26
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.3418737791385041 82.341873829684554646 (-0.6604648) 0.00000003635 0.7897071694602 (-0.6134839741208) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_27 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0434660748157):ℝ):ℂ) + (((-0.9990549035663):ℝ):ℂ) * I)‖ ≤ 0.00000013941 := by
  have hl := lg_27
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.295685094818586316 83.295685132728162135 (-1.6142761) 0.0000000394 (-0.0434660748157) (-0.9990549035663) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_28 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8206795344238):ℝ):ℂ) + (((-0.5713887483316):ℝ):ℂ) * I)‖ ≤ 0.00000013397 := by
  have hl := lg_28
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.214804559379520206 84.214804609925570752 (-2.5333956) 0.00000003396 (-0.8206795344238) (-0.5713887483316) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_29 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9614232816953):ℝ):ℂ) + ((0.2750732142107:ℝ):ℂ) * I)‖ ≤ 0.00000013502 := by
  have hl := lg_29
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.101667484969746916 85.101667535515822735 2.8629268 0.00000003501 (-0.9614232816953) 0.2750732142107 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p273_30 : ‖exp (-((((((25273:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4217156056487):ℝ):ℂ) + ((0.9067281554846:ℝ):ℂ) * I)‖ ≤ 0.00000015052 := by
  have hl := lg_30
  refine (ecis_approx ((((25273:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.958461400469232829 85.958461451015283375 2.0061329 0.00000005051 (-0.4217156056487) 0.9067281554846 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_2 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.353992063723:ℝ):ℂ) + ((0.9352484262596:ℝ):ℂ) * I)‖ ≤ 0.00000012984 := by
  have hl := lg_2
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.640595738635 17.64059575136 1.2089602 0.00000002983 0.353992063723 0.9352484262596 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_3 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9509043993491):ℝ):ℂ) + (((-0.3094847703727):ℝ):ℂ) * I)‖ ≤ 0.00000012401 := by
  have hl := lg_3
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.9596827399877738 27.95968275271279925 (-2.8269415) 0.000000024 (-0.9509043993491) (-0.3094847703727) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_4 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7493792376366):ℝ):ℂ) + ((0.6621410409916:ℝ):ℂ) * I)‖ ≤ 0.00000015966 := by
  have hl := lg_4
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.28119147727 35.28119150272 2.4179204 0.00000005965 (-0.7493792376366) 0.6621410409916 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_5 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9928695176147):ℝ):ℂ) + ((0.1192062101962:ℝ):ℂ) * I)‖ ≤ 0.00000013342 := by
  have hl := lg_5
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.96019485821661905 40.9601948836666445 3.0221023 0.00000003341 (-0.9928695176147) 0.1192062101962 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_6 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0471674662128):ℝ):ℂ) + (((-0.9988869956761):ℝ):ℂ) * I)‖ ≤ 0.00000015383 := by
  have hl := lg_6
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.6002784786227738 45.60027850407279925 (-1.6179813) 0.00000005382 (-0.0471674662128) (-0.9988869956761) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_7 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7370717422698:ℝ):ℂ) + ((0.6758145061682:ℝ):ℂ) * I)‖ ≤ 0.00000014825 := by
  have hl := lg_7
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.5234132802264899 49.5234133056765408 0.7420692 0.00000004824 0.7370717422698 0.6758145061682 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_8 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8845407126807):ℝ):ℂ) + (((-0.4664629969355):ℝ):ℂ) * I)‖ ≤ 0.00000014155 := by
  have hl := lg_8
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.921787215905 52.92178725408 (-2.6563048) 0.00000004154 (-0.8845407126807) (-0.4664629969355) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_9 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8084383579085:ℝ):ℂ) + ((0.588580853802:ℝ):ℂ) * I)‖ ≤ 0.00000014082 := by
  have hl := lg_9
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.9193654799755476 55.9193655054255985 0.6293023 0.00000004081 0.8084383579085 0.588580853802 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_10 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4629554325753):ℝ):ℂ) + (((-0.8863815586101):ℝ):ℂ) * I)‖ ≤ 0.00000016778 := by
  have hl := lg_10
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.60079059685161905 58.6007906350266445 (-2.0521229) 0.00000006777 (-0.4629554325753) (-0.8863815586101) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_11 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2324754296649):ℝ):ℂ) + ((0.9726022694817:ℝ):ℂ) * I)‖ ≤ 0.00000013927 := by
  have hl := lg_11
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.02643467287166485 61.02643471104671575 1.8054184 0.00000003926 (-0.2324754296649) 0.9726022694817 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_12 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.917510542241:ℝ):ℂ) + (((-0.3977114593227):ℝ):ℂ) * I)‖ ≤ 0.00000015455 := by
  have hl := lg_12
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.2408742172577738 63.24087425543279925 (-0.4090212) 0.00000005454 0.917510542241 (-0.3977114593227) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_13 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7677433105672):ℝ):ℂ) + (((-0.6407575274945):ℝ):ℂ) * I)‖ ≤ 0.00000014426 := by
  have hl := lg_13
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.277961127549265 65.2779611657243159 (-2.4461081) 0.00000004425 (-0.7677433105672) (-0.6407575274945) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_14 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3711368133216):ℝ):ℂ) + ((0.9285781958428:ℝ):ℂ) * I)‖ ≤ 0.00000016013 := by
  have hl := lg_14
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.1640090188614899 67.1640090570365408 1.9510293 0.00000006012 (-0.3711368133216) 0.9285781958428 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_15 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9810164992076:ℝ):ℂ) + ((0.1939242849219:ℝ):ℂ) * I)‖ ≤ 0.00000015742 := by
  have hl := lg_15
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.91987759820439285 68.91987763637944375 0.1951608 0.00000005741 0.9810164992076 0.1939242849219 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_16 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1231383915046:ℝ):ℂ) + (((-0.9923895084782):ℝ):ℂ) * I)‖ ≤ 0.00000012648 := by
  have hl := lg_16
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.56238295454 70.56238300544 (-1.4473446) 0.00000002647 0.1231383915046 (-0.9923895084782) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_17 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9885682161688):ℝ):ℂ) + (((-0.1507742736313):ℝ):ℂ) * I)‖ ≤ 0.00000015171 := by
  have hl := lg_17
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.1052795797682453 72.10527963066827075 (-2.9902412) 0.0000000517 (-0.9885682161688) (-0.1507742736313) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_18 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2642884580918):ℝ):ℂ) + ((0.9644436794951:ℝ):ℂ) * I)‖ ≤ 0.00000016756 := by
  have hl := lg_18
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.5599612186105476 73.5599612567855985 1.8382624 0.00000006755 (-0.2642884580918) 0.9644436794951 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_19 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8950505888572:ℝ):ℂ) + ((0.4459646212273:ℝ):ℂ) * I)‖ ≤ 0.00000015197 := by
  have hl := lg_19
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.93597199993904635 74.9359720381141227 0.4622517 0.00000005196 0.8950505888572 0.4459646212273 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p45_20 : ‖exp (-((((((25450:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6651044087691:ℝ):ℂ) + (((-0.7467503769238):ℝ):ℂ) * I)‖ ≤ 0.00000015068 := by
  have hl := lg_20
  refine (ecis_approx ((((25450:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.24138633548661905 76.2413863863866445 (-0.8431627) 0.00000005067 0.6651044087691 (-0.7467503769238) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_2 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5015754680673:ℝ):ℂ) + ((0.8651138941394:ℝ):ℂ) * I)‖ ≤ 0.00000014837 := by
  have hl := lg_2
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.8041784731858 17.8041784860288 1.0453774 0.00000004836 0.5015754680673 0.8651138941394 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_3 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9984669939409):ℝ):ℂ) + (((-0.05535035184):ℝ):ℂ) * I)‖ ≤ 0.00000012419 := by
  have hl := lg_3
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.218955240052100504 28.21895525289512619 (-3.086214) 0.00000002418 (-0.9984669939409) (-0.05535035184) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_4 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4968441864501):ℝ):ℂ) + ((0.8678397630811:ℝ):ℂ) * I)‖ ≤ 0.000000129 := by
  have hl := lg_4
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.6083569463716 35.6083569720576 2.0907549 0.00000002899 (-0.4968441864501) 0.8678397630811 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_5 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8779094439522):ℝ):ℂ) + ((0.4788266994699:ℝ):ℂ) * I)‖ ≤ 0.00000014484 := by
  have hl := lg_5
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.340022205428372374 41.34002223111439806 2.6422749 0.00000004483 (-0.8779094439522) 0.4788266994699 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_6 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4529221913243):ℝ):ℂ) + (((-0.8915500482874):ℝ):ℂ) * I)‖ ≤ 0.00000013703 := by
  have hl := lg_6
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.023133713237900504 46.02313373892392619 (-2.0408366) 0.00000003702 (-0.4529221913243) (-0.8915500482874) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_7 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9602682764371:ℝ):ℂ) + ((0.2790785503556:ℝ):ℂ) * I)‖ ≤ 0.00000014355 := by
  have hl := lg_7
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.982648075280849492 49.982648100966900864 0.2828344 0.00000004354 0.9602682764371 0.2790785503556 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_8 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999850919709):ℝ):ℂ) + ((0.0054603261563:ℝ):ℂ) * I)‖ ≤ 0.00000014507 := by
  have hl := lg_8
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.4125354195574 53.4125354580864 3.1361323 0.00000004506 (-0.9999850919709) 0.0054603261563 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_9 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9938726778389:ℝ):ℂ) + ((0.1105309922391:ℝ):ℂ) * I)‖ ≤ 0.00000014119 := by
  have hl := lg_9
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.437910480104201008 56.43791050579025238 0.1107573 0.00000004118 0.9938726778389 0.1105309922391 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_10 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8545774152446):ℝ):ℂ) + (((-0.5193240233968):ℝ):ℂ) * I)‖ ≤ 0.00000015254 := by
  have hl := lg_10
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.144200678614172374 59.14420071714319806 (-2.5955329) 0.00000005253 (-0.8545774152446) (-0.5193240233968) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_11 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3252548568978:ℝ):ℂ) + ((0.9456263945472:ℝ):ℂ) * I)‖ ≤ 0.00000012382 := by
  have hl := lg_11
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.592337957068038638 61.59233799559709001 1.2395151 0.00000002381 0.3252548568978 0.9456263945472 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_12 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5441177578858:ℝ):ℂ) + (((-0.8390088590434):ℝ):ℂ) * I)‖ ≤ 0.00000015317 := by
  have hl := lg_12
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.827312186423700504 63.82731222495272619 (-0.9954591) 0.00000005316 0.5441177578858 (-0.8390088590434) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_13 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9959386497706):ℝ):ℂ) + (((-0.0900344678405):ℝ):ℂ) * I)‖ ≤ 0.00000014247 := by
  have hl := lg_13
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.8832891757261462 65.883289214255197572 (-3.0514361) 0.00000004246 (-0.9959386497706) (-0.0900344678405) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_14 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2402122787551:ℝ):ℂ) + ((0.9707203825692:ℝ):ℂ) * I)‖ ≤ 0.00000013052 := by
  have hl := lg_14
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.786826548466649492 67.786826586995700864 1.3282118 0.00000003051 0.2402122787551 0.9707203825692 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v25p686_15 : ‖exp (-((((((25686:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9030668301276:ℝ):ℂ) + (((-0.4295000585836):ℝ):ℂ) * I)‖ ≤ 0.00000013351 := by
  have hl := lg_15
  refine (ecis_approx ((((25686:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.558977445480472878 69.55897748400952425 (-0.4439391) 0.0000000335 0.9030668301276 (-0.4295000585836) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_2 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6770599473704:ℝ):ℂ) + ((0.7359278685216:ℝ):ℂ) * I)‖ ≤ 0.00000012646 := by
  have hl := lg_2
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.0225198349803 18.0225198479808 0.8270361 0.00000002645 0.6770599473704 0.7359278685216 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_3 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9580479872816):ℝ):ℂ) + ((0.2866078398071:ℝ):ℂ) * I)‖ ≤ 0.00000012501 := by
  have hl := lg_3
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.565018110900672164 28.565018123901198165 2.8509084 0.000000025 (-0.9580479872816) 0.2866078398071 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_4 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0831796553337):ℝ):ℂ) + ((0.9965345678591:ℝ):ℂ) * I)‖ ≤ 0.0000001529 := by
  have hl := lg_4
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.0450396699606 36.0450396959616 1.6540722 0.00000005289 (-0.0831796553337) 0.9965345678591 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_5 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5349982478352):ℝ):ℂ) + ((0.844853167601:ℝ):ℂ) * I)‖ ≤ 0.00000012344 := by
  have hl := lg_5
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.846995147681348209 41.84699517368237421 2.135302 0.00000002343 (-0.5349982478352) 0.844853167601 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_6 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8595786129511):ℝ):ℂ) + (((-0.5110035303958):ℝ):ℂ) * I)‖ ≤ 0.00000012164 := by
  have hl := lg_6
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.587537945880972164 46.587537971881998165 (-2.6052408) 0.00000002163 (-0.8595786129511) (-0.5110035303958) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_7 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9460010851855:ℝ):ℂ) + (((-0.3241634569593):ℝ):ℂ) * I)‖ ≤ 0.00000014065 := by
  have hl := lg_7
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.595609772069507422 50.595609798070559424 (-0.3301273) 0.00000004064 0.9460010851855 (-0.3241634569593) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_8 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7896951121364):ℝ):ℂ) + ((0.6134994945576:ℝ):ℂ) * I)‖ ≤ 0.00000015969 := by
  have hl := lg_8
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.0675595049409 54.0675595439424 2.4811082 0.00000005968 (-0.7896951121364) 0.6134994945576 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_9 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8357118961315:ℝ):ℂ) + (((-0.5491681224036):ℝ):ℂ) * I)‖ ≤ 0.00000014283 := by
  have hl := lg_9
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.130036221801344328 57.13003624780239633 (-0.5813685) 0.00000004282 0.8357118961315 (-0.5491681224036) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_10 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9839768762248):ℝ):ℂ) + ((0.1782961208298:ℝ):ℂ) * I)‖ ≤ 0.00000014988 := by
  have hl := lg_10
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.869514982661648209 59.86951502166317421 2.9623381 0.00000004987 (-0.9839768762248) 0.1782961208298 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_11 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8850578269084:ℝ):ℂ) + ((0.4654810877234:ℝ):ℂ) * I)‖ ≤ 0.00000013497 := by
  have hl := lg_11
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.347674967753876533 62.347675006755428535 0.4841781 0.00000003496 0.8850578269084 0.4654810877234 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_12 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2059245114956):ℝ):ℂ) + (((-0.9785678798961):ℝ):ℂ) * I)‖ ≤ 0.00000014808 := by
  have hl := lg_12
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.610057780861272164 64.610057819862798165 (-1.7782047) 0.00000004807 (-0.2059245114956) (-0.9785678798961) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_13 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7532528753012):ℝ):ℂ) + ((0.6577310284727:ℝ):ℂ) * I)‖ ≤ 0.00000015591 := by
  have hl := lg_13
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.6912482230808817 66.691248262082433702 2.4237901 0.0000000559 (-0.7532528753012) 0.6577310284727 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_14 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8790603668807:ℝ):ℂ) + ((0.4767104691315:ℝ):ℂ) * I)‖ ≤ 0.00000016709 := by
  have hl := lg_14
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.618129607049807422 68.618129646051359424 0.4969088 0.00000006708 0.8790603668807 0.4767104691315 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p001_15 : ‖exp (-((((((26001:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2704124600748:ℝ):ℂ) + (((-0.962744567077):ℝ):ℂ) * I)‖ ≤ 0.00000012041 := by
  have hl := lg_15
  refine (ecis_approx ((((26001:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.412013258582020373 70.412013297583572375 (-1.2969749) 0.0000000204 0.2704124600748 (-0.962744567077) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p316_2 : ‖exp (-((((((26316:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8203950832674:ℝ):ℂ) + ((0.5717970858186:ℝ):ℂ) * I)‖ ≤ 0.00000012478 := by
  have hl := lg_2
  refine (ecis_approx ((((26316:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.2408611967748 18.2408612099328 0.6086947 0.00000002477 0.8203950832674 0.5717970858186 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p316_3 : ‖exp (-((((((26316:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8040340960078):ℝ):ℂ) + ((0.5945831921658:ℝ):ℂ) * I)‖ ≤ 0.00000015416 := by
  have hl := lg_3
  refine (ecis_approx ((((26316:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.911080981749243824 28.91108099490727014 2.5048455 0.00000005415 (-0.8040340960078) 0.5945831921658 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p316_4 : ‖exp (-((((((26316:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3460961852988:ℝ):ℂ) + ((0.9381990356644:ℝ):ℂ) * I)‖ ≤ 0.00000014954 := by
  have hl := lg_4
  refine (ecis_approx ((((26316:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.4817223935496 36.4817224198656 1.2173894 0.00000004953 0.3460961852988 0.9381990356644 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p316_5 : ‖exp (-((((((26316:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0575009395181):ℝ):ℂ) + ((0.9983454522129:ℝ):ℂ) * I)‖ ≤ 0.00000016034 := by
  have hl := lg_5
  refine (ecis_approx ((((26316:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.353968089934324044 42.35396811625035036 1.628329 0.00000006033 (-0.0575009395181) 0.9983454522129 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p316_6 : ‖exp (-((((((26316:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996065582284):ℝ):ℂ) + ((0.0280486742268:ℝ):ℂ) * I)‖ ≤ 0.00000014742 := by
  have hl := lg_6
  refine (ecis_approx ((((26316:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.151942178524043824 47.15194220484007014 3.1135403 0.00000004741 (-0.9996065582284) 0.0280486742268 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p316_7 : ‖exp (-((((((26316:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5872906681729:ℝ):ℂ) + (((-0.8093760998924):ℝ):ℂ) * I)‖ ≤ 0.00000013775 := by
  have hl := lg_7
  refine (ecis_approx ((((26316:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.208571468858165352 51.208571495174217984 (-0.943089) 0.00000003774 0.5872906681729 (-0.8093760998924) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p316_8 : ‖exp (-((((((26316:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2525239625131):ℝ):ℂ) + ((0.967590640899:ℝ):ℂ) * I)‖ ≤ 0.0000001652 := by
  have hl := lg_8
  refine (ecis_approx ((((26316:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.7225835903244 54.7225836297984 1.8260842 0.00000006519 (-0.2525239625131) 0.967590640899 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p316_9 : ‖exp (-((((((26316:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2929417575979:ℝ):ℂ) + (((-0.9561302874899):ℝ):ℂ) * I)‖ ≤ 0.00000012521 := by
  have hl := lg_9
  refine (ecis_approx ((((26316:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.822161963498487648 57.82216198981454028 (-1.2734942) 0.0000000252 0.2929417575979 (-0.9561302874899) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p316_10 : ‖exp (-((((((26316:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6180245868943):ℝ):ℂ) + ((0.7861587689396:ℝ):ℂ) * I)‖ ≤ 0.0000001544 := by
  have hl := lg_10
  refine (ecis_approx ((((26316:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.594829286709124044 60.59482932618315036 2.2370238 0.00000005439 (-0.6180245868943) 0.7861587689396 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p737_2 : ‖exp (-((((((26737:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.950212306365:ℝ):ℂ) + ((0.311603229817:ℝ):ℂ) * I)‖ ≤ 0.00000015153 := by
  have hl := lg_2
  refine (ecis_approx ((((26737:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.5326761596811 18.5326761730496 0.3168798 0.00000005152 0.950212306365 0.311603229817 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p737_3 : ‖exp (-((((((26737:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4542529484337):ℝ):ℂ) + ((0.8908727512022:ℝ):ℂ) * I)‖ ≤ 0.00000013265 := by
  have hl := lg_3
  refine (ecis_approx ((((26737:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.373596755169080868 29.373596768537607605 2.0423298 0.00000003264 (-0.4542529484337) 0.8908727512022 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p737_4 : ‖exp (-((((((26737:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.805806913553:ℝ):ℂ) + ((0.5921783667698:ℝ):ℂ) * I)‖ ≤ 0.00000012373 := by
  have hl := lg_4
  refine (ecis_approx ((((26737:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.0653523193622 37.0653523460992 0.6337595 0.00000002372 0.805806913553 0.5921783667698 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p737_5 : ‖exp (-((((((26737:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5810682253309:ℝ):ℂ) + ((0.8138548503946:ℝ):ℂ) * I)‖ ≤ 0.00000012735 := by
  have hl := lg_5
  refine (ecis_approx ((((26737:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.031541450850206033 43.03154147758723277 0.9507557 0.00000002734 0.5810682253309 0.8138548503946 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p737_6 : ‖exp (-((((((26737:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.709235497935):ℝ):ℂ) + ((0.7049716366235:ℝ):ℂ) * I)‖ ≤ 0.0000001426 := by
  have hl := lg_6
  refine (ecis_approx ((((26737:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.906272914850180868 47.906272941587207605 2.3592095 0.00000004259 (-0.709235497935) 0.7049716366235 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p737_7 : ‖exp (-((((((26737:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1903521799088):ℝ):ℂ) + (((-0.9817158690798):ℝ):ℂ) * I)‖ ≤ 0.00000011606 := by
  have hl := lg_7
  refine (ecis_approx ((((26737:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.027799641391578014 52.027799668128631488 (-1.7623172) 0.00000001605 (-0.1903521799088) (-0.9817158690798) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p737_8 : ‖exp (-((((((26737:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5811629540989:ℝ):ℂ) + ((0.8137872085399:ℝ):ℂ) * I)‖ ≤ 0.00000015455 := by
  have hl := lg_8
  refine (ecis_approx ((((26737:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.5980284790433 55.5980285191488 0.9506393 0.00000005454 0.5811629540989 0.8137872085399 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p737_9 : ‖exp (-((((((26737:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5873085928033):ℝ):ℂ) + (((-0.8093630933075):ℝ):ℂ) * I)‖ ≤ 0.00000015429 := by
  have hl := lg_9
  refine (ecis_approx ((((26737:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.747193510338161736 58.74719353707521521 (-2.1985258) 0.00000005428 (-0.5873085928033) (-0.8093630933075) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v26p737_10 : ‖exp (-((((((26737:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2985384740017:ℝ):ℂ) + ((0.9543976003431:ℝ):ℂ) * I)‖ ≤ 0.00000016128 := by
  have hl := lg_10
  refine (ecis_approx ((((26737:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.564217610531306033 61.56421765063683277 1.2676354 0.00000006127 0.2985384740017 0.9543976003431 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p158_2 : ‖exp (-((((((27158:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9996858943456:ℝ):ℂ) + ((0.0250621756132:ℝ):ℂ) * I)‖ ≤ 0.00000011464 := by
  have hl := lg_2
  refine (ecis_approx ((((27158:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.8244911225874 18.8244911361664 0.0250648 0.00000001463 0.9996858943456 0.0250621756132 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p158_3 : ‖exp (-((((((27158:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0090175509885):ℝ):ℂ) + ((0.9999593410604:ℝ):ℂ) * I)‖ ≤ 0.00000010732 := by
  have hl := lg_3
  refine (ecis_approx ((((27158:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.836112528588917912 29.83611254216794507 1.579814 0.00000000731 (-0.0090175509885) 0.9999593410604 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p158_4 : ‖exp (-((((((27158:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9987437747071:ℝ):ℂ) + ((0.0501086068843:ℝ):ℂ) * I)‖ ≤ 0.00000012927 := by
  have hl := lg_4
  refine (ecis_approx ((((27158:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.6489822451748 37.6489822723328 0.0501296 0.00000002926 0.9987437747071 0.0501086068843 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p158_5 : ‖exp (-((((((27158:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9629171982817:ℝ):ℂ) + ((0.2697970890378:ℝ):ℂ) * I)‖ ≤ 0.00000013851 := by
  have hl := lg_5
  refine (ecis_approx ((((27158:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.709114811766088022 43.70911483892411518 0.2731823 0.0000000385 0.9629171982817 0.2697970890378 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p158_6 : ‖exp (-((((((27158:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0340758751365):ℝ):ℂ) + ((0.9994192487307:ℝ):ℂ) * I)‖ ≤ 0.00000012091 := by
  have hl := lg_6
  refine (ecis_approx ((((27158:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.660603651176317912 48.66060367833434507 1.6048788 0.0000000209 (-0.0340758751365) 0.9994192487307 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p158_7 : ‖exp (-((((((27158:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8472300095952):ℝ):ℂ) + (((-0.5312262331334):ℝ):ℂ) * I)‖ ≤ 0.00000014353 := by
  have hl := lg_7
  refine (ecis_approx ((((27158:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.847027813924990676 52.847027841083044992 (-2.5815454) 0.00000004352 (-0.8472300095952) (-0.5312262331334) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p158_8 : ‖exp (-((((((27158:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9971742329346:ℝ):ℂ) + ((0.0751235593619:ℝ):ℂ) * I)‖ ≤ 0.0000001439 := by
  have hl := lg_8
  refine (ecis_approx ((((27158:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.4734733677622 56.4734734084992 0.0751944 0.00000004389 0.9971742329346 0.0751235593619 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p158_9 : ‖exp (-((((((27158:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.999837367102):ℝ):ℂ) + (((-0.0180343755785):ℝ):ℂ) * I)‖ ≤ 0.00000011973 := by
  have hl := lg_9
  refine (ecis_approx ((((27158:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.672225057177835824 59.67222508433589014 (-3.1235573) 0.00000001972 (-0.999837367102) (-0.0180343755785) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p158_10 : ‖exp (-((((((27158:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9558530385196:ℝ):ℂ) + ((0.2938451441709:ℝ):ℂ) * I)‖ ≤ 0.00000013746 := by
  have hl := lg_10
  refine (ecis_approx ((((27158:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.533605934353488022 62.53360597509051518 0.2982471 0.00000003745 0.9558530385196 0.2938451441709 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p579_2 : ‖exp (-((((((27579:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9646326293789:ℝ):ℂ) + (((-0.2635979710421):ℝ):ℂ) * I)‖ ≤ 0.00000013606 := by
  have hl := lg_2
  refine (ecis_approx ((((27579:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.1163060854937 19.1163060992832 (-0.2667502) 0.00000003605 0.9646326293789 (-0.2635979710421) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p579_3 : ‖exp (-((((((27579:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.438112744513:ℝ):ℂ) + ((0.8989200315352:ℝ):ℂ) * I)‖ ≤ 0.0000001339 := by
  have hl := lg_3
  refine (ecis_approx ((((27579:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.298628302008754956 30.298628315798282535 1.1172982 0.00000003389 0.438112744513 0.8989200315352 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p579_4 : ‖exp (-((((((27579:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.86103227018:ℝ):ℂ) + (((-0.5085503217073):ℝ):ℂ) * I)‖ ≤ 0.0000001555 := by
  have hl := lg_4
  refine (ecis_approx ((((27579:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.2326121709874 38.2326121985664 (-0.5335003) 0.00000005549 0.86103227018 (-0.5085503217073) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p579_5 : ‖exp (-((((((27579:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9193421841372:ℝ):ℂ) + (((-0.3934589539785):ℝ):ℂ) * I)‖ ≤ 0.00000015002 := by
  have hl := lg_5
  refine (ecis_approx ((((27579:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.386688172681970011 44.38668820026099759 (-0.404391) 0.00000005001 0.9193421841372 (-0.3934589539785) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p579_6 : ‖exp (-((((((27579:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6595712699816:ℝ):ℂ) + ((0.751642029037:ℝ):ℂ) * I)‖ ≤ 0.00000015766 := by
  have hl := lg_6
  refine (ecis_approx ((((27579:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.414934387502454956 49.414934415081482535 0.8505481 0.00000005765 0.6595712699816 0.751642029037 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p579_7 : ‖exp (-((((((27579:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9666002403995):ℝ):ℂ) + ((0.2562888507181:ℝ):ℂ) * I)‖ ≤ 0.00000014944 := by
  have hl := lg_7
  refine (ecis_approx ((((27579:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.666255986458403338 53.666256014037458496 2.8824118 0.00000004943 (-0.9666002403995) 0.2562888507181 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p579_8 : ‖exp (-((((((27579:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.696526989789:ℝ):ℂ) + (((-0.7175305934213):ℝ):ℂ) * I)‖ ≤ 0.00000013325 := by
  have hl := lg_8
  refine (ecis_approx ((((27579:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.3489182564811 57.3489182978496 (-0.8002505) 0.00000003324 0.696526989789 (-0.7175305934213) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p579_9 : ‖exp (-((((((27579:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6161145249551):ℝ):ℂ) + ((0.7876565826082:ℝ):ℂ) * I)‖ ≤ 0.00000015982 := by
  have hl := lg_9
  refine (ecis_approx ((((27579:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.597256604017509912 60.59725663159656507 2.2345965 0.00000005981 (-0.6161145249551) 0.7876565826082 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v27p579_10 : ‖exp (-((((((27579:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7831124864262:ℝ):ℂ) + (((-0.6218800797609):ℝ):ℂ) * I)‖ ≤ 0.00000012776 := by
  have hl := lg_10
  refine (ecis_approx ((((27579:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.502994258175670011 63.50299429954419759 (-0.6711412) 0.00000002775 0.7831124864262 (-0.6218800797609) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v28_2 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8480164376045:ℝ):ℂ) + (((-0.5299699251396):ℝ):ℂ) * I)‖ ≤ 0.00000014088 := by
  have hl := lg_2
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.4081210484 19.4081210624 (-0.5585651) 0.00000004087 0.8480164376045 (-0.5299699251396) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v28_3 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.793180401478:ℝ):ℂ) + ((0.6089867409979:ℝ):ℂ) * I)‖ ≤ 0.00000015355 := by
  have hl := lg_3
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.761144075428592 30.76114408942862 0.6547825 0.00000005354 0.793180401478 0.6089867409979 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v28_4 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4382636670103:ℝ):ℂ) + (((-0.8988464597353):ℝ):ℂ) * I)‖ ≤ 0.00000014629 := by
  have hl := lg_4
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.8162420968 38.8162421248 (-1.1171303) 0.00000004628 0.4382636670103 (-0.8988464597353) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v28_5 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4695949379756:ℝ):ℂ) + (((-0.8828819820495):ℝ):ℂ) * I)‖ ≤ 0.00000011667 := by
  have hl := lg_5
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.064261533597852 45.06426156159788 (-1.0819644) 0.00000001666 0.4695949379756 (-0.8828819820495) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v28_6 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9953746855837:ℝ):ℂ) + ((0.0960689091184:ℝ):ℂ) * I)‖ ≤ 0.00000013362 := by
  have hl := lg_6
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.169265123828592 50.16926515182862 0.0962173 0.00000003361 0.9953746855837 0.0960689091184 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v28_7 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4727309146966):ℝ):ℂ) + ((0.8812068328632:ℝ):ℂ) * I)‖ ≤ 0.00000012239 := by
  have hl := lg_7
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.485484158991816 54.485484186991872 2.0631836 0.00000002238 (-0.4727309146966) 0.8812068328632 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v28_8 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1047067973484):ℝ):ℂ) + (((-0.9945031355348):ℝ):ℂ) * I)‖ ≤ 0.0000001226 := by
  have hl := lg_8
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.2243631452 58.2243631872 (-1.6756954) 0.00000002259 (-0.1047067973484) (-0.9945031355348) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v28_9 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2582703951848:ℝ):ℂ) + ((0.9660726696119:ℝ):ℂ) * I)‖ ≤ 0.00000012095 := by
  have hl := lg_9
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.522288150857184 61.52228817885724 1.3095649 0.00000002094 0.2582703951848 0.9660726696119 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v28_10 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0696766715148):ℝ):ℂ) + (((-0.9975696273676):ℝ):ℂ) * I)‖ ≤ 0.00000015222 := by
  have hl := lg_10
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.472382581997852 64.47238262399788 (-1.6405295) 0.00000005221 (-0.0696766715148) (-0.9975696273676) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
