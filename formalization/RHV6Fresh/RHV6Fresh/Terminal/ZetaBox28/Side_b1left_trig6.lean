/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 6

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

lemma cs_b1left_v20p756_18 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9546555305257):ℝ):ℂ) + ((0.2977126430306:ℝ):ℂ) * I)‖ ≤ 0.00000015006 := by
  have hl := lg_18
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.992556190706503968 59.99255622184054548 2.8392969 0.00000005005 (-0.9546555305257) 0.2977126430306 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_19 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1457601381634):ℝ):ℂ) + ((0.9893199594277:ℝ):ℂ) * I)‖ ≤ 0.00000013642 := by
  have hl := lg_19
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.114775435392331868 61.114775466526394136 1.7170776 0.00000003641 (-0.1457601381634) 0.9893199594277 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_20 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7946084181512:ℝ):ℂ) + ((0.6071222791195:ℝ):ℂ) * I)‖ ≤ 0.00000012351 := by
  have hl := lg_20
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.179419048304922004 62.17941908981694276 0.652434 0.0000000235 0.7946084181512 0.6071222791195 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_21 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9358071043262:ℝ):ℂ) + (((-0.3525125011864):ℝ):ℂ) * I)‖ ≤ 0.00000016055 := by
  have hl := lg_21
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.192107701201071016 63.192107732335133284 (-0.3602546) 0.00000006054 0.9358071043262 (-0.3525125011864) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_22 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2425293808721:ℝ):ℂ) + (((-0.970144061165):ℝ):ℂ) * I)‖ ≤ 0.00000013149 := by
  have hl := lg_22
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.157677140323470948 64.15767718183551246 (-1.3258241) 0.00000003148 0.2425293808721 (-0.970144061165) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_23 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6269784628705):ℝ):ℂ) + (((-0.7790365890522):ℝ):ℂ) * I)‖ ≤ 0.00000014757 := by
  have hl := lg_23
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.080317924243680696 65.080317965755742964 (-2.2484649) 0.00000004756 (-0.6269784628705) (-0.7790365890522) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_24 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.999952366822):ℝ):ℂ) + (((-0.0097602983206):ℝ):ℂ) * I)‖ ≤ 0.00000015085 := by
  have hl := lg_24
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.963685281120251984 65.96368532263227274 (-3.1318322) 0.00000005084 (-0.999952366822) (-0.0097602983206) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_25 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6692919922421):ℝ):ℂ) + ((0.7429994812255:ℝ):ℂ) * I)‖ ≤ 0.00000016193 := by
  have hl := lg_25
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.810986599382644008 66.81098664089468552 2.3040518 0.00000006192 (-0.6692919922421) 0.7429994812255 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_26 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0807218047334:ℝ):ℂ) + ((0.9967366704604:ℝ):ℂ) * I)‖ ≤ 0.0000001574 := by
  have hl := lg_26
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.6250517215921652 67.625051763104206712 1.4899866 0.00000005739 0.0807218047334 0.9967366704604 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_27 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7605422985474:ℝ):ℂ) + ((0.6492883890231:ℝ):ℂ) * I)‖ ≤ 0.00000012677 := by
  have hl := lg_27
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.408389974599555952 68.40839000573361822 0.7066484 0.00000002676 0.7605422985474 0.6492883890231 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_28 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.998838681965:ℝ):ℂ) + (((-0.0481797406647):ℝ):ℂ) * I)‖ ≤ 0.00000015417 := by
  have hl := lg_28
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.163236791614819032 69.163236833126860544 (-0.0481984) 0.00000005416 0.998838681965 (-0.0481797406647) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_29 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7133328831618:ℝ):ℂ) + (((-0.7008253689758):ℝ):ℂ) * I)‖ ≤ 0.00000015337 := by
  have hl := lg_29
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.891592225617539152 69.89159226712960142 (-0.7765539) 0.00000005336 0.7133328831618 (-0.7008253689758) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_30 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0904580059389:ℝ):ℂ) + (((-0.9959002706905):ℝ):ℂ) * I)‖ ≤ 0.00000014679 := by
  have hl := lg_30
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.595252832197973988 70.5952528737100155 (-1.4802145) 0.00000004678 0.0904580059389 (-0.9959002706905) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_31 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5563640751241):ℝ):ℂ) + (((-0.8309386354613):ℝ):ℂ) * I)‖ ≤ 0.00000015726 := by
  have hl := lg_31
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.275838394711954428 71.275838436224016696 (-2.1608) 0.00000005725 (-0.5563640751241) (-0.8309386354613) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_32 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9486623935072):ℝ):ℂ) + (((-0.3162904724227):ℝ):ℂ) * I)‖ ≤ 0.00000014446 := by
  have hl := lg_32
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.934814371534 71.934814423424 (-2.819776) 0.00000004445 (-0.9486623935072) (-0.3162904724227) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_33 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9502122584333):ℝ):ℂ) + ((0.3116033756542:ℝ):ℂ) * I)‖ ≤ 0.00000016195 := by
  have hl := lg_33
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.573510924216522932 72.5735109657285852 2.8247127 0.00000006194 (-0.9502122584333) 0.3116033756542 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_34 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5926043730667):ℝ):ℂ) + ((0.8054936728558:ℝ):ℂ) * I)‖ ≤ 0.00000016421 := by
  have hl := lg_34
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.193139021955904104 73.19313907384592486 2.2050846 0.0000000642 (-0.5926043730667) 0.8054936728558 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_35 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0326171869676):ℝ):ℂ) + ((0.9994679180014:ℝ):ℂ) * I)‖ ≤ 0.00000014348 := by
  have hl := lg_35
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.794804342692541036 73.794804384204603304 1.6034193 0.00000004347 (-0.0326171869676) 0.9994679180014 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_36 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5244693325546:ℝ):ℂ) + ((0.8514293389411:ℝ):ℂ) * I)‖ ≤ 0.00000012116 := by
  have hl := lg_36
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.379519065013303968 74.37951910652534548 1.0187046 0.00000002115 0.5244693325546 0.8514293389411 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_37 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9004421001895:ℝ):ℂ) + ((0.4349758892241:ℝ):ℂ) * I)‖ ≤ 0.00000012863 := by
  have hl := lg_37
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.948212173261798152 74.94821221477386042 0.4500115 0.00000002862 0.9004421001895 0.4349758892241 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_38 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9946471461293:ℝ):ℂ) + (((-0.1033298344955):ℝ):ℂ) * I)‖ ≤ 0.00000016507 := by
  have hl := lg_38
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.501738309699131868 75.501738351211194136 (-0.1035146) 0.00000006506 0.9946471461293 (-0.1033298344955) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_39 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8005033034412:ℝ):ℂ) + (((-0.5993283417124):ℝ):ℂ) * I)‖ ≤ 0.00000016086 := by
  have hl := lg_39
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.040885505485217184 76.040885546997279452 (-0.6426618) 0.00000006085 0.8005033034412 (-0.5993283417124) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_40 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3918467680559:ℝ):ℂ) + (((-0.9200304942577):ℝ):ℂ) * I)‖ ≤ 0.00000016356 := by
  have hl := lg_40
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.566381922611722004 76.56638197450174276 (-1.1681583) 0.00000006355 0.3918467680559 (-0.9200304942577) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_41 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1096607878266):ℝ):ℂ) + (((-0.9939690697465):ℝ):ℂ) * I)‖ ≤ 0.00000015529 := by
  have hl := lg_41
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.07890178953746248 77.078901841427503992 (-1.6806781) 0.00000005528 (-0.1096607878266) (-0.9939690697465) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_42 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5729089115946):ℝ):ℂ) + (((-0.819619045048):ℝ):ℂ) * I)‖ ≤ 0.00000013088 := by
  have hl := lg_42
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.579070575507871016 77.579070617019933284 (-2.1808469) 0.00000003087 (-0.5729089115946) (-0.819619045048) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_43 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.89050302158):ℝ):ℂ) + (((-0.4549773274029):ℝ):ℂ) * I)‖ ≤ 0.00000013513 := by
  have hl := lg_43
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.06746957975385768 78.067469621265940704 (-2.6692459) 0.00000003512 (-0.89050302158) (-0.4549773274029) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_44 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999883658692):ℝ):ℂ) + ((0.0048236345837:ℝ):ℂ) * I)‖ ≤ 0.0000001732 := by
  have hl := lg_44
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.544640014630270948 78.54464006652031246 3.136769 0.00000007319 (-0.9999883658692) 0.0048236345837 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_45 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8909922885976):ℝ):ℂ) + ((0.4540184374593:ℝ):ℂ) * I)‖ ≤ 0.00000016428 := by
  have hl := lg_45
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.011086616091025972 79.01108665760308824 2.6703224 0.00000006427 (-0.8909922885976) 0.4540184374593 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_46 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.599864602937):ℝ):ℂ) + ((0.8001015298893:ℝ):ℂ) * I)‖ ≤ 0.00000015712 := by
  have hl := lg_46
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.467280798550480696 79.467280850440542964 2.2141282 0.00000005711 (-0.599864602937) 0.8001015298893 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_47 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1956782994291):ℝ):ℂ) + ((0.9806681411832:ℝ):ℂ) * I)‖ ≤ 0.00000015269 := by
  have hl := lg_47
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.913663594116788724 79.913663646006871748 1.7677454 0.00000005268 (-0.1956782994291) 0.9806681411832 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_48 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2377371348021:ℝ):ℂ) + ((0.9713295294266:ℝ):ℂ) * I)‖ ≤ 0.00000013792 := by
  have hl := lg_48
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.350648155427051984 80.35064820731707274 1.3307608 0.00000003791 0.2377371348021 0.9713295294266 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_49 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6194245033699:ℝ):ℂ) + ((0.7850562302313:ℝ):ℂ) * I)‖ ≤ 0.00000013419 := by
  have hl := lg_49
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.778622086002438064 80.778622127514521088 0.9027869 0.00000003418 0.6194245033699 0.7850562302313 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_50 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8853920930735:ℝ):ℂ) + ((0.4648449650398:ℝ):ℂ) * I)‖ ≤ 0.00000013226 := by
  have hl := lg_50
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.197949473689444008 81.19794952557948552 0.4834595 0.00000003225 0.8853920930735 0.4648449650398 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_2 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2746396994878):ℝ):ℂ) + (((-0.9615472091706):ℝ):ℂ) * I)‖ ≤ 0.00000010568 := by
  have hl := lg_2
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.4153819086991 14.4153819190976 (-1.8490113) 0.00000000567 (-0.2746396994878) (-0.9615472091706) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_3 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6549414766392):ℝ):ℂ) + ((0.7556796028478:ℝ):ℂ) * I)‖ ≤ 0.00000014372 := by
  have hl := lg_3
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.847839762024586708 22.847839772423107505 2.2849015 0.00000004371 (-0.6549414766392) 0.7556796028478 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_4 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8491460671208):ℝ):ℂ) + ((0.5281580791961:ℝ):ℂ) * I)‖ ≤ 0.00000011851 := by
  have hl := lg_4
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.8307638173982 28.8307638381952 2.5851627 0.0000000185 (-0.8491460671208) 0.5281580791961 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_5 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.465993699881):ℝ):ℂ) + (((-0.8847880377052):ℝ):ℂ) * I)‖ ≤ 0.00000013899 := by
  have hl := lg_5
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.471480254079804573 33.47148027487682537 (-2.0555537) 0.00000003898 (-0.465993699881) (-0.8847880377052) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_6 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9064945434823:ℝ):ℂ) + ((0.4222175299971:ℝ):ℂ) * I)‖ ≤ 0.00000014846 := by
  have hl := lg_6
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.263221670723686708 37.263221691520707505 0.4358902 0.00000004845 0.9064945434823 0.4222175299971 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_7 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9317435177281):ℝ):ℂ) + (((-0.3631170844354):ℝ):ℂ) * I)‖ ≤ 0.00000013683 := by
  have hl := lg_7
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.469093359091171334 40.469093379888212928 (-2.7699815) 0.00000003682 (-0.9317435177281) (-0.3631170844354) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_8 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7410581477913:ℝ):ℂ) + ((0.6714408548726:ℝ):ℂ) * I)‖ ≤ 0.00000012417 := by
  have hl := lg_8
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.2461457260973 43.2461457572928 0.7361514 0.00000002416 0.7410581477913 0.6714408548726 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_9 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1421034162289):ℝ):ℂ) + (((-0.989851816736):ℝ):ℂ) * I)‖ ≤ 0.00000012622 := by
  have hl := lg_9
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.695679524049173416 45.69567954484621501 (-1.7133824) 0.00000002621 (-0.1421034162289) (-0.989851816736) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_10 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7227850937021):ℝ):ℂ) + ((0.691072867572:ℝ):ℂ) * I)‖ ≤ 0.00000013655 := by
  have hl := lg_10
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.886862162778904573 47.88686219397442537 2.3786203 0.00000003654 (-0.7227850937021) 0.691072867572 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_11 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.922435884718:ℝ):ℂ) + ((0.3861502797934:ℝ):ℂ) * I)‖ ≤ 0.00000014594 := by
  have hl := lg_11
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.869027972169430801 49.869028003364972395 0.3964545 0.00000004593 0.922435884718 0.3861502797934 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_12 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1570226986228:ℝ):ℂ) + (((-0.9875949939713):ℝ):ℂ) * I)‖ ≤ 0.0000001532 := by
  have hl := lg_12
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.678603579422786708 51.678603610618307505 (-1.4131211) 0.00000005319 0.1570226986228 (-0.9875949939713) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_13 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9979639807824):ℝ):ℂ) + (((-0.0637800322705):ℝ):ℂ) * I)‖ ≤ 0.00000014468 := by
  have hl := lg_13
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.3432517709093149 53.343251802104856494 (-3.0777693) 0.00000004467 (-0.9979639807824) (-0.0637800322705) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_14 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0932604523526):ℝ):ℂ) + ((0.9956417468279:ℝ):ℂ) * I)‖ ≤ 0.00000013438 := by
  have hl := lg_14
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.884475267790271334 54.884475298985812928 1.6641925 0.00000003437 (-0.0932604523526) 0.9956417468279 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_15 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9738148975882:ℝ):ℂ) + ((0.2273423524891:ℝ):ℂ) * I)‖ ≤ 0.00000014853 := by
  have hl := lg_15
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.319320016104391281 56.319320047299932875 0.2293477 0.00000004852 0.9738148975882 0.2273423524891 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_16 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4420980931142:ℝ):ℂ) + (((-0.8969667084484):ℝ):ℂ) * I)‖ ≤ 0.00000012983 := by
  have hl := lg_16
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.6615276347964 57.6615276763904 (-1.1128599) 0.00000002982 0.4420980931142 (-0.8969667084484) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_17 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7193553725104):ℝ):ℂ) + (((-0.6946422446218):ℝ):ℂ) * I)‖ ≤ 0.00000016992 := by
  have hl := lg_17
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.922337894712777898 58.922337936306798695 (-2.3736702) 0.00000006991 (-0.7193553725104) (-0.6946422446218) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_18 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9127620093732):ℝ):ℂ) + ((0.4084917552566:ℝ):ℂ) * I)‖ ≤ 0.00000013906 := by
  have hl := lg_18
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.111061432748273416 60.11106146394381501 2.7207916 0.00000003905 (-0.9127620093732) 0.4084917552566 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_19 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0255564904175):ℝ):ℂ) + ((0.9996733795582:ℝ):ℂ) * I)‖ ≤ 0.0000001383 := by
  have hl := lg_19
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.235497433506182591 61.235497464701744982 1.5963556 0.00000003829 (-0.0255564904175) 0.9996733795582 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_20 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8630046680927:ℝ):ℂ) + ((0.5051959450057:ℝ):ℂ) * I)‖ ≤ 0.00000014129 := by
  have hl := lg_20
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.302244071478004573 62.30224411307202537 0.529609 0.00000004128 0.8630046680927 0.5051959450057 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_21 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8846376029809:ℝ):ℂ) + (((-0.4662792204164):ℝ):ℂ) * I)‖ ≤ 0.0000001507 := by
  have hl := lg_21
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.316933121115758042 63.316933152311320433 (-0.4850801) 0.00000005069 0.8846376029809 (-0.4662792204164) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_22 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1179642096806:ℝ):ℂ) + (((-0.9930178473896):ℝ):ℂ) * I)‖ ≤ 0.00000015068 := by
  have hl := lg_22
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.284409880868530801 64.284409922462572395 (-1.4525568) 0.00000005067 0.1179642096806 (-0.9930178473896) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_23 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7216783139754):ℝ):ℂ) + (((-0.6922285829912):ℝ):ℂ) * I)‖ ≤ 0.00000015687 := by
  have hl := lg_23
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.208873187054144702 65.208873228648207093 (-2.3770201) 0.00000005686 (-0.7216783139754) (-0.6922285829912) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_24 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9927438759475):ℝ):ℂ) + ((0.1202480616404:ℝ):ℂ) * I)‖ ≤ 0.00000015076 := by
  have hl := lg_24
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.093985488121886708 66.093985529715907505 3.0210529 0.00000005075 (-0.9927438759475) 0.1202480616404 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_25 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5656997374215):ℝ):ℂ) + ((0.8246113066601:ℝ):ℂ) * I)‖ ≤ 0.00000017079 := by
  have hl := lg_25
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.942960508159609146 66.94296054975365074 2.1720779 0.00000007078 (-0.5656997374215) 0.8246113066601 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_26 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2127530225953:ℝ):ℂ) + ((0.9771060082593:ℝ):ℂ) * I)‖ ≤ 0.00000014224 := by
  have hl := lg_26
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.7586336796084149 67.758633721202456494 1.3564047 0.00000004223 0.2127530225953 0.9771060082593 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_27 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8410802490199:ℝ):ℂ) + ((0.5409103573686:ℝ):ℂ) * I)‖ ≤ 0.00000013831 := by
  have hl := lg_27
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.543519286073760124 68.543519317269322515 0.5715191 0.0000000383 0.8410802490199 0.5409103573686 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_28 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9829695656053:ℝ):ℂ) + (((-0.1837684224606):ℝ):ℂ) * I)‖ ≤ 0.00000013912 := by
  have hl := lg_28
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.299857176489371334 69.299857218083412928 (-0.1848188) 0.00000003911 0.9829695656053 (-0.1837684224606) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_29 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6100972514821:ℝ):ℂ) + (((-0.7923265385774):ℝ):ℂ) * I)‖ ≤ 0.00000012439 := by
  have hl := lg_29
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.029651354604353524 70.029651396198415915 (-0.914613) 0.00000002438 0.6100972514821 (-0.7923265385774) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_30 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0488478262679):ℝ):ℂ) + (((-0.9988062323938):ℝ):ℂ) * I)‖ ≤ 0.00000015419 := by
  have hl := lg_30
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.734701924803491281 70.734701966397532875 (-1.6196636) 0.00000005418 (-0.0488478262679) (-0.9988062323938) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_31 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6674634561124):ℝ):ℂ) + (((-0.7446425550125):ℝ):ℂ) * I)‖ ≤ 0.00000013269 := by
  have hl := lg_31
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.416631870053214311 71.416631911647276702 (-2.3015935) 0.00000003268 (-0.6674634561124) (-0.7446425550125) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_32 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9838935225179):ℝ):ℂ) + (((-0.1787555201831):ℝ):ℂ) * I)‖ ≤ 0.00000013549 := by
  have hl := lg_32
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.0769095434955 72.076909595488 (-2.9618712) 0.00000003548 (-0.9838935225179) (-0.1787555201831) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_33 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8959473660732):ℝ):ℂ) + ((0.4441602381063:ℝ):ℂ) * I)‖ ≤ 0.00000015198 := by
  have hl := lg_33
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.716867734194017509 72.7168677757880799 2.6813559 0.00000005197 (-0.8959473660732) 0.4441602381063 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_34 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4703678502825):ℝ):ℂ) + ((0.8824704444997:ℝ):ℂ) * I)‖ ≤ 0.00000016926 := by
  have hl := lg_34
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.337719803411877898 73.337719855404398695 2.0605039 0.00000006925 (-0.4703678502825) 0.8824704444997 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_35 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1129049636531:ℝ):ℂ) + ((0.9936057916409:ℝ):ℂ) * I)‖ ≤ 0.00000016863 := by
  have hl := lg_35
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.940573613170975907 73.940573654765038298 1.4576501 0.00000006862 0.1129049636531 0.9936057916409 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_36 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6434647912739:ℝ):ℂ) + ((0.7654757098634:ℝ):ℂ) * I)‖ ≤ 0.00000014472 := by
  have hl := lg_36
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.526443341447373416 74.52644338304141501 0.8717803 0.00000004471 0.6434647912739 0.7654757098634 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_37 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9547542750452:ℝ):ℂ) + ((0.2973958208901:ℝ):ℂ) * I)‖ ≤ 0.00000016309 := by
  have hl := lg_37
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.096259807637580274 75.096259849231642665 0.3019639 0.00000006308 0.9547542750452 0.2973958208901 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_38 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9682519750455:ℝ):ℂ) + (((-0.2499762245105):ℝ):ℂ) * I)‖ ≤ 0.00000014396 := by
  have hl := lg_38
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.650879342205282591 75.650879383799344982 (-0.2526557) 0.00000004395 0.9682519750455 (-0.2499762245105) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_39 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7018052017857:ℝ):ℂ) + (((-0.7123689063586):ℝ):ℂ) * I)‖ ≤ 0.00000015324 := by
  have hl := lg_39
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.191091532933901608 76.191091574527963999 (-0.7928679) 0.00000005323 0.7018052017857 (-0.7123689063586) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p797_40 : ‖exp (-((((((20797:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2487544083035:ℝ):ℂ) + (((-0.9685665926252):ℝ):ℂ) * I)‖ ≤ 0.00000014603 := by
  have hl := lg_40
  refine (ecis_approx ((((20797:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.717625980177104573 76.71762603216962537 (-1.3194023) 0.00000004602 0.2487544083035 (-0.9685665926252) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_2 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3018513340066):ℝ):ℂ) + (((-0.9533550084605):ℝ):ℂ) * I)‖ ≤ 0.00000013917 := by
  have hl := lg_2
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.4438009430914 14.4438009535104 (-1.8774303) 0.00000003916 (-0.3018513340066) (-0.9533550084605) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_3 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6202505466576):ℝ):ℂ) + ((0.7844037604176:ℝ):ℂ) * I)‖ ≤ 0.00000014756 := by
  have hl := lg_3
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.892882865849321432 22.89288287626834227 2.2398584 0.00000004755 (-0.6202505466576) 0.7844037604176 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_4 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8177714826182):ℝ):ℂ) + ((0.5755430497885:ℝ):ℂ) * I)‖ ≤ 0.00000014973 := by
  have hl := lg_4
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.8876018861828 28.8876019070208 2.5283246 0.00000004972 (-0.8177714826182) 0.5755430497885 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_5 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5233216804745):ℝ):ℂ) + (((-0.8521352115352):ℝ):ℂ) * I)‖ ≤ 0.00000012744 := by
  have hl := lg_5
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.537467208468287142 33.53746722930630798 (-2.1215407) 0.00000002743 (-0.5233216804745) (-0.8521352115352) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_6 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9350387440393:ℝ):ℂ) + ((0.3545455501701:ℝ):ℂ) * I)‖ ≤ 0.00000013415 := by
  have hl := lg_6
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.336683808940721432 37.33668382977874227 0.362428 0.00000003414 0.9350387440393 0.3545455501701 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_7 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9577193084465):ℝ):ℂ) + (((-0.2877042335507):ℝ):ℂ) * I)‖ ≤ 0.00000015296 := by
  have hl := lg_7
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.548875675181123636 40.548875696019165312 (-2.8497638) 0.00000005295 (-0.9577193084465) (-0.2877042335507) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_8 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7955422620756:ℝ):ℂ) + ((0.6058981013765:ℝ):ℂ) * I)‖ ≤ 0.000000121 := by
  have hl := lg_8
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.3314028292742 43.3314028605312 0.6508943 0.00000002099 0.7955422620756 0.6058981013765 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_9 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2305786090584):ℝ):ℂ) + (((-0.9730537010071):ℝ):ℂ) * I)‖ ≤ 0.00000011857 := by
  have hl := lg_9
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.785765731698642864 45.78576575253668454 (-1.8034686) 0.00000001856 (-0.2305786090584) (-0.9730537010071) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_10 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.654422019011):ℝ):ℂ) + ((0.7561295001627:ℝ):ℂ) * I)‖ ≤ 0.0000001254 := by
  have hl := lg_10
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.981268151559687142 47.98126818281670798 2.2842143 0.00000002539 (-0.654422019011) 0.7561295001627 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_11 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.955884268858:ℝ):ℂ) + ((0.2937435353329:ℝ):ℂ) * I)‖ ≤ 0.00000015216 := by
  have hl := lg_11
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.967341678322190654 49.96734170957923233 0.2981408 0.00000005215 0.955884268858 0.2937435353329 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_12 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0557650837464:ℝ):ℂ) + (((-0.9984439170202):ℝ):ℂ) * I)‖ ≤ 0.00000012587 := by
  have hl := lg_12
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.780484752032121432 51.78048478328914227 (-1.5150023) 0.00000002586 0.0557650837464 (-0.9984439170202) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_13 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9991456420519):ℝ):ℂ) + ((0.0413277797286:ℝ):ℂ) * I)‖ ≤ 0.00000016119 := by
  have hl := lg_13
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.4484146945332646 53.448414725790306276 3.1002531 0.00000006118 (-0.9991456420519) 0.0413277797286 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_14 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0148046859295:ℝ):ℂ) + ((0.9998904046316:ℝ):ℂ) * I)‖ ≤ 0.00000014636 := by
  have hl := lg_14
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.992676618272523636 54.992676649529565312 1.5559911 0.00000004635 0.0148046859295 0.9998904046316 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_15 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9930086227151:ℝ):ℂ) + ((0.1180418367079:ℝ):ℂ) * I)‖ ≤ 0.00000014097 := by
  have hl := lg_15
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.430350074317608574 56.43035010557465025 0.1183177 0.00000004096 0.9930086227151 0.1180418367079 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_16 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3375004964985:ℝ):ℂ) + (((-0.941325350165):ℝ):ℂ) * I)‖ ≤ 0.00000014944 := by
  have hl := lg_16
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.7752037723656 57.7752038140416 (-1.226536) 0.00000004943 0.3375004964985 (-0.941325350165) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_17 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7950169809234):ℝ):ℂ) + (((-0.606587174276):ℝ):ℂ) * I)‖ ≤ 0.00000012285 := by
  have hl := lg_17
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.038499641776451692 59.03849968345247253 (-2.4898319) 0.00000002284 (-0.7950169809234) (-0.606587174276) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_18 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.858065154913):ℝ):ℂ) + ((0.5135408356158:ℝ):ℂ) * I)‖ ≤ 0.00000013427 := by
  have hl := lg_18
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.229566674790042864 60.22956670604708454 2.6022864 0.00000003426 (-0.858065154913) 0.5135408356158 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_19 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0950191604202:ℝ):ℂ) + ((0.9954754437719:ℝ):ℂ) * I)‖ ≤ 0.00000014019 := by
  have hl := lg_19
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.356219431620033314 61.356219462877095828 1.4756336 0.00000004018 0.0950191604202 0.9954754437719 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_20 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9183980054771:ℝ):ℂ) + ((0.3956578111646:ℝ):ℂ) * I)‖ ≤ 0.00000016455 := by
  have hl := lg_20
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.425069094651087142 62.42506913632710798 0.406784 0.00000006454 0.9183980054771 0.3956578111646 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_21 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8197021501605:ℝ):ℂ) + (((-0.572790000805):ℝ):ℂ) * I)‖ ≤ 0.00000013078 := by
  have hl := lg_21
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.441758541030445068 63.441758572287507582 (-0.6099055) 0.00000003077 0.8197021501605 (-0.572790000805) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_22 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0084931710942):ℝ):ℂ) + (((-0.9999639323718):ℝ):ℂ) * I)‖ ≤ 0.0000001504 := by
  have hl := lg_22
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.411142621413590654 64.41114266308963233 (-1.5792896) 0.00000005039 (-0.0084931710942) (-0.9999639323718) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_23 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.804467868065):ℝ):ℂ) + (((-0.5939961693479):ℝ):ℂ) * I)‖ ≤ 0.00000012195 := by
  have hl := lg_23
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.337428449864608708 65.337428491540671222 (-2.5055754) 0.00000002194 (-0.804467868065) (-0.5939961693479) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_24 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.968704271994):ℝ):ℂ) + ((0.2482177132167:ℝ):ℂ) * I)‖ ≤ 0.00000015784 := by
  have hl := lg_24
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.224285695123521432 66.22428573679954227 2.8907527 0.00000005783 (-0.968704271994) 0.2482177132167 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_25 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4522688310869):ℝ):ℂ) + ((0.8918816650334:ℝ):ℂ) * I)‖ ≤ 0.00000016205 := by
  have hl := lg_25
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.074934416936574284 67.07493445861261596 2.0401039 0.00000006204 (-0.4522688310869) 0.8918816650334 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_26 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.340993585062:ℝ):ℂ) + ((0.940065622681:ℝ):ℂ) * I)‖ ≤ 0.00000014137 := by
  have hl := lg_26
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.8922156376246646 67.892215679300706276 1.2228227 0.00000004136 0.340993585062 0.940065622681 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_27 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9062834904825:ℝ):ℂ) + ((0.4226703619594:ℝ):ℂ) * I)‖ ≤ 0.00000014984 := by
  have hl := lg_27
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.678648597547964296 68.67864862880502681 0.4363898 0.00000004983 0.9062834904825 0.4226703619594 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_28 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9487817109708:ℝ):ℂ) + (((-0.3159323739779):ℝ):ℂ) * I)‖ ≤ 0.00000012408 := by
  have hl := lg_28
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.436477561363923636 69.436477603039965312 (-0.3214392) 0.00000002407 0.9487817109708 (-0.3159323739779) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_29 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4952514326919:ℝ):ℂ) + (((-0.8687496868585):ℝ):ℂ) * I)‖ ≤ 0.00000014631 := by
  have hl := lg_29
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.167710483591167896 70.16771052526723041 (-1.0526721) 0.0000000463 0.4952514326919 (-0.8687496868585) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_30 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1872052994452):ℝ):ℂ) + (((-0.9823208110688):ℝ):ℂ) * I)‖ ≤ 0.00000016158 := by
  have hl := lg_30
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.874151017409008574 70.87415105908505025 (-1.7591127) 0.00000006157 (-0.1872052994452) (-0.9823208110688) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_31 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7653536779287):ℝ):ℂ) + (((-0.6436099343882):ℝ):ℂ) * I)‖ ≤ 0.0000001336 := by
  have hl := lg_31
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.557425345394474194 71.557425387070536708 (-2.442387) 0.00000003359 (-0.7653536779287) (-0.6436099343882) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_32 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9992922157394):ℝ):ℂ) + (((-0.0376173758124):ℝ):ℂ) * I)‖ ≤ 0.00000016353 := by
  have hl := lg_32
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.219004715457 72.219004767552 (-3.1039664) 0.00000006352 (-0.9992922157394) (-0.0376173758124) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_33 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8233012172438):ℝ):ℂ) + ((0.5676047089531:ℝ):ℂ) * I)‖ ≤ 0.000000142 := by
  have hl := lg_33
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.860224544171512086 72.8602245858475746 2.5379991 0.00000004199 (-0.8233012172438) 0.5676047089531 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_34 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3383159776813):ℝ):ℂ) + ((0.9410325707665:ℝ):ℂ) * I)‖ ≤ 0.00000015082 := by
  have hl := lg_34
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.482300584867851692 73.48230063696287253 1.9159231 0.00000005081 (-0.3383159776813) 0.9410325707665 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_35 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2560323768867:ℝ):ℂ) + ((0.966668206773:ℝ):ℂ) * I)‖ ≤ 0.00000013919 := by
  have hl := lg_35
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.086342883649410778 74.086342925325473292 1.3118808 0.00000003918 0.2560323768867 0.966668206773 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_36 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7485949057091:ℝ):ℂ) + ((0.6630276518716:ℝ):ℂ) * I)‖ ≤ 0.00000016829 := by
  have hl := lg_36
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.673367617881442864 74.67336765955748454 0.724856 0.00000006828 0.7485949057091 0.6630276518716 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_37 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9881782676229:ℝ):ℂ) + ((0.1533092019346:ℝ):ℂ) * I)‖ ≤ 0.00000014416 := by
  have hl := lg_37
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.244307442013362396 75.24430748368942491 0.1539162 0.00000004415 0.9881782676229 0.1533092019346 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_38 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9203598397914:ℝ):ℂ) + (((-0.3910725831597):ℝ):ℂ) * I)‖ ≤ 0.00000013025 := by
  have hl := lg_38
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.800020374711433314 75.800020416387495828 (-0.4017967) 0.00000003024 0.9203598397914 (-0.3910725831597) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_39 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5873028896851:ℝ):ℂ) + (((-0.809367231711):ℝ):ℂ) * I)‖ ≤ 0.00000012579 := by
  have hl := lg_39
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.341297560382586032 76.341297602058648546 (-0.9430739) 0.00000002578 0.5873028896851 (-0.809367231711) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p838_40 : ‖exp (-((((((20838:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0999825933096:ℝ):ℂ) + (((-0.994989186391):ℝ):ℂ) * I)‖ ≤ 0.00000014843 := by
  have hl := lg_40
  refine (ecis_approx ((((20838:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.868870037742487142 76.86887008983750798 (-1.4706464) 0.00000004842 0.0999825933096 (-0.994989186391) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_2 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.328819292293):ℝ):ℂ) + (((-0.9443928594678):ℝ):ℂ) * I)‖ ≤ 0.00000013689 := by
  have hl := lg_2
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.4722199774837 14.4722199879232 (-1.9058494) 0.00000003688 (-0.328819292293) (-0.9443928594678) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_3 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5843014149647):ℝ):ℂ) + ((0.8115367252684:ℝ):ℂ) * I)‖ ≤ 0.00000015141 := by
  have hl := lg_3
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.937925969674056156 22.937925980113577035 2.1948153 0.0000000514 (-0.5843014149647) 0.8115367252684 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_4 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7837558036715):ℝ):ℂ) + ((0.6210691106212:ℝ):ℂ) * I)‖ ≤ 0.00000013996 := by
  have hl := lg_4
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.9444399549674 28.9444399758464 2.4714866 0.00000003995 (-0.7837558036715) 0.6210691106212 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_5 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5783717149009):ℝ):ℂ) + (((-0.8157733505037):ℝ):ℂ) * I)‖ ≤ 0.00000014785 := by
  have hl := lg_5
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.603454162856769711 33.60345418373579059 (-2.1875276) 0.00000004784 (-0.5783717149009) (-0.8157733505037) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_6 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9585390663008:ℝ):ℂ) + ((0.2849611523965:ℝ):ℂ) * I)‖ ≤ 0.00000012497 := by
  have hl := lg_6
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.410145947157756156 37.410145968036777035 0.2889659 0.00000002496 0.9585390663008 0.2849611523965 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_7 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9776022634038):ℝ):ℂ) + (((-0.2104609566593):ℝ):ℂ) * I)‖ ≤ 0.00000015182 := by
  have hl := lg_7
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.628657991271075938 40.628658012150117696 (-2.9295462) 0.00000005181 (-0.9776022634038) (-0.2104609566593) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_8 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8442472620269:ℝ):ℂ) + ((0.5359538791352:ℝ):ℂ) * I)‖ ≤ 0.00000011782 := by
  have hl := lg_8
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.4166599324511 43.4166599637696 0.5656372 0.00000001781 0.8442472620269 0.5359538791352 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_9 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3171838009665):ℝ):ℂ) + (((-0.9483640843065):ℝ):ℂ) * I)‖ ≤ 0.00000011092 := by
  have hl := lg_9
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.875851939348112312 45.87585196022715407 (-1.8935548) 0.00000001091 (-0.3171838009665) (-0.9483640843065) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_10 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5802307433421):ℝ):ℂ) + ((0.8144521376177:ℝ):ℂ) * I)‖ ≤ 0.00000011711 := by
  have hl := lg_10
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.075674140340469711 48.07567417165899059 2.1898083 0.0000000171 (-0.5802307433421) 0.8144521376177 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_11 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9801009131191:ℝ):ℂ) + ((0.198499874315:ℝ):ℂ) * I)‖ ≤ 0.00000015837 := by
  have hl := lg_11
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.065655384474950507 50.065655415793492265 0.1998271 0.00000005836 0.9801009131191 0.198499874315 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_12 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0460708598669):ℝ):ℂ) + (((-0.9989381741984):ℝ):ℂ) * I)‖ ≤ 0.00000013281 := by
  have hl := lg_12
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.882365924641456156 51.882365955959977035 (-1.6168835) 0.0000000328 (-0.0460708598669) (-0.9989381741984) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_13 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9892876811745):ℝ):ℂ) + ((0.1459790515017:ℝ):ℂ) * I)‖ ≤ 0.00000014647 := by
  have hl := lg_13
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.5535776181572143 53.553577649475756058 2.9950901 0.00000004646 (-0.9892876811745) 0.1459790515017 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_14 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1226965675069:ℝ):ℂ) + ((0.992444231341:ℝ):ℂ) * I)‖ ≤ 0.00000013547 := by
  have hl := lg_14
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.100877968754775938 55.100878000073317696 1.4477898 0.00000003546 0.1226965675069 0.992444231341 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_15 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999734455606:ℝ):ℂ) + ((0.0072875354938:ℝ):ℂ) * I)‖ ≤ 0.0000001321 := by
  have hl := lg_15
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.541380132530825867 56.541380163849367625 0.0072876 0.00000003209 0.9999734455606 0.0072875354938 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_16 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.22854622924:ℝ):ℂ) + (((-0.9735330611233):ℝ):ℂ) * I)‖ ≤ 0.0000001547 := by
  have hl := lg_16
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.8888799099348 57.8888799516928 (-1.3402122) 0.00000005469 0.22854622924 (-0.9735330611233) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_17 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8599630528074):ℝ):ℂ) + (((-0.5103562948821):ℝ):ℂ) * I)‖ ≤ 0.000000166 := by
  have hl := lg_17
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.154661388840125486 59.154661430598146365 (-2.6059936) 0.00000006599 (-0.8599630528074) (-0.5103562948821) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_18 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7913321120377):ℝ):ℂ) + ((0.6113865294655:ℝ):ℂ) * I)‖ ≤ 0.00000015498 := by
  have hl := lg_18
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.348071916831812312 60.34807194815035407 2.4837811 0.00000005497 (-0.7913321120377) 0.6113865294655 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_19 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.214211701884:ℝ):ℂ) + ((0.9767872576851:ℝ):ℂ) * I)‖ ≤ 0.00000014208 := by
  have hl := lg_19
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.476941429733884037 61.476941461052446674 1.3549116 0.00000004207 0.214211701884 0.9767872576851 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_20 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9599538455437:ℝ):ℂ) + ((0.2801581953574:ℝ):ℂ) * I)‖ ≤ 0.00000015399 := by
  have hl := lg_20
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.547894117824169711 62.54789415958219059 0.2839589 0.00000005398 0.9599538455437 0.2801581953574 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_21 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.742011181544:ℝ):ℂ) + (((-0.6703875047044):ℝ):ℂ) * I)‖ ≤ 0.00000012048 := by
  have hl := lg_21
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.566583960945132094 63.566583992263694731 (-0.7347309) 0.00000002047 0.742011181544 (-0.6703875047044) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_22 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1348142247189):ℝ):ℂ) + (((-0.9908708921009):ℝ):ℂ) * I)‖ ≤ 0.00000013194 := by
  have hl := lg_22
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.537875361958650507 64.537875403716692265 (-1.7060223) 0.00000003193 (-0.1348142247189) (-0.9908708921009) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_23 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8739807118314):ℝ):ℂ) + (((-0.4859606108067):ℝ):ℂ) * I)‖ ≤ 0.00000015914 := by
  have hl := lg_23
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.465983712675072714 65.465983754433135351 (-2.6341307) 0.00000005913 (-0.8739807118314) (-0.4859606108067) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_24 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9282411257035):ℝ):ℂ) + ((0.3719790483297:ℝ):ℂ) * I)‖ ≤ 0.00000016492 := by
  have hl := lg_24
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.354585902125156156 66.354585943883177035 2.7604525 0.00000006491 (-0.9282411257035) 0.3719790483297 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_25 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3309722176647):ℝ):ℂ) + ((0.9436404988829:ℝ):ℂ) * I)‖ ≤ 0.00000015328 := by
  have hl := lg_25
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.206908325713539422 67.20690836747158118 1.90813 0.00000005327 (-0.3309722176647) 0.9436404988829 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_26 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4631583606794:ℝ):ℂ) + ((0.8862755400736:ℝ):ℂ) * I)‖ ≤ 0.00000015844 := by
  have hl := lg_26
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.0257975956409143 68.025797637398956058 1.0892408 0.00000005843 0.4631583606794 0.8862755400736 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_27 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9549632270558:ℝ):ℂ) + ((0.2967241732169:ℝ):ℂ) * I)‖ ≤ 0.00000016138 := by
  have hl := lg_27
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.813777909022168468 68.813777940340731105 0.3012605 0.00000006137 0.9549632270558 0.2967241732169 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_28 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8969122470052:ℝ):ℂ) + (((-0.4422085720246):ℝ):ℂ) * I)‖ ≤ 0.00000013275 := by
  have hl := lg_28
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.573097946238475938 69.573097987996517696 (-0.4580596) 0.00000003274 0.8969122470052 (-0.4422085720246) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_29 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3709808567135:ℝ):ℂ) + (((-0.9286405138438):ℝ):ℂ) * I)‖ ≤ 0.00000016641 := by
  have hl := lg_29
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.305769612577982268 70.305769654336044905 (-1.1907313) 0.0000000664 0.3709808567135 (-0.9286405138438) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_30 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3219282641976):ℝ):ℂ) + (((-0.9467640639086):ℝ):ℂ) * I)‖ ≤ 0.00000016898 := by
  have hl := lg_30
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.013600110014525867 71.013600151772567625 (-1.8985618) 0.00000006897 (-0.3219282641976) (-0.9467640639086) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_31 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8480974846654):ℝ):ℂ) + (((-0.5298402178314):ℝ):ℂ) * I)‖ ≤ 0.00000015825 := by
  have hl := lg_31
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.698218820735734077 71.698218862493796714 (-2.5831805) 0.00000005824 (-0.8480974846654) (-0.5298402178314) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_32 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9945480902039):ℝ):ℂ) + ((0.1042789326944:ℝ):ℂ) * I)‖ ≤ 0.00000015348 := by
  have hl := lg_32
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.3610998874185 72.361099939616 3.0371238 0.00000005347 (-0.9945480902039) 0.1042789326944 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_33 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7337642203683):ℝ):ℂ) + ((0.679404201398:ℝ):ℂ) * I)‖ ≤ 0.00000013202 := by
  have hl := lg_33
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.003581354149006663 73.0035813959070693 2.3946423 0.00000003201 (-0.7337642203683) 0.679404201398 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_34 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1992043912489):ℝ):ℂ) + ((0.9799579636425:ℝ):ℂ) * I)‖ ≤ 0.00000013238 := by
  have hl := lg_34
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.626881366323825486 73.626881418521346365 1.7713423 0.00000003237 (-0.1992043912489) 0.9799579636425 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_35 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3937290643575:ℝ):ℂ) + ((0.9192265356702:ℝ):ℂ) * I)‖ ≤ 0.00000013204 := by
  have hl := lg_35
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.232112154127845649 74.232112195885908286 1.1661115 0.00000003203 0.3937290643575 0.9192265356702 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_36 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8375942832498:ℝ):ℂ) + ((0.5462927939002:ℝ):ℂ) * I)‖ ≤ 0.00000014993 := by
  have hl := lg_36
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.820291894315512312 74.82029193607355407 0.5779318 0.00000004992 0.8375942832498 0.5462927939002 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_37 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999827798164:ℝ):ℂ) + ((0.0058685663138:ℝ):ℂ) * I)‖ ≤ 0.00000013201 := by
  have hl := lg_37
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.392355076389144518 75.392355118147207155 0.0058686 0.000000032 0.9999827798164 0.0058685663138 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_38 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8520340235124:ℝ):ℂ) + (((-0.5234864112633):ℝ):ℂ) * I)‖ ≤ 0.00000016284 := by
  have hl := lg_38
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.949161407217584037 75.949161448975646674 (-0.5509377) 0.00000006283 0.8520340235124 (-0.5234864112633) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_39 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4595748368252:ℝ):ℂ) + (((-0.8881390484361):ℝ):ℂ) * I)‖ ≤ 0.00000014345 := by
  have hl := lg_39
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.491503587831270456 76.491503629589333093 (-1.0932799) 0.00000004344 0.4595748368252 (-0.8881390484361) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_40 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0510718450388):ℝ):ℂ) + (((-0.9986949817857):ℝ):ℂ) * I)‖ ≤ 0.00000016137 := by
  have hl := lg_40
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.020114095307869711 77.02011414750539059 (-1.6218904) 0.00000006136 (-0.0510718450388) (-0.9986949817857) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_41 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5368096475721):ℝ):ℂ) + (((-0.8437033852401):ℝ):ℂ) * I)‖ ≤ 0.00000013259 := by
  have hl := lg_41
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.53567115358222582 77.535671205779767578 (-2.1374475) 0.00000003258 (-0.5368096475721) (-0.8437033852401) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_42 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8770967640833):ℝ):ℂ) + (((-0.4803137165862):ℝ):ℂ) * I)‖ ≤ 0.00000014774 := by
  have hl := lg_42
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.038803938428832094 78.038803980186894731 (-2.6405803) 0.00000004773 (-0.8770967640833) (-0.4803137165862) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_43 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999527690695):ℝ):ℂ) + (((-0.0097190002795):ℝ):ℂ) * I)‖ ≤ 0.00000014947 := by
  have hl := lg_43
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.53009719385627262 78.530097235614356136 (-3.1318735) 0.00000004946 (-0.9999527690695) (-0.0097190002795) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_44 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8914418739091):ℝ):ℂ) + ((0.4531350630158:ℝ):ℂ) * I)‖ ≤ 0.00000015391 := by
  have hl := lg_44
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.010095339442350507 79.010095391639892265 2.6713136 0.0000000539 (-0.8914418739091) 0.4531350630158 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_45 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5902000018581):ℝ):ℂ) + ((0.8072570580648:ℝ):ℂ) * I)‖ ≤ 0.00000015064 := by
  have hl := lg_45
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.479306102204882023 79.47930614396294466 2.2021029 0.00000005063 (-0.5902000018581) 0.8072570580648 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_46 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1715561031704):ℝ):ℂ) + ((0.98517435181:ℝ):ℂ) * I)‖ ≤ 0.00000014904 := by
  have hl := lg_46
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.938203690158772714 79.938203742356335351 1.7432053 0.00000004903 (-0.1715561031704) 0.98517435181 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_47 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.273104868761:ℝ):ℂ) + ((0.9619842673656:ℝ):ℂ) * I)‖ ≤ 0.00000014438 := by
  have hl := lg_47
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.387231748967259191 80.387231801164842707 1.2941772 0.00000004437 0.273104868761 0.9619842673656 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_48 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6565179472406:ℝ):ℂ) + ((0.7543104035813:ℝ):ℂ) * I)‖ ≤ 0.00000013849 := by
  have hl := lg_48
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.826805879608856156 80.826805931806377035 0.8546031 0.00000003848 0.6565179472406 0.7543104035813 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_49 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9114123331193:ℝ):ℂ) + ((0.4114943001283:ℝ):ℂ) * I)‖ ≤ 0.00000013098 := by
  have hl := lg_49
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.257315982542151876 81.257316024300235392 0.424093 0.00000003097 0.9114123331193 0.4114943001283 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p879_50 : ‖exp (-((((((20879:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999973992049:ℝ):ℂ) + ((0.0022806980228:ℝ):ℂ) * I)‖ ≤ 0.00000016208 := by
  have hl := lg_50
  refine (ecis_approx ((((20879:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.679128303197239422 81.67912835539478118 0.0022807 0.00000006207 0.9999973992049 0.0022806980228 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_2 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3555216056482):ℝ):ℂ) + (((-0.9346680629586):ℝ):ℂ) * I)‖ ≤ 0.00000010799 := by
  have hl := lg_2
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.500639011876 14.500639022336 (-1.9342684) 0.00000000798 (-0.3555216056482) (-0.9346680629586) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_3 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5471669220327):ℝ):ℂ) + ((0.837023511871:ℝ):ℂ) * I)‖ ≤ 0.00000015523 := by
  have hl := lg_3
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.98296907349879088 22.9829690839588118 2.1497721 0.00000005522 (-0.5471669220327) 0.837023511871 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_4 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7472087710578):ℝ):ℂ) + ((0.664589386329:ℝ):ℂ) * I)‖ ≤ 0.00000011216 := by
  have hl := lg_4
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.001278023752 29.001278044672 2.4146485 0.00000001215 (-0.7472087710578) 0.664589386329 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_5 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6309043534232):ℝ):ℂ) + (((-0.7758606168745):ℝ):ℂ) * I)‖ ≤ 0.00000011867 := by
  have hl := lg_5
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.66944111724525228 33.6694411381652732 (-2.2535146) 0.00000001866 (-0.6309043534232) (-0.7758606168745) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_6 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9768688071756:ℝ):ℂ) + ((0.2138395042252:ℝ):ℂ) * I)‖ ≤ 0.00000015772 := by
  have hl := lg_6
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.48360808537479088 37.4836081062948118 0.2155037 0.00000005771 0.9768688071756 0.2138395042252 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_7 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9912658406044):ℝ):ℂ) + (((-0.1318788566434):ℝ):ℂ) * I)‖ ≤ 0.00000013573 := by
  have hl := lg_7
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.70844030736102824 40.70844032828107008 (-3.0093285) 0.00000003572 (-0.9912658406044) (-0.1318788566434) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_8 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8868193364441:ℝ):ℂ) + ((0.4621162889455:ℝ):ℂ) * I)‖ ≤ 0.00000011677 := by
  have hl := lg_8
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.501917035628 43.501917067008 0.4803801 0.00000001676 0.8868193364441 0.4621162889455 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_9 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4012166206911):ℝ):ℂ) + (((-0.9159832003251):ℝ):ℂ) * I)‖ ≤ 0.00000011768 := by
  have hl := lg_9
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.96593814699758176 45.9659381679176236 (-1.983641) 0.00000001767 (-0.4012166206911) (-0.9159832003251) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_10 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5008720049548):ℝ):ℂ) + ((0.8655213657942:ℝ):ℂ) * I)‖ ≤ 0.00000012833 := by
  have hl := lg_10
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.17008012912125228 48.1700801605012732 2.0954023 0.00000002832 (-0.5008720049548) 0.8655213657942 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_11 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9948519379746:ℝ):ℂ) + ((0.1013391410475:ℝ):ℂ) * I)‖ ≤ 0.00000016459 := by
  have hl := lg_11
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.16396909062771036 50.1639691220077522 0.1015134 0.00000006458 0.9948519379746 0.1013391410475 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_12 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1474290116362):ℝ):ℂ) + (((-0.9890726396617):ℝ):ℂ) * I)‖ ≤ 0.0000001602 := by
  have hl := lg_12
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.98424709725079088 51.9842471286308118 (-1.7187647) 0.00000006019 (-0.1474290116362) (-0.9890726396617) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_13 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9684990382335):ℝ):ℂ) + ((0.2490172939289:ℝ):ℂ) * I)‖ ≤ 0.00000012285 := by
  have hl := lg_13
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.658740541781164 53.65874057316120584 2.8899272 0.00000002284 (-0.9684990382335) 0.2490172939289 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_14 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2291534746575:ℝ):ℂ) + ((0.973390304581:ℝ):ℂ) * I)‖ ≤ 0.00000014539 := by
  have hl := lg_14
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.20907931923702824 55.20907935061707008 1.3395884 0.00000004538 0.2291534746575 0.973390304581 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_15 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9946235817857:ℝ):ℂ) + (((-0.1035564124324):ℝ):ℂ) * I)‖ ≤ 0.00000015752 := by
  have hl := lg_15
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.65241019074404316 56.652410222124085 (-0.1037424) 0.00000005751 0.9946235817857 (-0.1035564124324) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_16 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1166419022386:ℝ):ℂ) + (((-0.9931740364317):ℝ):ℂ) * I)‖ ≤ 0.00000012474 := by
  have hl := lg_16
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.002556047504 58.002556089344 (-1.4538883) 0.00000002473 0.1166419022386 (-0.9931740364317) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_17 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9133182614102):ℝ):ℂ) + (((-0.4072465509265):ℝ):ℂ) * I)‖ ≤ 0.00000012873 := by
  have hl := lg_17
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.27082313590379928 59.2708231777438202 (-2.7221554) 0.00000002872 (-0.9133182614102) (-0.4072465509265) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_18 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7134990613186):ℝ):ℂ) + ((0.7006561849234:ℝ):ℂ) * I)‖ ≤ 0.00000011847 := by
  have hl := lg_18
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.46657715887358176 60.4665771902536236 2.3652759 0.00000001846 (-0.7134990613186) 0.7006561849234 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_19 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3302861542005:ℝ):ℂ) + ((0.9438808485945:ℝ):ℂ) * I)‖ ≤ 0.00000014396 := by
  have hl := lg_19
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.59766342784773476 61.59766345922779752 1.2341896 0.00000004395 0.3302861542005 0.9438808485945 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_20 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9870459978464:ℝ):ℂ) + ((0.160437520971:ℝ):ℂ) * I)‖ ≤ 0.00000013081 := by
  have hl := lg_20
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.67071914099725228 62.6707191828372732 0.1611339 0.0000000308 0.9870459978464 0.160437520971 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_21 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6527736586756:ℝ):ℂ) + (((-0.757553001802):ℝ):ℂ) * I)‖ ≤ 0.00000014046 := by
  have hl := lg_21
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.69140938085981912 63.69140941223988188 (-0.8595563) 0.00000004045 0.6527736586756 (-0.757553001802) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_22 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2589729962944):ℝ):ℂ) + (((-0.9658845620409):ℝ):ℂ) * I)‖ ≤ 0.00000016931 := by
  have hl := lg_22
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.66460810250371036 64.6646081443437522 (-1.8327551) 0.0000000693 (-0.2589729962944) (-0.9658845620409) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_23 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9290695879514):ℝ):ℂ) + (((-0.3699049885928):ℝ):ℂ) * I)‖ ≤ 0.00000014554 := by
  have hl := lg_23
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.59453897548553672 65.59453901732559948 (-2.7626859) 0.00000004553 (-0.9290695879514) (-0.3699049885928) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_24 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8720404057659):ℝ):ℂ) + ((0.4894338878972:ℝ):ℂ) * I)‖ ≤ 0.00000016986 := by
  have hl := lg_24
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.48488610912679088 66.4848861509668118 2.6301522 0.00000006985 (-0.8720404057659) 0.4894338878972 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_25 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2039193866311):ℝ):ℂ) + ((0.9789876831478:ℝ):ℂ) * I)‖ ≤ 0.0000001445 := by
  have hl := lg_25
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.33888223449050456 67.3388822763305464 1.7761561 0.00000004449 (-0.2039193866311) 0.9789876831478 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_26 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5770708450632:ℝ):ℂ) + ((0.8166940919206:ℝ):ℂ) * I)‖ ≤ 0.00000012533 := by
  have hl := lg_26
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.159379553657164 68.15937959549720584 0.9556588 0.00000002532 0.5770708450632 0.8166940919206 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_27 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9862319385689:ℝ):ℂ) + ((0.1653679634831:ℝ):ℂ) * I)‖ ≤ 0.00000015849 := by
  have hl := lg_27
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.94890722049637264 68.9489072518764354 0.1661311 0.00000005848 0.9862319385689 0.1653679634831 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_28 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8283278192368:ℝ):ℂ) + (((-0.5602437182856):ℝ):ℂ) * I)‖ ≤ 0.00000014788 := by
  have hl := lg_28
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.70971833111302824 69.70971837295307008 (-0.59468) 0.00000004787 0.8283278192368 (-0.5602437182856) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_29 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2396505797642:ℝ):ℂ) + (((-0.970859206898):ℝ):ℂ) * I)‖ ≤ 0.00000013743 := by
  have hl := lg_29
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.44382874156479664 70.4438287834048594 (-1.3287904) 0.00000003742 0.2396505797642 (-0.970859206898) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_30 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4504010442271):ℝ):ℂ) + (((-0.8928263545363):ℝ):ℂ) * I)‖ ≤ 0.0000001655 := by
  have hl := lg_30
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.15304920262004316 71.153049244460085 (-2.0380108) 0.00000006549 (-0.4504010442271) (-0.8928263545363) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_31 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9140573287096):ℝ):ℂ) + (((-0.4055850092127):ℝ):ℂ) * I)‖ ≤ 0.00000015896 := by
  have hl := lg_31
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.83901229607699396 71.83901233791705672 (-2.7239739) 0.00000005895 (-0.9140573287096) (-0.4055850092127) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_32 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9697567673261):ℝ):ℂ) + ((0.2440733741208:ℝ):ℂ) * I)‖ ≤ 0.00000012679 := by
  have hl := lg_32
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.50319505938 72.50319511168 2.8950286 0.00000002678 (-0.9697567673261) 0.2440733741208 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_33 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6291733165089):ℝ):ℂ) + ((0.7772650370231:ℝ):ℂ) * I)‖ ≤ 0.00000012204 := by
  have hl := lg_33
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.14693816412650124 73.146938205966564 2.2512855 0.00000002203 (-0.6291733165089) 0.7772650370231 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_34 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0559359630211):ℝ):ℂ) + ((0.9984343584035:ℝ):ℂ) * I)‖ ≤ 0.00000013839 := by
  have hl := lg_34
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.77146214777979928 73.7714622000798202 1.6267615 0.00000003838 (-0.0559359630211) 0.9984343584035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_35 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5230743292489:ℝ):ℂ) + ((0.8522870678831:ℝ):ℂ) * I)‖ ≤ 0.00000016156 := by
  have hl := lg_35
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.37788142460628052 74.37788146644634328 1.0203422 0.00000006155 0.5230743292489 0.8522870678831 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_36 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9085452910868:ℝ):ℂ) + ((0.4177863736934:ℝ):ℂ) * I)‖ ≤ 0.00000012645 := by
  have hl := lg_36
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.96721617074958176 74.9672162125896236 0.4310075 0.00000002644 0.9085452910868 0.4177863736934 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_37 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9899095812143:ℝ):ℂ) + (((-0.1417004623144):ℝ):ℂ) * I)‖ ≤ 0.00000016646 := by
  have hl := lg_37
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.54040271076492664 75.5404027526049894 (-0.142179) 0.00000006645 0.9899095812143 (-0.1417004623144) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_38 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7647914205562:ℝ):ℂ) + (((-0.6442779548019):ℝ):ℂ) * I)‖ ≤ 0.00000014645 := by
  have hl := lg_38
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.09830243972373476 76.09830248156379752 (-0.7000788) 0.00000004644 0.7647914205562 (-0.6442779548019) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_39 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3214973146023:ℝ):ℂ) + (((-0.9469104903334):ℝ):ℂ) * I)‖ ≤ 0.00000017089 := by
  have hl := lg_39
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.64170961527995488 76.64170965712001764 (-1.243486) 0.00000007088 0.3214973146023 (-0.9469104903334) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_40 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2009603510509):ℝ):ℂ) + (((-0.9795993759209):ℝ):ℂ) * I)‖ ≤ 0.0000001333 := by
  have hl := lg_40
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.17135815287325228 77.1713582051732732 (-1.7731345) 0.00000003329 (-0.2009603510509) (-0.9795993759209) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_41 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6585629859562):ℝ):ℂ) + (((-0.7525256098702):ℝ):ℂ) * I)‖ ≤ 0.00000017442 := by
  have hl := lg_41
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.6879276082638136 77.68792766056385544 (-2.2897039) 0.00000007441 (-0.6585629859562) (-0.7525256098702) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_42 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9401357359795):ℝ):ℂ) + (((-0.3408002314473):ℝ):ℂ) * I)‖ ≤ 0.00000014844 := by
  have hl := lg_42
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.19204839273581912 78.19204843457588188 (-2.7938247) 0.00000004843 (-0.9401357359795) (-0.3408002314473) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_43 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9895794604318):ℝ):ℂ) + ((0.1439878157668:ℝ):ℂ) * I)‖ ≤ 0.00000014708 := by
  have hl := lg_43
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.6843063985570776 78.68430644039716128 2.9971026 0.00000004707 (-0.9895794604318) 0.1439878157668 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_44 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8107110115143):ℝ):ℂ) + ((0.5854465438927:ℝ):ℂ) * I)‖ ≤ 0.00000017336 := by
  have hl := lg_44
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.16524711437971036 79.1652471666797522 2.5161619 0.00000007335 (-0.8107110115143) 0.5854465438927 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_45 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4575459718158):ℝ):ℂ) + ((0.8891859668654:ℝ):ℂ) * I)‖ ≤ 0.00000012911 := by
  have hl := lg_45
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.63537926424283404 79.6353793060828968 2.0460297 0.0000000291 (-0.4575459718158) 0.8891859668654 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_46 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.015434060381):ℝ):ℂ) + ((0.9998808877961:ℝ):ℂ) * I)‖ ≤ 0.00000014634 := by
  have hl := lg_46
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.09517798736153672 80.09517803966159948 1.586231 0.00000004633 (-0.015434060381) 0.9998808877961 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_47 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4209343515552:ℝ):ℂ) + ((0.9070911043995:ℝ):ℂ) * I)‖ ≤ 0.00000015956 := by
  have hl := lg_47
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.54508780058408268 80.54508785288416636 1.1363212 0.00000005955 0.4209343515552 0.9070911043995 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_48 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.76748742925:ℝ):ℂ) + ((0.6410639952011:ℝ):ℂ) * I)‖ ≤ 0.00000017235 := by
  have hl := lg_48
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.98552512100279088 80.9855251733028118 0.6958838 0.00000007234 0.76748742925 0.6410639952011 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_49 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9652159099662:ℝ):ℂ) + ((0.2614541014178:ℝ):ℂ) * I)‖ ≤ 0.00000016324 := by
  have hl := lg_49
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.41688061472205648 81.41688065656214016 0.2645284 0.00000006323 0.9652159099662 0.2614541014178 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p92_50 : ‖exp (-((((((20920:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9875262692277:ℝ):ℂ) + (((-0.1574543349201):ℝ):ℂ) * I)‖ ≤ 0.00000014698 := by
  have hl := lg_50
  refine (ecis_approx ((((20920:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.83952124636650456 81.8395212986665464 (-0.1581123) 0.00000004697 0.9875262692277 (-0.1574543349201) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_2 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3819368050143):ℝ):ℂ) + (((-0.9241884423496):ℝ):ℂ) * I)‖ ≤ 0.0000001424 := by
  have hl := lg_2
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.5290580462683 14.5290580567488 (-1.9626874) 0.00000004239 (-0.3819368050143) (-0.9241884423496) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_3 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.508922561442):ℝ):ℂ) + ((0.8608123061671:ℝ):ℂ) * I)‖ ≤ 0.00000015141 := by
  have hl := lg_3
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.028012177323525604 23.028012187804046565 2.104729 0.0000000514 (-0.508922561442) 0.8608123061671 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_4 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7082484782827):ℝ):ℂ) + ((0.7059632377009:ℝ):ℂ) * I)‖ ≤ 0.00000014338 := by
  have hl := lg_4
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.0581160925366 29.0581161134976 2.3578104 0.00000004337 (-0.7082484782827) 0.7059632377009 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_5 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6806907785229):ℝ):ℂ) + (((-0.7325708593803):ℝ):ℂ) * I)‖ ≤ 0.00000015671 := by
  have hl := lg_5
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.735428071633734849 33.73542809259475581 (-2.3195015) 0.0000000567 (-0.6806907785229) (-0.7325708593803) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_6 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9899290415136:ℝ):ℂ) + ((0.1415644474008:ℝ):ℂ) * I)‖ ≤ 0.0000001195 := by
  have hl := lg_6
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.557070223591825604 37.557070244552846565 0.1420416 0.00000001949 0.9899290415136 0.1415644474008 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_7 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9986231433229):ℝ):ℂ) + (((-0.0524577644594):ℝ):ℂ) * I)‖ ≤ 0.00000011964 := by
  have hl := lg_7
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.788222623450980542 40.788222644412022464 (-3.0891108) 0.00000001963 (-0.9986231433229) (-0.0524577644594) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_8 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.922949225974:ℝ):ℂ) + ((0.3849217144745:ℝ):ℂ) * I)‖ ≤ 0.00000012 := by
  have hl := lg_8
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.5871741388049 43.5871741702464 0.395123 0.00000001999 0.922949225974 0.3849217144745 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_9 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4819955590022):ℝ):ℂ) + (((-0.8761736592118):ℝ):ℂ) * I)‖ ≤ 0.00000012537 := by
  have hl := lg_9
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.056024354647051208 46.05602437560809313 (-2.0737272) 0.00000002536 (-0.4819955590022) (-0.8761736592118) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_10 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4170525628872):ℝ):ℂ) + ((0.9088823685085:ℝ):ℂ) * I)‖ ≤ 0.00000013955 := by
  have hl := lg_10
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.264486117902034849 48.26448614934355581 2.0009963 0.00000003954 (-0.4170525628872) 0.9088823685085 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_11 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999948812843:ℝ):ℂ) + ((0.0031995945407:ℝ):ℂ) * I)‖ ≤ 0.00000016067 := by
  have hl := lg_11
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.262282796780470213 50.262282828222012135 0.0031996 0.00000006066 0.9999948812843 0.0031995945407 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_12 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2472581091709):ℝ):ℂ) + (((-0.9689496516579):ℝ):ℂ) * I)‖ ≤ 0.00000014388 := by
  have hl := lg_12
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.086128269860125604 52.086128301301646565 (-1.8206458) 0.00000004387 (-0.2472581091709) (-0.9689496516579) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_13 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.937009403805):ℝ):ℂ) + ((0.3493041325377:ℝ):ℂ) * I)‖ ≤ 0.00000013225 := by
  have hl := lg_13
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.7639034654051137 53.763903496846655622 2.7847643 0.00000003224 (-0.937009403805) 0.3493041325377 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_14 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3329300797822:ℝ):ℂ) + ((0.9429515162384:ℝ):ℂ) * I)‖ ≤ 0.00000013656 := by
  have hl := lg_14
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.317280669719280542 55.317280701160822464 1.2313871 0.00000003655 0.3329300797822 0.9429515162384 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_15 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9770249054641:ℝ):ℂ) + (((-0.213125160652):ℝ):ℂ) * I)‖ ≤ 0.0000001158 := by
  have hl := lg_15
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.763440248957260453 56.763440280398802375 (-0.2147725) 0.00000001579 0.9770249054641 (-0.213125160652) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_16 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0032319211684:ℝ):ℂ) + (((-0.999994777329):ℝ):ℂ) * I)‖ ≤ 0.00000016239 := by
  have hl := lg_16
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.1162321850732 58.1162322269952 (-1.5675644) 0.00000006238 0.0032319211684 (-0.999994777329) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_17 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9543633734866):ℝ):ℂ) + (((-0.2986478714669):ℝ):ℂ) * I)‖ ≤ 0.00000016029 := by
  have hl := lg_17
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.386984882967473074 59.386984924889494035 (-2.8383171) 0.00000006028 (-0.9543633734866) (-0.2986478714669) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_18 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6256577199005):ℝ):ℂ) + ((0.7800976974165:ℝ):ℂ) * I)‖ ≤ 0.00000016058 := by
  have hl := lg_18
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.585082400915351208 60.58508243235689313 2.2467707 0.00000006057 (-0.6256577199005) 0.7800976974165 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_19 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4415529248458:ℝ):ℂ) + ((0.8972352058185:ℝ):ℂ) * I)‖ ≤ 0.00000014585 := by
  have hl := lg_19
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.718385425961585483 61.718385457403148366 1.1134676 0.00000004584 0.4415529248458 0.8972352058185 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_20 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9992663038263:ℝ):ℂ) + ((0.0382995305105:ℝ):ℂ) * I)‖ ≤ 0.00000013431 := by
  have hl := lg_20
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.793544164170334849 62.79354420609235581 0.0383089 0.0000000343 0.9992663038263 0.0382995305105 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_21 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5533782208707:ℝ):ℂ) + (((-0.832930095906):ℝ):ℂ) * I)‖ ≤ 0.00000016044 := by
  have hl := lg_21
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.816234800774506146 63.816234832216069029 (-0.9843817) 0.00000006043 0.5533782208707 (-0.832930095906) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_22 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3789778216937):ℝ):ℂ) + (((-0.9254057546079):ℝ):ℂ) * I)‖ ≤ 0.00000012876 := by
  have hl := lg_22
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.791340843048770213 64.791340884970812135 (-1.9594878) 0.00000002875 (-0.3789778216937) (-0.9254057546079) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_23 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9688254107599):ℝ):ℂ) + (((-0.247744471582):ℝ):ℂ) * I)‖ ≤ 0.00000013351 := by
  have hl := lg_23
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.723094238296000726 65.723094280218063609 (-2.8912412) 0.0000000335 (-0.9688254107599) (-0.247744471582) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_24 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8010550328856):ℝ):ℂ) + ((0.5985907067764:ℝ):ℂ) * I)‖ ≤ 0.00000016286 := by
  have hl := lg_24
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.615186316128425604 66.615186358050446565 2.499852 0.00000006285 (-0.8010550328856) 0.5985907067764 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_25 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0733200211697):ℝ):ℂ) + ((0.9973084650675:ℝ):ℂ) * I)‖ ≤ 0.00000013572 := by
  have hl := lg_25
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.470856143267469698 67.47085618518951162 1.6441822 0.00000003571 (-0.0733200211697) 0.9973084650675 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_26 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.680701293477:ℝ):ℂ) + ((0.7325610889604:ℝ):ℂ) * I)‖ ≤ 0.00000016732 := by
  have hl := lg_26
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.2929615116734137 68.292961553595455622 0.8220768 0.00000006731 0.680701293477 0.7325610889604 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_27 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9995194826861:ℝ):ℂ) + ((0.030996834207:ℝ):ℂ) * I)‖ ≤ 0.00000014702 := by
  have hl := lg_27
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.084036531970576812 69.084036563412139695 0.0310018 0.00000004701 0.9995194826861 0.030996834207 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_28 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7443065752561:ℝ):ℂ) + (((-0.6678380956718):ℝ):ℂ) * I)‖ ≤ 0.000000163 := by
  have hl := lg_28
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.846338715987580542 69.846338757909622464 (-0.7313004) 0.00000006299 0.7443065752561 (-0.6678380956718) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_29 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.103759737978:ℝ):ℂ) + (((-0.9946023912975):ℝ):ℂ) * I)‖ ≤ 0.00000013351 := by
  have hl := lg_29
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.581887870551611012 70.581887912473673895 (-1.4668495) 0.0000000335 0.103759737978 (-0.9946023912975) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_30 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5701295810605):ℝ):ℂ) + (((-0.821554782586):ℝ):ℂ) * I)‖ ≤ 0.00000015819 := by
  have hl := lg_30
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.292498295225560453 71.292498337147602375 (-2.1774599) 0.00000005818 (-0.5701295810605) (-0.821554782586) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_31 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9619279526084):ℝ):ℂ) + (((-0.273303153569):ℝ):ℂ) * I)‖ ≤ 0.00000013438 := by
  have hl := lg_31
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.979805771418253843 71.979805813340316726 (-2.8647674) 0.00000003437 (-0.9619279526084) (-0.273303153569) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_32 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9254179645998):ℝ):ℂ) + ((0.378948005199:ℝ):ℂ) * I)‖ ≤ 0.00000015483 := by
  have hl := lg_32
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.6452902313415 72.645290283744 2.7529334 0.00000005482 (-0.9254179645998) 0.378948005199 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_33 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5116742926855):ℝ):ℂ) + ((0.8591795028968:ℝ):ℂ) * I)‖ ≤ 0.00000012989 := by
  have hl := lg_33
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.290294974103995817 73.2902950160260587 2.1079287 0.00000002988 (-0.5116742926855) 0.8591795028968 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_34 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0884996932356:ℝ):ℂ) + ((0.9960762040613:ℝ):ℂ) * I)‖ ≤ 0.00000015693 := by
  have hl := lg_34
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.916042929235773074 73.916042981638294035 1.4821807 0.00000005692 0.0884996932356 0.9960762040613 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_35 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6413245407927:ℝ):ℂ) + ((0.7672697266132:ℝ):ℂ) * I)‖ ≤ 0.00000015087 := by
  have hl := lg_35
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.523650695084715391 74.523650737006778274 0.874573 0.00000005086 0.6413245407927 0.7672697266132 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_36 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9599190144642:ℝ):ℂ) + ((0.2802775154559:ℝ):ℂ) * I)‖ ≤ 0.00000013899 := by
  have hl := lg_36
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.114140447183651208 75.11414048910569313 0.2840832 0.00000003898 0.9599190144642 0.2802775154559 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_37 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9581790255204:ℝ):ℂ) + (((-0.2861694516416):ℝ):ℂ) * I)‖ ≤ 0.00000014103 := by
  have hl := lg_37
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.688450345140708762 75.688450387062771645 (-0.2902267) 0.00000004102 0.9581790255204 (-0.2861694516416) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_38 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6605690939278:ℝ):ℂ) + (((-0.7507652576854):ℝ):ℂ) * I)‖ ≤ 0.00000012801 := by
  have hl := lg_38
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.247443472229885483 76.247443514151948366 (-0.8492198) 0.000000028 0.6605690939278 (-0.7507652576854) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_39 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1761799370138:ℝ):ℂ) + (((-0.9843579784782):ℝ):ℂ) * I)‖ ≤ 0.00000014344 := by
  have hl := lg_39
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.791915642728639304 76.791915684650702187 (-1.393692) 0.00000004343 0.1761799370138 (-0.9843579784782) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_40 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3462606898104):ℝ):ℂ) + (((-0.9381383345167):ℝ):ℂ) * I)‖ ≤ 0.00000017573 := by
  have hl := lg_40
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.322602210438634849 77.32260226284115581 (-1.9243786) 0.00000007572 (-0.3462606898104) (-0.9381383345167) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_41 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7650790442966):ℝ):ℂ) + (((-0.6439363756928):ℝ):ℂ) * I)‖ ≤ 0.00000012921 := by
  have hl := lg_41
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.84018406294540138 77.840184115347943302 (-2.4419604) 0.0000000292 (-0.7650790442966) (-0.6439363756928) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_42 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9811398967597):ℝ):ℂ) + (((-0.1932989980694):ℝ):ℂ) * I)‖ ≤ 0.00000013913 := by
  have hl := lg_42
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.345292847042806146 78.345292888964869029 (-2.9470692) 0.00000003912 (-0.9811398967597) (-0.1932989980694) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_43 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9557200775986):ℝ):ℂ) + ((0.2942773063885:ℝ):ℂ) * I)‖ ≤ 0.00000015186 := by
  have hl := lg_43
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.83851560325788258 78.838515645179966424 2.8428934 0.00000005185 (-0.9557200775986) 0.2942773063885 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_44 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7105037194507):ℝ):ℂ) + ((0.7036934450606:ℝ):ℂ) * I)‖ ≤ 0.0000001484 := by
  have hl := lg_44
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.320398889317070213 79.320398941719612135 2.3610101 0.00000004839 (-0.7105037194507) 0.7036934450606 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_45 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3137692564379):ℝ):ℂ) + ((0.9494992647246:ℝ):ℂ) * I)‖ ≤ 0.00000016707 := by
  have hl := lg_45
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.791452426280786057 79.79145246820284894 1.8899565 0.00000006706 (-0.3137692564379) 0.9494992647246 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_46 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1410675117324:ℝ):ℂ) + ((0.9899999783503:ℝ):ℂ) * I)‖ ≤ 0.00000014365 := by
  have hl := lg_46
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.252152284564300726 80.252152336966863609 1.4292567 0.00000004364 0.1410675117324 0.9899999783503 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_47 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5582966205301:ℝ):ℂ) + ((0.829641418629:ℝ):ℂ) * I)‖ ≤ 0.00000014115 := by
  have hl := lg_47
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.702943852200906169 80.702943904603490013 0.9784651 0.00000004114 0.5582966205301 0.829641418629 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_48 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.859163012832:ℝ):ℂ) + ((0.5117019810216:ℝ):ℂ) * I)‖ ≤ 0.00000013095 := by
  have hl := lg_48
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.144244362396725604 81.144244414799246565 0.5371646 0.00000003094 0.859163012832 0.5117019810216 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_49 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9944963665935:ℝ):ℂ) + ((0.1047710686798:ℝ):ℂ) * I)‖ ≤ 0.00000014645 := by
  have hl := lg_49
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.576445246901961084 81.576445288824044928 0.1049637 0.00000004644 0.9944963665935 0.1047710686798 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p961_50 : ‖exp (-((((((20961:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9497045715037:ℝ):ℂ) + (((-0.3131472926036):ℝ):ℂ) * I)‖ ≤ 0.00000014862 := by
  have hl := lg_50
  refine (ecis_approx ((((20961:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.999914189535769698 81.99991424193831162 (-0.3185052) 0.00000004861 0.9497045715037 (-0.3131472926036) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_2 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4080436491635):ℝ):ℂ) + (((-0.9129624200228):ℝ):ℂ) * I)‖ ≤ 0.00000013371 := by
  have hl := lg_2
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.5574770806606 14.5574770911616 (-1.9911065) 0.0000000337 (-0.4080436491635) (-0.9129624200228) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_3 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4696458321722):ℝ):ℂ) + ((0.8828549101172:ℝ):ℂ) * I)‖ ≤ 0.00000014759 := by
  have hl := lg_3
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.073055281148260328 23.07305529164928133 2.0596859 0.00000004758 (-0.4696458321722) 0.8828549101172 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_4 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6670008299092):ℝ):ℂ) + ((0.7450569729099:ℝ):ℂ) * I)‖ ≤ 0.00000014644 := by
  have hl := lg_4
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.1149541613212 29.1149541823232 2.3009724 0.00000004643 (-0.6670008299092) 0.7450569729099 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_5 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7275144354505):ℝ):ℂ) + (((-0.6860923743799):ℝ):ℂ) * I)‖ ≤ 0.00000011114 := by
  have hl := lg_5
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.801415026022217418 33.80141504702423842 (-2.3854885) 0.00000001113 (-0.7275144354505) (-0.6860923743799) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_6 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9976493475954:ℝ):ℂ) + ((0.0685257560522:ℝ):ℂ) * I)‖ ≤ 0.00000013975 := by
  have hl := lg_6
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.630532361808860328 37.63053238281088133 0.0685795 0.00000003974 0.9976493475954 0.0685257560522 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_7 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996273654581):ℝ):ℂ) + ((0.0272970621969:ℝ):ℂ) * I)‖ ≤ 0.00000011073 := by
  have hl := lg_7
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.868004939540932844 40.868004960542974848 3.1142922 0.00000001072 (-0.9996273654581) 0.0272970621969 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_8 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9523744696859:ℝ):ℂ) + ((0.3049309257692:ℝ):ℂ) * I)‖ ≤ 0.00000012324 := by
  have hl := lg_8
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.6724312419818 43.6724312734848 0.3098659 0.00000002323 0.9523744696859 0.3049309257692 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_9 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5588654957664):ℝ):ℂ) + (((-0.8292583177952):ℝ):ℂ) * I)‖ ≤ 0.00000013306 := by
  have hl := lg_9
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.146110562296520656 46.14611058329856266 (-2.1638134) 0.00000003305 (-0.5588654957664) (-0.8292583177952) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_10 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3295189026488):ℝ):ℂ) + ((0.9441489780724:ℝ):ℂ) * I)‖ ≤ 0.00000015077 := by
  have hl := lg_10
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.358892106682817418 48.35889213818583842 1.9065903 0.00000005076 (-0.3295189026488) 0.9441489780724 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_11 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9954800630723:ℝ):ℂ) + (((-0.0949707535277):ℝ):ℂ) * I)‖ ≤ 0.00000015452 := by
  have hl := lg_11
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.360596502933230066 50.36059653443627207 (-0.0951141) 0.00000005451 0.9954800630723 (-0.0949707535277) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_12 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.344523040299):ℝ):ℂ) + (((-0.9387778622767):ℝ):ℂ) * I)‖ ≤ 0.00000011655 := by
  have hl := lg_12
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.188009442469460328 52.18800947397248133 (-1.922527) 0.00000001654 (-0.344523040299) (-0.9387778622767) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_13 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8951667083518):ℝ):ℂ) + ((0.4457314933316:ℝ):ℂ) * I)‖ ≤ 0.00000015593 := by
  have hl := lg_13
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.8690663890290634 53.869066420532105404 2.6796014 0.00000005592 (-0.8951667083518) 0.4457314933316 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_14 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4328127903482:ℝ):ℂ) + ((0.9014838259841:ℝ):ℂ) * I)‖ ≤ 0.00000014443 := by
  have hl := lg_14
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.425482020201532844 55.425482051704574848 1.1231857 0.00000004442 0.4328127903482 0.9014838259841 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_15 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9473941439883:ℝ):ℂ) + (((-0.3200692674043):ℝ):ℂ) * I)‖ ≤ 0.00000015746 := by
  have hl := lg_15
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.874470307170477746 56.87447033867351975 (-0.3258026) 0.00000005745 0.9473941439883 (-0.3200692674043) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_16 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1102198780501):ℝ):ℂ) + (((-0.9939072283076):ℝ):ℂ) * I)‖ ≤ 0.00000014199 := by
  have hl := lg_16
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.2299083226424 58.2299083646464 (-1.6812406) 0.00000004198 (-0.1102198780501) (-0.9939072283076) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_17 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.982545237276):ℝ):ℂ) + (((-0.1860238059091):ℝ):ℂ) * I)‖ ≤ 0.0000001346 := by
  have hl := lg_17
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.503146630031146868 59.50314667203516787 (-2.9544789) 0.00000003459 (-0.982545237276) (-0.1860238059091) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_18 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5290401582676):ℝ):ℂ) + ((0.8485967893721:ℝ):ℂ) * I)‖ ≤ 0.00000012885 := by
  have hl := lg_18
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.703587642957120656 60.70358767446016266 2.1282654 0.00000002884 (-0.5290401582676) 0.8485967893721 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_19 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5463924024402:ℝ):ℂ) + ((0.8375293084756:ℝ):ℂ) * I)‖ ≤ 0.00000014774 := by
  have hl := lg_19
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.839107424075436206 61.839107455578499212 0.9927456 0.00000004773 0.5463924024402 0.8375293084756 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_20 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9964306398325:ℝ):ℂ) + (((-0.084415519918):ℝ):ℂ) * I)‖ ≤ 0.00000015757 := by
  have hl := lg_20
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.916369187343417418 62.91636922934743842 (-0.0845161) 0.00000005756 0.9964306398325 (-0.084415519918) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_21 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4453714868434:ℝ):ℂ) + (((-0.8953458765789):ℝ):ℂ) * I)‖ ≤ 0.00000015112 := by
  have hl := lg_21
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.941060220689193172 63.941060252192256178 (-1.1092072) 0.00000005111 0.4453714868434 (-0.8953458765789) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_22 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4929039595692):ℝ):ℂ) + (((-0.8700837239226):ℝ):ℂ) * I)‖ ≤ 0.00000015382 := by
  have hl := lg_22
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.918073583593830066 64.91807362559787207 (-2.0862205) 0.00000005381 (-0.4929039595692) (-0.8700837239226) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_23 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9925920127802):ℝ):ℂ) + (((-0.1214952498108):ℝ):ℂ) * I)‖ ≤ 0.0000001707 := by
  have hl := lg_23
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.851649501106464732 65.851649543110527738 (-3.0197965) 0.00000007069 (-0.9925920127802) (-0.1214952498108) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_24 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7164884654142):ℝ):ℂ) + ((0.6975989384323:ℝ):ℂ) * I)‖ ≤ 0.00000015586 := by
  have hl := lg_24
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.745486523130060328 66.74548656513408133 2.3695518 0.00000005585 (-0.7164884654142) 0.6975989384323 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_25 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0585545147579:ℝ):ℂ) + ((0.9982842124372:ℝ):ℂ) * I)‖ ≤ 0.00000012695 := by
  have hl := lg_25
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.602830052044434836 67.60283009404847684 1.5122083 0.00000002694 0.0585545147579 0.9982842124372 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_26 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7722031931867:ℝ):ℂ) + ((0.6353756593011:ℝ):ℂ) * I)‖ ≤ 0.00000013273 := by
  have hl := lg_26
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.4265434696896634 68.426543511693705404 0.6884949 0.00000003272 0.7722031931867 0.6353756593011 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_27 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9945836284599:ℝ):ℂ) + (((-0.1039394342854):ℝ):ℂ) * I)‖ ≤ 0.00000013555 := by
  have hl := lg_27
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.219165843444780984 69.21916587494784399 (-0.1041275) 0.00000003554 0.9945836284599 (-0.1039394342854) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_28 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.646414421304:ℝ):ℂ) + (((-0.7629864978689):ℝ):ℂ) * I)‖ ≤ 0.00000016391 := by
  have hl := lg_28
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.982959100862132844 69.982959142866174848 (-0.8679207) 0.0000000639 0.646414421304 (-0.7629864978689) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_29 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.034105657815):ℝ):ℂ) + (((-0.9994182328258):ℝ):ℂ) * I)‖ ≤ 0.00000016258 := by
  have hl := lg_29
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.719946999538425384 70.71994704154248839 (-1.6049086) 0.00000006257 (-0.034105657815) (-0.9994182328258) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_30 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6787893032182):ℝ):ℂ) + (((-0.7343330864234):ℝ):ℂ) * I)‖ ≤ 0.00000015087 := by
  have hl := lg_30
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.431947387831077746 71.43194742983511975 (-2.316909) 0.00000005086 (-0.6787893032182) (-0.7343330864234) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_31 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9907619395955):ℝ):ℂ) + (((-0.1356126049956):ℝ):ℂ) * I)‖ ≤ 0.00000013223 := by
  have hl := lg_31
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.120599246759513726 72.120599288763576732 (-3.0055609) 0.00000003222 (-0.9907619395955) (-0.1356126049956) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_32 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8624254741492):ℝ):ℂ) + ((0.5061840588722:ℝ):ℂ) * I)‖ ≤ 0.00000016967 := by
  have hl := lg_32
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.787385403303 72.787385455808 2.6108383 0.00000006966 (-0.8624254741492) 0.5061840588722 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_33 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3836777589095):ℝ):ℂ) + ((0.9234670418132:ℝ):ℂ) * I)‖ ≤ 0.00000013995 := by
  have hl := lg_33
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.433651784081490394 73.4336518260855534 1.9645719 0.00000003994 (-0.3836777589095) 0.9234670418132 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_34 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2310886069511:ℝ):ℂ) + ((0.9729327087406:ℝ):ℂ) * I)‖ ≤ 0.00000017548 := by
  have hl := lg_34
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.060623710691746868 74.06062376319676787 1.3375999 0.00000007547 0.2310886069511 0.9729327087406 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_35 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7459716450769:ℝ):ℂ) + ((0.6659777058891:ℝ):ℂ) * I)‖ ≤ 0.00000012143 := by
  have hl := lg_35
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.669419965563150262 74.669420007567213268 0.7288037 0.00000002142 0.7459716450769 0.6659777058891 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_36 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9906084551879:ℝ):ℂ) + ((0.136729252577:ℝ):ℂ) * I)‖ ≤ 0.00000016255 := by
  have hl := lg_36
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.261064723617720656 75.26106476562176266 0.1371589 0.00000006254 0.9906084551879 0.136729252577 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_37 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9054853593968:ℝ):ℂ) + (((-0.4243775016634):ℝ):ℂ) * I)‖ ≤ 0.00000013538 := by
  have hl := lg_37
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.836497979516490884 75.83649802152055389 (-0.4382743) 0.00000003537 0.9054853593968 (-0.4243775016634) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_38 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5416809185991:ℝ):ℂ) + (((-0.8405841911586):ℝ):ℂ) * I)‖ ≤ 0.0000001606 := by
  have hl := lg_38
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.396584504736036206 76.396584546740099212 (-0.9983608) 0.00000006059 0.5416809185991 (-0.8405841911586) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_39 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0268950833327:ℝ):ℂ) + (((-0.9996382618189):ℝ):ℂ) * I)‖ ≤ 0.00000012604 := by
  have hl := lg_39
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.942121670177323728 76.942121712181386734 (-1.543898) 0.00000002603 0.0268950833327 (-0.9996382618189) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_40 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4836553917673):ℝ):ℂ) + (((-0.8752585115317):ℝ):ℂ) * I)‖ ≤ 0.00000013437 := by
  have hl := lg_40
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.473846268004017418 77.47384632050903842 (-2.0756226) 0.00000003436 (-0.4836553917673) (-0.8752585115317) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_41 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8538932450248):ℝ):ℂ) + (((-0.5204481972538):ℝ):ℂ) * I)‖ ≤ 0.00000016854 := by
  have hl := lg_41
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.99244051762698916 77.992440570132031164 (-2.5942169) 0.00000006853 (-0.8538932450248) (-0.5204481972538) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_42 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9991481405539):ℝ):ℂ) + (((-0.0412673313416):ℝ):ℂ) * I)‖ ≤ 0.00000015721 := by
  have hl := lg_42
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.498537301349793172 78.498537343353856178 (-3.1003136) 0.0000000572 (-0.9991481405539) (-0.0412673313416) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_43 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8991782185489):ℝ):ℂ) + ((0.4375825992562:ℝ):ℂ) * I)‖ ≤ 0.00000015664 := by
  have hl := lg_43
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.99272480795868756 78.992724849962771568 2.6886842 0.00000005663 (-0.8991782185489) 0.4375825992562 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
