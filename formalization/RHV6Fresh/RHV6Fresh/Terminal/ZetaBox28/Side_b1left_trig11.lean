/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 11

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

lemma cs_b1left_v24p492_10 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9882031673211:ℝ):ℂ) + ((0.1531486209426:ℝ):ℂ) * I)‖ ≤ 0.00000015065 := by
  have hl := lg_10
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.394914078510406828 56.39491411524843132 0.1537537 0.00000005064 0.9882031673211 0.1531486209426 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_11 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5726928401125):ℝ):ℂ) + (((-0.8197700353598):ℝ):ℂ) * I)‖ ≤ 0.00000016235 := by
  have hl := lg_11
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.729251002277910236 58.72925103901595922 (-2.1805833) 0.00000006234 (-0.5726928401125) (-0.8197700353598) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_12 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.390084234975):ℝ):ℂ) + ((0.9207791752754:ℝ):ℂ) * I)‖ ≤ 0.0000001243 := by
  have hl := lg_12
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.860333647507952688 60.86033368424597718 1.9715194 0.00000002429 (-0.390084234975) 0.9207791752754 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_13 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999382468058:ℝ):ℂ) + ((0.0111131712364:ℝ):ℂ) * I)‖ ≤ 0.00000012796 := by
  have hl := lg_13
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.8207396438481964 62.820739680586245384 0.0111134 0.00000002795 0.9999382468058 0.0111131712364 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_14 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2310363079917):ℝ):ℂ) + (((-0.9729451291766):ℝ):ℂ) * I)‖ ≤ 0.00000016279 := by
  have hl := lg_14
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.635792097837155624 64.635792134575204608 (-1.803939) 0.00000006278 (-0.2310363079917) (-0.9729451291766) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_15 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9386437440066):ℝ):ℂ) + ((0.3448882741713:ℝ):ℂ) * I)‖ ≤ 0.00000016407 := by
  have hl := lg_15
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.325565506295559516 66.3255655430336085 2.7894729 0.00000006406 (-0.9386437440066) 0.3448882741713 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_16 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3541461878559:ℝ):ℂ) + ((0.9351900756676:ℝ):ℂ) * I)‖ ≤ 0.00000012965 := by
  have hl := lg_16
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.9062429596304 67.9062430086144 1.2087954 0.00000002964 0.3541461878559 0.9351900756676 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_17 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9621469560635:ℝ):ℂ) + (((-0.2725311632413):ℝ):ℂ) * I)‖ ≤ 0.00000016718 := by
  have hl := lg_17
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.391061197158501528 69.39106124614252602 (-0.2760228) 0.00000006717 0.9621469560635 (-0.2725311632413) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_18 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1049567126775):ℝ):ℂ) + (((-0.9944767913146):ℝ):ℂ) * I)‖ ≤ 0.00000013307 := by
  have hl := lg_18
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.790985075293105376 70.79098511203115436 (-1.6759467) 0.00000003306 (-0.1049567126775) (-0.9944767913146) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_19 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9900152180093):ℝ):ℂ) + (((-0.1409605182424):ℝ):ℂ) * I)‖ ≤ 0.00000012035 := by
  have hl := lg_19
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.115199458644680676 72.115199495382754152 (-3.0001611) 0.00000002034 (-0.9900152180093) (-0.1409605182424) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_20 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4403176838958):ℝ):ℂ) + ((0.8978420447074:ℝ):ℂ) * I)‖ ≤ 0.00000016775 := by
  have hl := lg_20
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.371474818418006828 73.37147486740203132 2.0267488 0.00000006774 (-0.4403176838958) 0.8978420447074 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_21 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6735610998733:ℝ):ℂ) + ((0.7391315476541:ℝ):ℂ) * I)‖ ≤ 0.00000016055 := by
  have hl := lg_21
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.566443525622308312 74.566443562360381788 0.8317801 0.00000006054 0.6735610998733 0.7391315476541 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_22 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9530665701122:ℝ):ℂ) + (((-0.3027608180307):ℝ):ℂ) * I)‖ ≤ 0.00000014398 := by
  have hl := lg_22
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.705811742185510236 75.70581179116955922 (-0.3075881) 0.00000004397 0.9530665701122 (-0.3027608180307) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_23 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1736115442696:ℝ):ℂ) + (((-0.984814211766):ℝ):ℂ) * I)‖ ≤ 0.00000017391 := by
  have hl := lg_23
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.794524311070352072 76.794524360054425548 (-1.3963006) 0.0000000739 0.1736115442696 (-0.984814211766) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_24 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7629565507352):ℝ):ℂ) + (((-0.6464497673083):ℝ):ℂ) * I)‖ ≤ 0.00000015026 := by
  have hl := lg_24
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.836894387415552688 77.83689443639957718 (-2.4386707) 0.00000005025 (-0.7629565507352) (-0.6464497673083) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_25 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9562508319127):ℝ):ℂ) + ((0.292548023827:ℝ):ℂ) * I)‖ ≤ 0.00000013287 := by
  have hl := lg_25
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.836706677205613656 78.83670672618966264 2.8447023 0.00000003286 (-0.9562508319127) 0.292548023827 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_26 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3082113462205):ℝ):ℂ) + ((0.9513179100906:ℝ):ℂ) * I)‖ ≤ 0.00000013942 := by
  have hl := lg_26
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.7973003837557964 79.797300432739845384 1.8841086 0.00000003941 (-0.3082113462205) 0.9513179100906 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_27 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.573706337311:ℝ):ℂ) + ((0.8190610713062:ℝ):ℂ) * I)‖ ≤ 0.0000001465 := by
  have hl := lg_27
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.721636503078258064 80.72163653981633154 0.9597725 0.00000004649 0.573706337311 0.8190610713062 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_28 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9976165749145:ℝ):ℂ) + ((0.0690012279305:ℝ):ℂ) * I)‖ ≤ 0.0000001556 := by
  have hl := lg_28
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.612352837744755624 81.612352886728804608 0.0690561 0.00000005559 0.9976165749145 0.0690012279305 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_29 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7035607627258:ℝ):ℂ) + (((-0.7106351054886):ℝ):ℂ) * I)‖ ≤ 0.00000015079 := by
  have hl := lg_29
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.471809442562380464 82.47180949154645394 (-0.7904005) 0.00000005078 0.7035607627258 (-0.7106351054886) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_30 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0499002410828):ℝ):ℂ) + (((-0.9987542069697):ℝ):ℂ) * I)‖ ≤ 0.00000014715 := by
  have hl := lg_30
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.302126246203159516 83.3021262951872085 (-1.6207173) 0.00000004714 (-0.0499002410828) (-0.9987542069697) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_2 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2482816662937):ℝ):ℂ) + ((0.9686878827472:ℝ):ℂ) * I)‖ ≤ 0.00000012201 := by
  have hl := lg_2
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.0278536312498 17.0278536435328 1.8217023 0.000000022 (-0.2482816662937) 0.9686878827472 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_3 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2811305549447):ℝ):ℂ) + (((-0.9596695322219):ℝ):ℂ) * I)‖ ≤ 0.0000001517 := by
  have hl := lg_3
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.988509477034956824 26.98850948931798139 (-1.8557683) 0.00000005169 (-0.2811305549447) (-0.9596695322219) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_4 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8767124248862):ℝ):ℂ) + (((-0.4810148895375):ℝ):ℂ) * I)‖ ≤ 0.00000015118 := by
  have hl := lg_4
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.0557072624996 34.0557072870656 (-2.6397807) 0.00000005117 (-0.8767124248862) (-0.4810148895375) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_5 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2643632016831):ℝ):ℂ) + (((-0.9644231942433):ℝ):ℂ) * I)‖ ≤ 0.00000012559 := by
  have hl := lg_5
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.537451744084458294 39.53745176865048286 (-1.8383399) 0.00000002558 (-0.2643632016831) (-0.9644231942433) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_6 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9994198099341:ℝ):ℂ) + (((-0.0340594114935):ℝ):ℂ) * I)‖ ≤ 0.00000014199 := by
  have hl := lg_6
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.016363108284756824 44.01636313285078139 (-0.034066) 0.00000004198 0.9994198099341 (-0.0340594114935) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_7 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7779882101913):ℝ):ℂ) + ((0.6282788749924:ℝ):ℂ) * I)‖ ≤ 0.00000014853 := by
  have hl := lg_7
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.803228708921176852 47.803228733487225984 2.4622537 0.00000004852 (-0.7779882101913) 0.6282788749924 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_8 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6836248436996:ℝ):ℂ) + (((-0.7298335927297):ℝ):ℂ) * I)‖ ≤ 0.0000001637 := by
  have hl := lg_8
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.0835608937494 51.0835609305984 (-0.8180785) 0.00000006369 0.6836248436996 (-0.7298335927297) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_9 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8419312722211):ℝ):ℂ) + ((0.5395847781277:ℝ):ℂ) * I)‖ ≤ 0.00000011403 := by
  have hl := lg_9
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.977018954069913648 53.97701897863596278 2.5716488 0.00000001402 (-0.8419312722211) 0.5395847781277 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_10 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9998615983257:ℝ):ℂ) + (((-0.0166368324357):ℝ):ℂ) * I)‖ ≤ 0.00000014758 := by
  have hl := lg_10
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.565305375334258294 56.56530541218328286 (-0.0166376) 0.00000004757 0.9998615983257 (-0.0166368324357) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_11 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7084017262096):ℝ):ℂ) + (((-0.7058094603206):ℝ):ℂ) * I)‖ ≤ 0.00000012466 := by
  have hl := lg_11
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.906695252407281678 58.90669528925633081 (-2.3580275) 0.00000002465 (-0.7084017262096) (-0.7058094603206) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_12 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.21514467653):ℝ):ℂ) + ((0.9765821870994:ℝ):ℂ) * I)‖ ≤ 0.00000013228 := by
  have hl := lg_12
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.044216739534556824 61.04421677638358139 1.7876363 0.00000003227 (-0.21514467653) 0.9765821870994 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_13 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9840768795978:ℝ):ℂ) + (((-0.1777433403566):ℝ):ℂ) * I)‖ ≤ 0.00000016131 := by
  have hl := lg_13
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.0105458962426422 63.010545933091691332 (-0.1786928) 0.0000000613 0.9840768795978 (-0.1777433403566) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_14 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4154459174986):ℝ):ℂ) + (((-0.9096178811073):ℝ):ℂ) * I)‖ ≤ 0.00000013164 := by
  have hl := lg_14
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.831082340170976852 64.831082377020025984 (-1.9992293) 0.00000003163 (-0.4154459174986) (-0.9096178811073) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_15 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8512069783024):ℝ):ℂ) + ((0.5248301439654:ℝ):ℂ) * I)‖ ≤ 0.00000015787 := by
  have hl := lg_15
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.525961221119415118 66.52596125796846425 2.5890771 0.00000005786 (-0.8512069783024) 0.5248301439654 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_16 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5372494423861:ℝ):ℂ) + ((0.8434234029571:ℝ):ℂ) * I)‖ ≤ 0.00000015399 := by
  have hl := lg_16
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.1114145249992 68.1114145741312 1.0036238 0.00000005398 0.5372494423861 0.8434234029571 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_17 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8843574428256:ℝ):ℂ) + (((-0.4668103611949):ℝ):ℂ) * I)‖ ≤ 0.00000015471 := by
  have hl := lg_17
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.600718984541717644 69.60071903367374221 (-0.4856806) 0.0000000547 0.8843574428256 (-0.4668103611949) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_18 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3136531303315):ℝ):ℂ) + (((-0.9495376316036):ℝ):ℂ) * I)‖ ≤ 0.00000014321 := by
  have hl := lg_18
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.004872585319713648 71.00487262216876278 (-1.8898342) 0.0000000432 (-0.3136531303315) (-0.9495376316036) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_19 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9970785904298):ℝ):ℂ) + ((0.0763824848185:ℝ):ℂ) * I)‖ ≤ 0.00000014312 := by
  have hl := lg_19
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.333087943045289298 72.333087979894362996 3.0651357 0.00000004311 (-0.9970785904298) 0.0763824848185 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_20 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2321314057076):ℝ):ℂ) + ((0.9726844352014:ℝ):ℂ) * I)‖ ≤ 0.00000016958 := by
  have hl := lg_20
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.593159006584058294 73.59315905571608286 1.8050647 0.00000006957 (-0.2321314057076) 0.9726844352014 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_21 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8216562943671:ℝ):ℂ) + ((0.5699832751291:ℝ):ℂ) * I)‖ ≤ 0.00000013667 := by
  have hl := lg_21
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.791738185956133676 74.791738222805207374 0.6064855 0.00000003666 0.8216562943671 0.5699832751291 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_22 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8595922327446:ℝ):ℂ) + (((-0.5109806194026):ℝ):ℂ) * I)‖ ≤ 0.00000014665 := by
  have hl := lg_22
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.934548883657081678 75.93454893278913081 (-0.5363252) 0.00000004664 0.8595922327446 (-0.5109806194026) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_23 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0574991424962):ℝ):ℂ) + (((-0.998345555713):ℝ):ℂ) * I)‖ ≤ 0.00000014596 := by
  have hl := lg_23
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.026550882972165156 77.026550932104238854 (-1.6283272) 0.00000004595 (-0.0574991424962) (-0.998345555713) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_24 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8925868490999):ℝ):ℂ) + (((-0.4508755002277):ℝ):ℂ) * I)‖ ≤ 0.00000013378 := by
  have hl := lg_24
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.072070370784356824 78.07207041991638139 (-2.6738467) 0.00000003377 (-0.8925868490999) (-0.4508755002277) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_25 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8602241915102):ℝ):ℂ) + ((0.5099160129472:ℝ):ℂ) * I)‖ ≤ 0.00000014398 := by
  have hl := lg_25
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.074903488168916588 79.07490353730096572 2.6065055 0.00000004397 (-0.8602241915102) 0.5099160129472 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_26 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0721503276457):ℝ):ℂ) + ((0.9973937688898:ℝ):ℂ) * I)‖ ≤ 0.00000016586 := by
  have hl := lg_26
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.0383995274924422 80.038399576624491332 1.6430094 0.00000006585 (-0.0721503276457) 0.9973937688898 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_27 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7545156774463:ℝ):ℂ) + ((0.6562820220665:ℝ):ℂ) * I)‖ ≤ 0.00000016224 := by
  have hl := lg_27
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.965528431104870472 80.96552846795394417 0.7158805 0.00000006223 0.7545156774463 0.6562820220665 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_28 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9842834240128:ℝ):ℂ) + (((-0.1765959830056):ℝ):ℂ) * I)‖ ≤ 0.00000012723 := by
  have hl := lg_28
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.858935971420776852 81.858936020552825984 (-0.177527) 0.00000002722 0.9842834240128 (-0.1765959830056) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_29 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5065820774723:ℝ):ℂ) + (((-0.8621917413104):ℝ):ℂ) * I)‖ ≤ 0.00000015945 := by
  have hl := lg_29
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.720989333904435672 82.72098938303650937 (-1.0395804) 0.00000005944 0.5065820774723 (-0.8621917413104) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_30 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2970575072064):ℝ):ℂ) + (((-0.9548595904166):ℝ):ℂ) * I)‖ ≤ 0.00000014098 := by
  have hl := lg_30
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.553814852369215118 83.55381490150126425 (-1.8724059) 0.00000004097 (-0.2970575072064) (-0.9548595904166) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_31 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8944163034719):ℝ):ℂ) + (((-0.4472353697701):ℝ):ℂ) * I)‖ ≤ 0.00000015351 := by
  have hl := lg_31
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.359329639838787458 84.359329688970861156 (-2.6779207) 0.0000000535 (-0.8944163034719) (-0.4472353697701) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_32 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9504032171686):ℝ):ℂ) + ((0.3110204568693:ℝ):ℂ) * I)‖ ≤ 0.00000014428 := by
  have hl := lg_32
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.139268156249 85.139268217664 2.8253261 0.00000004427 (-0.9504032171686) 0.3110204568693 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_33 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4781904579183):ℝ):ℂ) + ((0.87825616192:ℝ):ℂ) * I)‖ ≤ 0.00000017109 := by
  have hl := lg_33
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.895204729442238502 85.8952047785743122 2.0693895 0.00000007108 (-0.4781904579183) 0.87825616192 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_34 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2326238009267:ℝ):ℂ) + ((0.9725667932036:ℝ):ℂ) * I)‖ ≤ 0.00000017671 := by
  have hl := lg_34
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.628572615791517644 86.62857267720654221 1.3360217 0.0000000767 0.2326238009267 0.9725667932036 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_35 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8115981736387:ℝ):ℂ) + ((0.5842160598155:ℝ):ℂ) * I)‖ ≤ 0.00000014752 := by
  have hl := lg_35
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.340680453005635146 87.340680502137708844 0.6239138 0.00000004751 0.8115981736387 0.5842160598155 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_36 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9976799197854:ℝ):ℂ) + (((-0.0680792013547):ℝ):ℂ) * I)‖ ≤ 0.0000001652 := by
  have hl := lg_36
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.032726216569513648 88.03272626570156278 (-0.0681319) 0.00000006519 0.9976799197854 (-0.0680792013547) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_37 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7376486865273:ℝ):ℂ) + (((-0.6751847267708):ℝ):ℂ) * I)‖ ≤ 0.00000016511 := by
  have hl := lg_37
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.705809416474722172 88.70580946560679587 (-0.7412151) 0.0000000651 0.7376486865273 (-0.6751847267708) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_38 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1735655532566:ℝ):ℂ) + (((-0.9848223183512):ℝ):ℂ) * I)‖ ≤ 0.00000012623 := by
  have hl := lg_38
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.360941574295089298 89.360941623427162996 (-1.3963473) 0.00000002622 0.1735655532566 (-0.9848223183512) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_39 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4472289475651):ℝ):ℂ) + (((-0.8944195148001):ℝ):ℂ) * I)‖ ≤ 0.00000012725 := by
  have hl := lg_39
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.999055373277599024 89.999055422409672722 (-2.0344611) 0.00000002724 (-0.4472289475651) (-0.8944195148001) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p566_40 : ‖exp (-((((((24566:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8845936971695):ℝ):ℂ) + (((-0.4663625101009):ℝ):ℂ) * I)‖ ≤ 0.0000001627 := by
  have hl := lg_40
  refine (ecis_approx ((((24566:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.621012637833858294 90.62101269924888286 (-2.6564184) 0.00000006269 (-0.8845936971695) (-0.4663625101009) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_2 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1982901019132):ℝ):ℂ) + ((0.9801433749622:ℝ):ℂ) * I)‖ ≤ 0.00000011339 := by
  have hl := lg_2
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.079146522592 17.079146534912 1.7704094 0.00000001338 (-0.1982901019132) 0.9801433749622 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_3 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3581346648866):ℝ):ℂ) + (((-0.9336699426479):ℝ):ℂ) * I)‖ ≤ 0.00000014236 := by
  have hl := lg_3
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.06980678637716096 27.0698067986971856 (-1.9370656) 0.00000004235 (-0.3581346648866) (-0.9336699426479) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_4 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9213620681297):ℝ):ℂ) + (((-0.3887054659595):ℝ):ℂ) * I)‖ ≤ 0.00000013394 := by
  have hl := lg_4
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.158293045184 34.158293069824 (-2.7423665) 0.00000003393 (-0.9213620681297) (-0.3887054659595) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_5 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3770804079889):ℝ):ℂ) + (((-0.92618052555):ℝ):ℂ) * I)‖ ≤ 0.00000013114 := by
  have hl := lg_5
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.65655014956610976 39.6565501742061344 (-1.9574383) 0.00000003113 (-0.3770804079889) (-0.92618052555) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_6 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9861449678884:ℝ):ℂ) + (((-0.1658858110518):ℝ):ℂ) * I)‖ ≤ 0.0000001413 := by
  have hl := lg_6
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.14895330896916096 44.1489533336091856 (-0.1666562) 0.00000004129 0.9861449678884 (-0.1658858110518) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_7 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.679778127153):ℝ):ℂ) + ((0.733417819407:ℝ):ℂ) * I)‖ ≤ 0.00000012713 := by
  have hl := lg_7
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.94722605991279808 47.94722608455284736 2.3182564 0.00000002712 (-0.679778127153) 0.733417819407 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_8 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5636840657452:ℝ):ℂ) + (((-0.8259904805898):ℝ):ℂ) * I)‖ ≤ 0.00000014731 := by
  have hl := lg_8
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.237439567776 51.237439604736 (-0.9719571) 0.0000000473 0.5636840657452 (-0.8259904805898) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_9 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7434791856825):ℝ):ℂ) + ((0.6687590750223:ℝ):ℂ) * I)‖ ≤ 0.00000013279 := by
  have hl := lg_9
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.13961357275432192 54.1396135973943712 2.4090542 0.00000003278 (-0.7434791856825) 0.6687590750223 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_10 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9825610186684:ℝ):ℂ) + (((-0.1859404329169):ℝ):ℂ) * I)‖ ≤ 0.00000014452 := by
  have hl := lg_10
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.73569667215810976 56.7356967091181344 (-0.1870289) 0.00000004451 0.9825610186684 (-0.1859404329169) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_11 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8218640820781):ℝ):ℂ) + (((-0.5696836231905):ℝ):ℂ) * I)‖ ≤ 0.00000016209 := by
  have hl := lg_11
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.08413950253665312 59.0841395394967024 (-2.5354718) 0.00000006208 (-0.8218640820781) (-0.5696836231905) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_12 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.032950907481):ℝ):ℂ) + ((0.9994569714079:ℝ):ℂ) * I)‖ ≤ 0.00000014025 := by
  have hl := lg_12
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.22809983156116096 61.2280998685211856 1.6037532 0.00000004024 (-0.032950907481) 0.9994569714079 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_13 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.932869043877:ℝ):ℂ) + (((-0.3602156950717):ℝ):ℂ) * I)‖ ≤ 0.00000012317 := by
  have hl := lg_13
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.200352148637088 63.20035218559713728 (-0.3684991) 0.00000002316 0.932869043877 (-0.3602156950717) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_14 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5840613368424):ℝ):ℂ) + (((-0.8117095261207):ℝ):ℂ) * I)‖ ≤ 0.00000014768 := by
  have hl := lg_14
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.02637258250479808 65.02637261946484736 (-2.1945195) 0.00000004767 (-0.5840613368424) (-0.8117095261207) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_15 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7297013477106):ℝ):ℂ) + ((0.6837660002663:ℝ):ℂ) * I)‖ ≤ 0.00000014305 := by
  have hl := lg_15
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.72635693594327072 66.72635697290332 2.3886814 0.00000004304 (-0.7297013477106) 0.6837660002663 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_16 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.697816126489:ℝ):ℂ) + ((0.7162769391876:ℝ):ℂ) * I)‖ ≤ 0.00000016069 := by
  have hl := lg_16
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.316586090368 68.316586139648 0.7984523 0.00000006068 0.697816126489 0.7162769391876 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_17 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7678369513868:ℝ):ℂ) + (((-0.6406453122321):ℝ):ℂ) * I)‖ ≤ 0.00000014224 := by
  have hl := lg_17
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.81037677192493376 69.8103768212049584 (-0.6953384) 0.00000004223 0.7678369513868 (-0.6406453122321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_18 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5080552071627):ℝ):ℂ) + (((-0.8613245070635):ℝ):ℂ) * I)‖ ≤ 0.00000015335 := by
  have hl := lg_18
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.21876009534632192 71.2187601323063712 (-2.1037217) 0.00000005334 (-0.5080552071627) (-0.8613245070635) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_19 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9569922399889):ℝ):ℂ) + ((0.290113516365:ℝ):ℂ) * I)‖ ≤ 0.00000015872 := by
  have hl := lg_19
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.55097642744589792 72.55097646440597184 2.8472472 0.00000005871 (-0.9569922399889) 0.290113516365 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_20 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0125838410665):ℝ):ℂ) + ((0.9999208203372:ℝ):ℂ) * I)‖ ≤ 0.00000015789 := by
  have hl := lg_20
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.81484319475010976 73.8148432440301344 1.5833805 0.00000005788 (-0.0125838410665) 0.9999208203372 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_21 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9282222851606:ℝ):ℂ) + ((0.3720260600162:ℝ):ℂ) * I)‖ ≤ 0.00000013988 := by
  have hl := lg_21
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.01703284628995904 75.01703288325003296 0.3811908 0.00000003987 0.9282222851606 0.3720260600162 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_22 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7213391417235:ℝ):ℂ) + (((-0.6925820114742):ℝ):ℂ) * I)‖ ≤ 0.00000016104 := by
  have hl := lg_22
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.16328602512865312 76.1632860744087024 (-0.7650624) 0.00000006103 0.7213391417235 (-0.6925820114742) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_23 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2855281485288):ℝ):ℂ) + (((-0.958370323203):ℝ):ℂ) * I)‖ ≤ 0.0000001313 := by
  have hl := lg_23
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.25857745487397824 77.25857750415405216 (-1.8603538) 0.00000003129 (-0.2855281485288) (-0.958370323203) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_24 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9730772885157):ℝ):ℂ) + (((-0.2304790452276):ℝ):ℂ) * I)‖ ≤ 0.00000013202 := by
  have hl := lg_24
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.30724635415316096 78.3072464034331856 (-2.9090227) 0.00000003201 (-0.9730772885157) (-0.2304790452276) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_25 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7156207268033):ℝ):ℂ) + ((0.6984890660154:ℝ):ℂ) * I)‖ ≤ 0.00000015509 := by
  have hl := lg_25
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.31310029913221952 79.3131003484122688 2.3683087 0.00000005508 (-0.7156207268033) 0.6984890660154 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_26 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1680843293001:ℝ):ℂ) + ((0.9857726199503:ℝ):ℂ) * I)‖ ≤ 0.00000012719 := by
  have hl := lg_26
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.279498671229088 80.27949872050913728 1.4019103 0.00000002718 0.1680843293001 0.9857726199503 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_27 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8906659162556:ℝ):ℂ) + ((0.4546583614325:ℝ):ℂ) * I)‖ ≤ 0.00000013422 := by
  have hl := lg_27
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.20942035913148288 81.2094203960915568 0.4719886 0.00000003421 0.8906659162556 0.4546583614325 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_28 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9114052964335:ℝ):ℂ) + (((-0.411509885219):ℝ):ℂ) * I)‖ ≤ 0.00000016106 := by
  have hl := lg_28
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.10551910509679808 82.10551915437684736 (-0.4241101) 0.00000006105 0.9114052964335 (-0.411509885219) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_29 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2783118090331:ℝ):ℂ) + (((-0.9604907792127):ℝ):ℂ) * I)‖ ≤ 0.0000001681 := by
  have hl := lg_29
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.97016922524649088 82.9701692745265648 (-1.2887603) 0.00000006809 0.2783118090331 (-0.9604907792127) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_30 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5254961544888):ℝ):ℂ) + (((-0.8507959753138):ℝ):ℂ) * I)‖ ≤ 0.00000013481 := by
  have hl := lg_30
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.80550345853527072 83.80550350781532 (-2.1240945) 0.0000000348 (-0.5254961544888) (-0.8507959753138) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_31 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9781231760156):ℝ):ℂ) + (((-0.2080265661597):ℝ):ℂ) * I)‖ ≤ 0.00000014885 := by
  have hl := lg_31
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.61344469289374432 84.61344474217381824 (-2.9320357) 0.00000004884 (-0.9781231760156) (-0.2080265661597) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_32 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8404241274052):ℝ):ℂ) + ((0.541929226013:ℝ):ℂ) * I)‖ ≤ 0.00000017406 := by
  have hl := lg_32
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.39573261296 85.39573267456 2.5688617 0.00000007405 (-0.8404241274052) 0.541929226013 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_33 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2375585483644):ℝ):ℂ) + ((0.9713732218349:ℝ):ℂ) * I)‖ ≤ 0.00000013769 := by
  have hl := lg_33
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.15394628891381408 86.153946338193888 1.810648 0.00000003768 (-0.2375585483644) 0.9713732218349 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_34 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4756697911421:ℝ):ℂ) + ((0.879623925206:ℝ):ℂ) * I)‖ ≤ 0.00000015562 := by
  have hl := lg_34
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.88952329451693376 86.8895233561169584 1.075071 0.00000005561 0.4756697911421 0.879623925206 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_35 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9356083149678:ℝ):ℂ) + ((0.3530397724948:ℝ):ℂ) * I)‖ ≤ 0.00000015826 := by
  have hl := lg_35
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.60377620947890784 87.60377625875898176 0.3608181 0.00000005825 0.9356083149678 0.3530397724948 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_36 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9449638281008:ℝ):ℂ) + (((-0.3271748211293):ℝ):ℂ) * I)‖ ≤ 0.00000016672 := by
  have hl := lg_36
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.29790661793832192 88.2979066672183712 (-0.3333123) 0.00000006671 0.9449638281008 (-0.3271748211293) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_37 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5331954286908:ℝ):ℂ) + (((-0.8459921009225):ℝ):ℂ) * I)‖ ≤ 0.0000001586 := by
  have hl := lg_37
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.97301734193345088 88.9730173912135248 (-1.0084231) 0.00000005859 0.5331954286908 (-0.8459921009225) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_38 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0945907452038):ℝ):ℂ) + (((-0.9955162434242):ℝ):ℂ) * I)‖ ≤ 0.00000015049 := by
  have hl := lg_38
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.63012295003789792 89.63012299931797184 (-1.6655287) 0.00000005048 (-0.0945907452038) (-0.9955162434242) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_39 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6704153097686):ℝ):ℂ) + (((-0.7419860594435):ℝ):ℂ) * I)‖ ≤ 0.00000016551 := by
  have hl := lg_39
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.27015893501424896 90.27015898429432288 (-2.3055647) 0.0000000655 (-0.6704153097686) (-0.7419860594435) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p64_40 : ‖exp (-((((((24640:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9775705147761):ℝ):ℂ) + (((-0.2106083766872):ℝ):ℂ) * I)‖ ≤ 0.00000017844 := by
  have hl := lg_40
  refine (ecis_approx ((((24640:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.89398971734210976 90.8939897789421344 (-2.9293954) 0.00000007843 (-0.9775705147761) (-0.2106083766872) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_2 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1607889714249):ℝ):ℂ) + ((0.9869888077721:ℝ):ℂ) * I)‖ ≤ 0.00000010833 := by
  have hl := lg_2
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.1172696175085 17.117269629856 1.7322863 0.00000000832 (-0.1607889714249) 0.9869888077721 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_3 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4138624632483):ℝ):ℂ) + (((-0.910339421046):ℝ):ℂ) * I)‖ ≤ 0.00000014588 := by
  have hl := lg_3
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.13023046223960998 27.130230474587134675 (-1.9974892) 0.00000004587 (-0.4138624632483) (-0.910339421046) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_4 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9482938109873):ℝ):ℂ) + (((-0.317393837124):ℝ):ℂ) * I)‖ ≤ 0.00000012383 := by
  have hl := lg_4
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.234539235017 34.234539259712 (-2.8186127) 0.00000002382 (-0.9482938109873) (-0.317393837124) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_5 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4574816824745):ℝ):ℂ) + (((-0.8892190451151):ℝ):ℂ) * I)‖ ≤ 0.00000011635 := by
  have hl := lg_5
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.745069234721391255 39.74506925941641595 (-2.0459574) 0.00000001634 (-0.4574816824745) (-0.8892190451151) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_6 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9650393396255:ℝ):ℂ) + (((-0.2621050800254):ℝ):ℂ) * I)‖ ≤ 0.0000001542 := by
  have hl := lg_6
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.24750007974810998 44.247500104443134675 (-0.2652029) 0.00000005419 0.9650393396255 (-0.2621050800254) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_7 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5975442750179):ℝ):ℂ) + ((0.8018359179916:ℝ):ℂ) * I)‖ ≤ 0.00000013937 := by
  have hl := lg_7
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.05425111808224629 48.05425114277729568 2.2112313 0.00000003936 (-0.5975442750179) 0.8018359179916 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_8 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4657393514878:ℝ):ℂ) + (((-0.8849219493694):ℝ):ℂ) * I)‖ ≤ 0.00000013215 := by
  have hl := lg_8
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.3518088525255 51.351808889568 (-1.0863264) 0.00000003214 0.4657393514878 (-0.8849219493694) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_9 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6574356422653):ℝ):ℂ) + ((0.7535107008275:ℝ):ℂ) * I)‖ ≤ 0.00000014015 := by
  have hl := lg_9
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.26046092447921996 54.26046094917426935 2.2882068 0.00000004014 (-0.6574356422653) 0.7535107008275 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_10 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9512072543602:ℝ):ℂ) + (((-0.3085526847275):ℝ):ℂ) * I)‖ ≤ 0.00000012467 := by
  have hl := lg_10
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.862338852229891255 56.86233888927241595 (-0.3136711) 0.00000002466 0.9512072543602 (-0.3085526847275) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_11 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8896415701269):ℝ):ℂ) + (((-0.456659475536):ℝ):ℂ) * I)‖ ≤ 0.00000012213 := by
  have hl := lg_11
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.216023742497672435 59.216023779540221825 (-2.667356) 0.00000002212 (-0.8896415701269) (-0.456659475536) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_12 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1035270976425:ℝ):ℂ) + ((0.994626633493:ℝ):ℂ) * I)‖ ≤ 0.00000016252 := by
  have hl := lg_12
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.36476969725660998 61.364769734299134675 1.4670834 0.00000006251 0.1035270976425 0.994626633493 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_13 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.872953709027:ℝ):ℂ) + (((-0.4878030564644):ℝ):ℂ) * I)‖ ≤ 0.00000012852 := by
  have hl := lg_13
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.3414243632545815 63.34142440029713089 (-0.5095713) 0.00000002851 0.872953709027 (-0.4878030564644) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_14 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6953245422103):ℝ):ℂ) + (((-0.7186958890776):ℝ):ℂ) * I)‖ ≤ 0.00000013622 := by
  have hl := lg_14
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.17152073559074629 65.17152077263329568 (-2.3396677) 0.00000003621 (-0.6953245422103) (-0.7186958890776) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_15 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6201566490842):ℝ):ℂ) + ((0.7844779987883:ℝ):ℂ) * I)‖ ≤ 0.00000015504 := by
  have hl := lg_15
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.875299696961001235 66.875299734003550625 2.2397387 0.00000005503 (-0.6201566490842) 0.7844779987883 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_16 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.798522308502:ℝ):ℂ) + ((0.601965217288:ℝ):ℂ) * I)‖ ≤ 0.00000014046 := by
  have hl := lg_16
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.469078470034 68.469078519424 0.6459599 0.00000004045 0.798522308502 0.601965217288 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_17 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6591073061284:ℝ):ℂ) + (((-0.7520489073246):ℝ):ℂ) * I)‖ ≤ 0.0000001732 := by
  have hl := lg_17
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.96620350579083763 69.966203555180862325 (-0.8511652) 0.00000007319 0.6591073061284 (-0.7520489073246) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_18 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6379982220352):ℝ):ℂ) + (((-0.7700378358655):ℝ):ℂ) * I)‖ ≤ 0.000000137 := by
  have hl := lg_18
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.37773054198771996 71.37773057903026935 (-2.2626922) 0.00000003699 (-0.6379982220352) (-0.7700378358655) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_19 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8976935712173):ℝ):ℂ) + ((0.4406203037552:ℝ):ℂ) * I)‖ ≤ 0.00000012216 := by
  have hl := lg_19
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.712920571257161085 72.71292060829973517 2.6853031 0.00000002215 (-0.8976935712173) 0.4406203037552 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_20 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1515944103938:ℝ):ℂ) + ((0.9884427827332:ℝ):ℂ) * I)‖ ≤ 0.00000013299 := by
  have hl := lg_20
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.979608469738391255 73.97960851912841595 1.4186152 0.00000003298 0.1515944103938 0.9884427827332 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_21 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9772439909253:ℝ):ℂ) + ((0.2121183212275:ℝ):ℂ) * I)‖ ≤ 0.00000013122 := by
  have hl := lg_21
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.18448158032185627 75.184481617364430355 0.2137421 0.00000003121 0.9772439909253 0.2121183212275 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_22 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.593762344376:ℝ):ℂ) + (((-0.8046404653018):ℝ):ℂ) * I)‖ ≤ 0.00000012616 := by
  have hl := lg_22
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.333293360006172435 76.333293409396221825 (-0.9350697) 0.00000002615 0.593762344376 (-0.8046404653018) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_23 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4457479819425):ℝ):ℂ) + (((-0.8951584980269):ℝ):ℂ) * I)‖ ≤ 0.00000014948 := by
  have hl := lg_23
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.43102963669289337 77.431029686082967455 (-2.032806) 0.00000004947 (-0.4457479819425) (-0.8951584980269) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_24 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9983313758104):ℝ):ℂ) + (((-0.0577448137554):ℝ):ℂ) * I)‖ ≤ 0.0000001714 := by
  have hl := lg_24
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.48203931476510998 78.482039364155134675 (-3.0838157) 0.00000007139 (-0.9983313758104) (-0.0577448137554) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_25 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5814210145585):ℝ):ℂ) + ((0.8136028538661:ℝ):ℂ) * I)‖ ≤ 0.00000012551 := by
  have hl := lg_25
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.49013846944278251 79.4901385188328319 2.1912705 0.0000000255 (-0.5814210145585) 0.8136028538661 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_26 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3410948281517:ℝ):ℂ) + ((0.9400288922199:ℝ):ℂ) * I)‖ ≤ 0.00000013683 := by
  have hl := lg_26
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.4586939807630815 80.45869403015313089 1.222715 0.00000003682 0.3410948281517 0.9400288922199 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_27 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9580384294899:ℝ):ℂ) + ((0.2866397872254:ℝ):ℂ) * I)‖ ≤ 0.00000013044 := by
  have hl := lg_27
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.39069138671882994 81.390691423761404025 0.2907176 0.00000003043 0.9580384294899 0.2866397872254 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_28 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8211453166735:ℝ):ℂ) + (((-0.57071916816):ℝ):ℂ) * I)‖ ≤ 0.00000014025 := by
  have hl := lg_28
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.28879035309924629 82.28879040248929568 (-0.6073814) 0.00000004024 0.8211453166735 (-0.57071916816) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_29 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0966835613012:ℝ):ℂ) + (((-0.9953151706741):ℝ):ℂ) * I)‖ ≤ 0.00000015191 := by
  have hl := lg_29
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.15537049583855894 83.155370545228633025 (-1.4739615) 0.0000000519 0.0966835613012 (-0.9953151706741) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_30 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6745566497244):ℝ):ℂ) + (((-0.7382230870765):ℝ):ℂ) * I)‖ ≤ 0.00000017054 := by
  have hl := lg_30
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.992569314469501235 83.992569363859550625 (-2.3111603) 0.00000007053 (-0.6745566497244) (-0.7382230870765) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_31 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997860178132):ℝ):ℂ) + (((-0.020686177688):ℝ):ℂ) * I)‖ ≤ 0.00000014515 := by
  have hl := lg_31
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.802313989083239285 84.80231403847331337 (-3.120905) 0.00000004514 (-0.9997860178132) (-0.020686177688) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_32 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7225265127712):ℝ):ℂ) + ((0.6913432131112:ℝ):ℂ) * I)‖ ≤ 0.00000014878 := by
  have hl := lg_32
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.5863480875425 85.58634814928 2.3782462 0.00000004877 (-0.7225265127712) 0.6913432131112 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_33 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0475258638231):ℝ):ℂ) + ((0.9988700076925:ℝ):ℂ) * I)‖ ≤ 0.00000015363 := by
  have hl := lg_33
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.346254204737282415 86.3462542541273565 1.6183401 0.00000005362 (-0.0475258638231) 0.9988700076925 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_34 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6362866686159:ℝ):ℂ) + ((0.7714527045397:ℝ):ℂ) * I)‖ ≤ 0.00000017723 := by
  have hl := lg_34
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.08347312329933763 87.083473185036862325 0.8811211 0.00000007722 0.6362866686159 0.7714527045397 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_35 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9863733296323:ℝ):ℂ) + ((0.1645225048134:ℝ):ℂ) * I)‖ ≤ 0.00000014773 := by
  have hl := lg_35
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.799320352803637545 87.79932040219371163 0.1652739 0.00000004772 0.9863733296323 0.1645225048134 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_36 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8626018034614:ℝ):ℂ) + (((-0.5058835129406):ℝ):ℂ) * I)‖ ≤ 0.00000014103 := by
  have hl := lg_36
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.49500015949621996 88.49500020888626935 (-0.5304059) 0.00000004102 0.8626018034614 (-0.5058835129406) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_37 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.355802600884:ℝ):ℂ) + (((-0.9345611318711):ℝ):ℂ) * I)‖ ≤ 0.00000017346 := by
  have hl := lg_37
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.17161782707169519 89.171617876461769275 (-1.2070236) 0.00000007345 0.355802600884 (-0.9345611318711) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_38 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2905480754987):ℝ):ℂ) + (((-0.9568603951583):ℝ):ℂ) * I)‖ ≤ 0.00000013766 := by
  have hl := lg_38
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.830190188765661085 89.83019023815573517 (-1.8655959) 0.00000003765 (-0.2905480754987) (-0.9568603951583) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_39 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8053491243162):ℝ):ℂ) + (((-0.5928007995203):ℝ):ℂ) * I)‖ ≤ 0.00000017439 := by
  have hl := lg_39
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.47165482549419148 90.471654874884265565 (-2.5070605) 0.00000007438 (-0.8053491243162) (-0.5928007995203) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_40 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999566726056):ℝ):ℂ) + (((-0.0093087188513):ℝ):ℂ) * I)‖ ≤ 0.00000014849 := by
  have hl := lg_40
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 91.096878087246891255 91.09687814898441595 (-3.1322838) 0.00000004848 (-0.9999566726056) (-0.0093087188513) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_41 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8250671733362):ℝ):ℂ) + ((0.5650346532939:ℝ):ℂ) * I)‖ ≤ 0.00000015254 := by
  have hl := lg_41
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.7066621551661031 91.70666221690365249 2.5411174 0.00000005253 (-0.8250671733362) 0.5650346532939 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_42 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3664884651071):ℝ):ℂ) + ((0.9304225948142:ℝ):ℂ) * I)‖ ≤ 0.00000013954 := by
  have hl := lg_42
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.30175119783035627 92.301751247220430355 1.9460284 0.00000003953 (-0.3664884651071) 0.9304225948142 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_43 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2044027404373:ℝ):ℂ) + ((0.9788868778882:ℝ):ℂ) * I)‖ ≤ 0.00000017309 := by
  have hl := lg_43
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.8828368313750971 92.88283688076519588 1.3649428 0.00000007308 0.2044027404373 0.9788868778882 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_44 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6987006969108:ℝ):ℂ) + ((0.7154141011585:ℝ):ℂ) * I)‖ ≤ 0.00000013157 := by
  have hl := lg_44
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.450562977514672435 93.450563039252221825 0.7972166 0.00000003156 0.6987006969108 0.7154141011585 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_45 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.970800829628:ℝ):ℂ) + ((0.2398869508616:ℝ):ℂ) * I)‖ ≤ 0.00000014851 := by
  have hl := lg_45
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.005530159200611215 94.0055302085906853 0.2422494 0.0000000485 0.970800829628 0.2398869508616 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_46 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9551827782686:ℝ):ℂ) + (((-0.2960166551041):ℝ):ℂ) * I)‖ ≤ 0.00000015351 := by
  have hl := lg_46
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.54829925420139337 94.548299315938967455 (-0.3005197) 0.0000000535 0.9551827782686 (-0.2960166551041) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_47 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6736828257031:ℝ):ℂ) + (((-0.7390206021166):ℝ):ℂ) * I)‖ ≤ 0.00000014619 := by
  have hl := lg_47
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.079394992133074655 95.079395053870673435 (-0.8316154) 0.00000004618 0.6736828257031 (-0.7390206021166) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_48 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.217514160236:ℝ):ℂ) + (((-0.9760571653837):ℝ):ℂ) * I)‖ ≤ 0.00000017544 := by
  have hl := lg_48
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.59930893227360998 95.599308994011134675 (-1.3515294) 0.00000007543 0.217514160236 (-0.9760571653837) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_49 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2858816719047):ℝ):ℂ) + (((-0.9582649266604):ℝ):ℂ) * I)‖ ≤ 0.00000017154 := by
  have hl := lg_49
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.10850223616449258 96.10850228555459136 (-1.8607227) 0.00000007153 (-0.2858816719047) (-0.9582649266604) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p695_50 : ‖exp (-((((((24695:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.709530818785):ℝ):ℂ) + (((-0.7046744050758):ℝ):ℂ) * I)‖ ≤ 0.00000014101 := by
  have hl := lg_50
  refine (ecis_approx ((((24695:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.60740808695128251 96.6074081486888319 (-2.3596285) 0.000000041 (-0.709530818785) (-0.7046744050758) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_2 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1230541832493):ℝ):ℂ) + ((0.9923999536398:ℝ):ℂ) * I)‖ ≤ 0.00000010913 := by
  have hl := lg_2
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.155392712425 17.1553927248 1.6941632 0.00000000912 (-0.1230541832493) 0.9923999536398 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_3 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4680797930642):ℝ):ℂ) + (((-0.8836862041018):ℝ):ℂ) * I)‖ ≤ 0.00000012177 := by
  have hl := lg_3
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.190654138102059 27.19065415047708375 (-2.0579129) 0.00000002176 (-0.4680797930642) (-0.8836862041018) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_4 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9697153341112):ℝ):ℂ) + (((-0.2442379383291):ℝ):ℂ) * I)‖ ≤ 0.00000011372 := by
  have hl := lg_4
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.31078542485 34.3107854496 (-2.8948589) 0.00000001371 (-0.9697153341112) (-0.2442379383291) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_5 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5343006393372):ℝ):ℂ) + (((-0.8452945207417):ℝ):ℂ) * I)‖ ≤ 0.00000012322 := by
  have hl := lg_5
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.83358831987667275 39.8335883446266975 (-2.1344765) 0.00000002321 (-0.5343006393372) (-0.8452945207417) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_6 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9345693246168:ℝ):ℂ) + (((-0.3557810808422):ℝ):ℂ) * I)‖ ≤ 0.00000012503 := by
  have hl := lg_6
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.346046850527059 44.34604687527708375 (-0.3637497) 0.00000002502 0.9345693246168 (-0.3557810808422) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_7 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5084725453474):ℝ):ℂ) + ((0.8610782023843:ℝ):ℂ) * I)‖ ≤ 0.00000014358 := by
  have hl := lg_7
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.1612761762516945 48.161276201001744 2.1042063 0.00000004357 (-0.5084725453474) 0.8610782023843 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_8 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3617092472466:ℝ):ℂ) + (((-0.9322909526839):ℝ):ℂ) * I)‖ ≤ 0.00000012018 := by
  have hl := lg_8
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.466178137275 51.4661781744 (-1.2006957) 0.00000002017 0.3617092472466 (-0.9322909526839) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_9 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5618026087099):ℝ):ℂ) + ((0.8272713151303:ℝ):ℂ) * I)‖ ≤ 0.00000013635 := by
  have hl := lg_9
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.381308276204118 54.3813083009541675 2.1673595 0.00000003634 (-0.5618026087099) 0.8272713151303 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_10 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9046181719839:ℝ):ℂ) + (((-0.426222902853):ℝ):ℂ) * I)‖ ≤ 0.00000013233 := by
  have hl := lg_10
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.98898103230167275 56.9889810694266975 (-0.4403133) 0.00000003232 0.9046181719839 (-0.426222902853) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_11 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9419675446628):ℝ):ℂ) + (((-0.3357039538317):ℝ):ℂ) * I)‖ ≤ 0.00000015498 := by
  have hl := lg_11
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.34790798245869175 59.34790801958374125 (-2.7992402) 0.00000005497 (-0.9419675446628) (-0.3357039538317) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_12 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2380744632033:ℝ):ℂ) + ((0.9712469047418:ℝ):ℂ) * I)‖ ≤ 0.0000001283 := by
  have hl := lg_12
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.501439562952059 61.50143960007708375 1.3304135 0.00000002829 0.2380744632033 0.9712469047418 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_13 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7956941962978:ℝ):ℂ) + (((-0.6056985603236):ℝ):ℂ) * I)‖ ≤ 0.00000014322 := by
  have hl := lg_13
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.482496577872075 63.4824966149971245 (-0.6506435) 0.00000004321 0.7956941962978 (-0.6056985603236) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_14 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7919642899652):ℝ):ℂ) + (((-0.6105674109987):ℝ):ℂ) * I)‖ ≤ 0.00000015402 := by
  have hl := lg_14
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.3166688886766945 65.316668925801744 (-2.4848158) 0.00000005401 (-0.7919642899652) (-0.6105674109987) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_15 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4968797674628):ℝ):ℂ) + ((0.86781939174:ℝ):ℂ) * I)‖ ≤ 0.00000012101 := by
  have hl := lg_15
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.02424245797873175 67.02424249510378125 2.0907959 0.000000021 (-0.4968797674628) 0.86781939174 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_16 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.880695662229:ℝ):ℂ) + ((0.4736825419318:ℝ):ℂ) * I)‖ ≤ 0.00000012929 := by
  have hl := lg_16
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.6215708497 68.6215708992 0.4934675 0.00000002928 0.880695662229 0.4736825419318 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_17 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5344056660914:ℝ):ℂ) + (((-0.8452281254487):ℝ):ℂ) * I)‖ ≤ 0.00000013933 := by
  have hl := lg_17
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.1220302396567415 70.12203028915676625 (-1.0069919) 0.00000003932 0.5344056660914 (-0.8452281254487) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_18 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7518518488867):ℝ):ℂ) + (((-0.6593320842272):ℝ):ℂ) * I)‖ ≤ 0.00000014679 := by
  have hl := lg_18
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.536700988629118 71.5367010257541675 (-2.4216626) 0.00000004678 (-0.7518518488867) (-0.6593320842272) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_19 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8149034958451):ℝ):ℂ) + ((0.579596663555:ℝ):ℂ) * I)‖ ≤ 0.00000016605 := by
  have hl := lg_19
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.87486471506842425 72.8748647521934985 2.523359 0.00000006604 (-0.8149034958451) 0.579596663555 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_20 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3116665387258:ℝ):ℂ) + ((0.9501915431315:ℝ):ℂ) * I)‖ ≤ 0.00000014144 := by
  have hl := lg_20
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.14437374472667275 74.1443737942266975 1.2538499 0.00000004143 0.3116665387258 0.9501915431315 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_21 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9989286519107:ℝ):ℂ) + ((0.0462768667037:ℝ):ℂ) * I)‖ ≤ 0.00000016534 := by
  have hl := lg_21
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.3519303143537535 75.35193035147882775 0.0462934 0.00000006533 0.9989286519107 0.0462768667037 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_22 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4490656351783:ℝ):ℂ) + (((-0.8934987718525):ℝ):ℂ) * I)‖ ≤ 0.00000015824 := by
  have hl := lg_22
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.50330069488369175 76.50330074438374125 (-1.105077) 0.00000005823 0.4490656351783 (-0.8934987718525) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_23 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5927441978379):ℝ):ℂ) + (((-0.8053907845996):ℝ):ℂ) * I)‖ ≤ 0.00000016766 := by
  have hl := lg_23
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.6034818185118085 77.60348186801188275 (-2.2052582) 0.00000006765 (-0.5927441978379) (-0.8053907845996) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_24 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.993161441661):ℝ):ℂ) + ((0.1167490914376:ℝ):ℂ) * I)‖ ≤ 0.00000013156 := by
  have hl := lg_24
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.656832275377059 78.65683232487708375 3.0245767 0.00000003155 (-0.993161441661) 0.1167490914376 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_25 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4290456471219):ℝ):ℂ) + ((0.9032828088045:ℝ):ℂ) * I)‖ ≤ 0.0000001536 := by
  have hl := lg_25
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.6671766397533455 79.667176689253395 2.0142323 0.00000005359 (-0.4290456471219) 0.9032828088045 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_26 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5031817237434:ℝ):ℂ) + ((0.8641806251534:ℝ):ℂ) * I)‖ ≤ 0.00000014648 := by
  have hl := lg_26
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.637889290297075 80.6378893397971245 1.0435197 0.00000004647 0.5031817237434 0.8641806251534 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_27 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.994016697065:ℝ):ℂ) + ((0.1092282287508:ℝ):ℂ) * I)‖ ≤ 0.00000015811 := by
  have hl := lg_27
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.571962414306177 81.57196245143125125 0.1094466 0.0000000581 0.994016697065 0.1092282287508 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_28 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7033815892604:ℝ):ℂ) + (((-0.710812450573):ℝ):ℂ) * I)‖ ≤ 0.00000015728 := by
  have hl := lg_28
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.4720616011016945 82.472061650601744 (-0.7906526) 0.00000005727 0.7033815892604 (-0.710812450573) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_29 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0882515145294):ℝ):ℂ) + (((-0.9960982231602):ℝ):ℂ) * I)‖ ≤ 0.00000012692 := by
  have hl := lg_29
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.340571766430627 83.34057181593070125 (-1.6591628) 0.00000002691 (-0.0882515145294) (-0.9960982231602) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_30 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8000807858589):ℝ):ℂ) + (((-0.5998922703703):ℝ):ℂ) * I)‖ ≤ 0.00000012658 := by
  have hl := lg_30
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.17963517040373175 84.17963521990378125 (-2.4982262) 0.00000002657 (-0.8000807858589) (-0.5998922703703) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_31 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.985890769341):ℝ):ℂ) + ((0.1673899356619:ℝ):ℂ) * I)‖ ≤ 0.00000013427 := by
  have hl := lg_31
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 84.99118328527273425 84.9911833347728085 2.973411 0.00000003426 (-0.985890769341) 0.1673899356619 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_32 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5784558180593):ℝ):ℂ) + ((0.8157137160444:ℝ):ℂ) * I)‖ ≤ 0.0000001384 := by
  have hl := lg_32
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.776963562125 85.776963624 2.1876307 0.00000003839 (-0.5784558180593) 0.8157137160444 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_33 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1442590277637:ℝ):ℂ) + ((0.9895399602384:ℝ):ℂ) * I)‖ ≤ 0.00000016956 := by
  have hl := lg_33
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.53856212056075075 86.538562170060825 1.4260322 0.00000006955 0.1442590277637 0.9895399602384 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_34 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7730434997459:ℝ):ℂ) + ((0.6343530148904:ℝ):ℂ) * I)‖ ≤ 0.00000014845 := by
  have hl := lg_34
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.2774229520817415 87.27742301395676625 0.6871713 0.00000004844 0.7730434997459 0.6343530148904 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_35 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9995418924773:ℝ):ℂ) + (((-0.0302655775234):ℝ):ℂ) * I)‖ ≤ 0.00000014513 := by
  have hl := lg_35
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.99486449612836725 87.9948645456284415 (-0.0302702) 0.00000004512 0.9995418924773 (-0.0302655775234) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_36 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7468396450296:ℝ):ℂ) + (((-0.6650041688682):ℝ):ℂ) * I)‖ ≤ 0.00000015005 := by
  have hl := lg_36
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.692093701054118 88.6920937505541675 (-0.7274994) 0.00000005004 0.7468396450296 (-0.6650041688682) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_37 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1644223148644:ℝ):ℂ) + (((-0.9863900356221):ℝ):ℂ) * I)‖ ≤ 0.00000016121 := by
  have hl := lg_37
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.3702183122099395 89.37021836171001375 (-1.405624) 0.0000000612 0.1644223148644 (-0.9863900356221) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_38 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4749144996479):ℝ):ℂ) + (((-0.8800319414765):ℝ):ℂ) * I)‖ ≤ 0.00000017304 := by
  have hl := lg_38
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.03025742749342425 90.0302574769934985 (-2.0656632) 0.00000007303 (-0.4749144996479) (-0.8800319414765) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_39 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9076958363115):ℝ):ℂ) + (((-0.4196287271114):ℝ):ℂ) * I)‖ ≤ 0.00000016497 := by
  have hl := lg_39
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.673150715974134 90.67315076547420825 (-2.7085564) 0.00000006496 (-0.9076958363115) (-0.4196287271114) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_40 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9813219145845):ℝ):ℂ) + ((0.1923728141481:ℝ):ℂ) * I)‖ ≤ 0.00000015056 := by
  have hl := lg_40
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.29976645715167275 91.2997665190266975 2.9480131 0.00000005055 (-0.9813219145845) 0.1923728141481 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_41 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6933118487881):ℝ):ℂ) + ((0.7206376900408:ℝ):ℂ) * I)‖ ≤ 0.00000017296 := by
  have hl := lg_41
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.910908618763355 91.9109086806384045 2.336871 0.00000007295 (-0.6933118487881) 0.7206376900408 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_42 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1688475097565):ℝ):ℂ) + ((0.98564218581:ℝ):ℂ) * I)‖ ≤ 0.0000001686 := by
  have hl := lg_42
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.5073230267787535 92.50732307627882775 1.7404566 0.00000006859 (-0.1688475097565) 0.98564218581 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_43 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4011020771435:ℝ):ℂ) + ((0.9160333638635:ℝ):ℂ) * I)‖ ≤ 0.00000017003 := by
  have hl := lg_43
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.089702837681055 93.089702887181154 1.1580767 0.00000007002 0.4011020771435 0.9160333638635 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_44 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8314487348018:ℝ):ℂ) + ((0.5556014771367:ℝ):ℂ) * I)‖ ≤ 0.0000001615 := by
  have hl := lg_44
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.65869340730869175 93.65869346918374125 0.5890862 0.00000006149 0.8314487348018 0.5556014771367 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_45 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9994594028701:ℝ):ℂ) + ((0.0328770743013:ℝ):ℂ) * I)‖ ≤ 0.0000001379 := by
  have hl := lg_45
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.21489659608079075 94.214896645580865 0.032883 0.00000003789 0.9994594028701 0.0328770743013 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_46 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.872209430446:ℝ):ℂ) + (((-0.4891326092595):ℝ):ℂ) * I)‖ ≤ 0.00000017677 := by
  have hl := lg_46
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.7588745309368085 94.75887459281188275 (-0.511095) 0.00000007676 0.872209430446 (-0.4891326092595) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_47 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5033080615728:ℝ):ℂ) + (((-0.86410705075):ℝ):ℂ) * I)‖ ≤ 0.00000016435 := by
  have hl := lg_47
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.29115311015564275 95.29115317203074175 (-1.0433735) 0.00000006434 0.5033080615728 (-0.86410705075) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_48 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0063508841016:ℝ):ℂ) + (((-0.9999798329321):ℝ):ℂ) * I)‖ ≤ 0.000000142 := by
  have hl := lg_48
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.812224987802059 95.81222504967708375 (-1.5644454) 0.00000004199 0.0063508841016 (-0.9999798329321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_49 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4829114225355):ℝ):ℂ) + (((-0.8756692057959):ℝ):ℂ) * I)‖ ≤ 0.00000015521 := by
  have hl := lg_49
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.322552352503389 96.322552402003488 (-2.0747728) 0.0000000552 (-0.4829114225355) (-0.8756692057959) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_50 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8436219520287):ℝ):ℂ) + (((-0.5369376146121):ℝ):ℂ) * I)‖ ≤ 0.00000015553 := by
  have hl := lg_50
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.8225693521783455 96.822569414053395 (-2.5747898) 0.00000005552 (-0.8436219520287) (-0.5369376146121) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_51 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9970609271348):ℝ):ℂ) + (((-0.0766127082271):ℝ):ℂ) * I)‖ ≤ 0.00000013196 := by
  have hl := lg_51
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.3126843777588005 97.31268443963385 (-3.0649048) 0.00000003195 (-0.9970609271348) (-0.0766127082271) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_52 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9195314283352):ℝ):ℂ) + ((0.3930164782317:ℝ):ℂ) * I)‖ ≤ 0.00000014974 := by
  have hl := lg_52
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.793282002722075 97.7932820645971245 2.7376829 0.00000004973 (-0.9195314283352) 0.3930164782317 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_53 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6407262181143):ℝ):ℂ) + ((0.7677694402652:ℝ):ℂ) * I)‖ ≤ 0.00000017526 := by
  have hl := lg_53
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.2647248282467515 98.26472489012182575 2.2662401 0.00000007525 (-0.6407262181143) 0.7677694402652 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_54 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2307160019419):ℝ):ℂ) + ((0.9730211336075:ℝ):ℂ) * I)‖ ≤ 0.00000016137 := by
  have hl := lg_54
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.727355126731177 98.72735517623125125 1.8036098 0.00000006136 (-0.2307160019419) 0.9730211336075 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_55 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2195251555388:ℝ):ℂ) + ((0.9756068399133:ℝ):ℂ) * I)‖ ≤ 0.00000014935 := by
  have hl := lg_55
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.1814963023353645 99.18149636421043875 1.3494686 0.00000004934 0.2195251555388 0.9756068399133 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_56 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6188561960165:ℝ):ℂ) + ((0.7855043021219:ℝ):ℂ) * I)‖ ≤ 0.00000016054 := by
  have hl := lg_56
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.6274543135266945 99.627454375401744 0.9035106 0.00000006053 0.6188561960165 0.7855043021219 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_57 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8936214801462:ℝ):ℂ) + ((0.4488214012514:ℝ):ℂ) * I)‖ ≤ 0.00000016172 := by
  have hl := lg_57
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.06551885317048325 100.06551890267058225 0.465446 0.00000006171 0.8936214801462 0.4488214012514 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_58 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9993875485263:ℝ):ℂ) + ((0.0349932543594:ℝ):ℂ) * I)‖ ≤ 0.00000013603 := by
  have hl := lg_58
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.495964478855627 100.49596454073070125 0.0350004 0.00000003602 0.9993875485263 0.0349932543594 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_59 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9256347431518:ℝ):ℂ) + (((-0.3784181843812):ℝ):ℂ) * I)‖ ≤ 0.00000015152 := by
  have hl := lg_59
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.919051704498302 100.919051766373401 (-0.3880868) 0.00000005151 0.9256347431518 (-0.3784181843812) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p75_60 : ‖exp (-((((((24750:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6937863489704:ℝ):ℂ) + (((-0.7201808814335):ℝ):ℂ) * I)‖ ≤ 0.00000013206 := by
  have hl := lg_60
  refine (ecis_approx ((((24750:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.33502788282873175 101.33502794470378125 (-0.804063) 0.00000003205 0.6937863489704 (-0.7201808814335) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_2 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.085140573382):ℝ):ℂ) + ((0.9963689491166:ℝ):ℂ) * I)‖ ≤ 0.00000011421 := by
  have hl := lg_2
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.1935158073415 17.193515819744 1.6560401 0.0000000142 (-0.085140573382) 0.9963689491166 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_3 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5205886724398):ℝ):ℂ) + (((-0.8538076095469):ℝ):ℂ) * I)‖ ≤ 0.00000011477 := by
  have hl := lg_3
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.25107781396450802 27.251077826367032825 (-2.1183366) 0.00000001476 (-0.5205886724398) (-0.8538076095469) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_4 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9855021641561):ℝ):ℂ) + (((-0.1696628541534):ℝ):ℂ) * I)‖ ≤ 0.00000012123 := by
  have hl := lg_4
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.387031614683 34.387031639488 (-2.9711051) 0.00000002122 (-0.9855021641561) (-0.1696628541534) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_5 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6069357465078):ℝ):ℂ) + (((-0.7947509041193):ℝ):ℂ) * I)‖ ≤ 0.00000013806 := by
  have hl := lg_5
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.922107405031954245 39.92210742983697905 (-2.2229956) 0.00000003805 (-0.6069357465078) (-0.7947509041193) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_6 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8950306087439:ℝ):ℂ) + (((-0.4460047190462):ℝ):ℂ) * I)‖ ≤ 0.00000012897 := by
  have hl := lg_6
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.44459362130600802 44.444593646111032825 (-0.4622965) 0.00000002896 0.8950306087439 (-0.4460047190462) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_7 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4135820590807):ℝ):ℂ) + ((0.9104668475035:ℝ):ℂ) * I)‖ ≤ 0.00000012303 := by
  have hl := lg_7
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.26830123442114271 48.26830125922619232 1.9971812 0.00000002302 (-0.4135820590807) 0.9104668475035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_8 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2529530192125:ℝ):ℂ) + (((-0.9674785631068):ℝ):ℂ) * I)‖ ≤ 0.00000013543 := by
  have hl := lg_8
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.5805474220245 51.580547459232 (-1.315065) 0.00000003542 0.2529530192125 (-0.9674785631068) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_9 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4579748618718):ℝ):ℂ) + ((0.8889651432361:ℝ):ℂ) * I)‖ ≤ 0.0000001367 := by
  have hl := lg_9
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.50215562792901604 54.50215565273406565 2.0465121 0.00000003669 (-0.4579748618718) 0.8889651432361 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_10 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8435399806179:ℝ):ℂ) + (((-0.5370663842573):ℝ):ℂ) * I)‖ ≤ 0.00000015226 := by
  have hl := lg_10
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.115623212373454245 57.11562324958097905 (-0.5669555) 0.00000005225 0.8435399806179 (-0.5370663842573) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_11 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9779332161745):ℝ):ℂ) + (((-0.2089177455142):ℝ):ℂ) * I)‖ ≤ 0.00000014221 := by
  have hl := lg_11
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.479792222419711065 59.479792259627260675 (-2.9311245) 0.0000000422 (-0.9779332161745) (-0.2089177455142) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_12 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3681818339943:ℝ):ℂ) + ((0.9297538045723:ℝ):ℂ) * I)‖ ≤ 0.00000014316 := by
  have hl := lg_12
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.63810942864750802 61.638109465855032825 1.1937436 0.00000004315 0.3681818339943 0.9297538045723 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_13 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7026255272121:ℝ):ℂ) + (((-0.7115598137261):ℝ):ℂ) * I)‖ ≤ 0.00000015792 := by
  have hl := lg_13
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.6235687924895685 63.62356882969711811 (-0.7917157) 0.00000005791 0.7026255272121 (-0.7115598137261) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_14 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8719482788653):ℝ):ℂ) + (((-0.4895979972329):ℝ):ℂ) * I)‖ ≤ 0.00000013005 := by
  have hl := lg_14
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.46181704176264271 65.46181707897019232 (-2.629964) 0.00000003004 (-0.8719482788653) (-0.4895979972329) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_15 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3626004884184):ℝ):ℂ) + ((0.9319446795793:ℝ):ℂ) * I)‖ ≤ 0.00000015999 := by
  have hl := lg_15
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.173185218996462265 67.173185256204011875 1.9418531 0.00000005998 (-0.3626004884184) 0.9319446795793 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_16 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9424290341214:ℝ):ℂ) + ((0.3344062135264:ℝ):ℂ) * I)‖ ≤ 0.00000014962 := by
  have hl := lg_16
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.774063229366 68.774063278976 0.3409751 0.00000004961 0.9424290341214 0.3344062135264 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_17 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3967538453089:ℝ):ℂ) + (((-0.9179250439075):ℝ):ℂ) * I)‖ ≤ 0.00000014417 := by
  have hl := lg_17
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.27785697352264537 70.277857023132670175 (-1.1628186) 0.00000004416 0.3967538453089 (-0.9179250439075) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_18 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.846745019399):ℝ):ℂ) + (((-0.5319989398967):ℝ):ℂ) * I)‖ ≤ 0.00000014372 := by
  have hl := lg_18
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.69567143527051604 71.69567147247806565 (-2.5806331) 0.00000004371 (-0.846745019399) (-0.5319989398967) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_19 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7107884459962):ℝ):ℂ) + ((0.703405846587:ℝ):ℂ) * I)‖ ≤ 0.00000012729 := by
  have hl := lg_19
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.036808858879687415 73.03680889608726183 2.3614148 0.00000002728 (-0.7107884459962) 0.703405846587 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_20 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.463296791268:ℝ):ℂ) + ((0.8862031839261:ℝ):ℂ) * I)‖ ≤ 0.00000016646 := by
  have hl := lg_20
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.309139019714954245 74.30913906932497905 1.0890846 0.00000006645 0.463296791268 0.8862031839261 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_21 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9926696577259:ℝ):ℂ) + (((-0.1208592182267):ℝ):ℂ) * I)‖ ≤ 0.00000013778 := by
  have hl := lg_21
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.51937904838565073 75.519379085593225145 (-0.1211554) 0.00000003777 0.9926696577259 (-0.1208592182267) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_22 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2914209494694:ℝ):ℂ) + (((-0.9565949143762):ℝ):ℂ) * I)‖ ≤ 0.00000015641 := by
  have hl := lg_22
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.673308029761211065 76.673308079371260675 (-1.2750844) 0.0000000564 0.2914209494694 (-0.9565949143762) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_23 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7221559182103):ℝ):ℂ) + (((-0.6917303157778):ℝ):ℂ) * I)‖ ≤ 0.0000001638 := by
  have hl := lg_23
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.77593400033072363 77.775934049940798045 (-2.3777103) 0.00000006379 (-0.7221559182103) (-0.6917303157778) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_24 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9577250335711):ℝ):ℂ) + ((0.2876851748795:ℝ):ℂ) * I)‖ ≤ 0.00000015736 := by
  have hl := lg_24
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.83162523598900802 78.831625285599032825 2.8497837 0.00000005735 (-0.9577250335711) 0.2876851748795 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_25 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2632580887659):ℝ):ℂ) + ((0.9647254421326:ℝ):ℂ) * I)‖ ≤ 0.00000016635 := by
  have hl := lg_25
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.84421481006390849 79.8442148596739581 1.8371942 0.00000006634 (-0.2632580887659) 0.9647254421326 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_26 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6491541635764:ℝ):ℂ) + ((0.7606568687072:ℝ):ℂ) * I)‖ ≤ 0.00000015612 := by
  have hl := lg_26
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.8170845998310685 80.81708464944111811 0.8643244 0.00000005611 0.6491541635764 0.7606568687072 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_27 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9974217292756:ℝ):ℂ) + (((-0.0717627617149):ℝ):ℂ) * I)‖ ≤ 0.00000015146 := by
  have hl := lg_27
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.75323344189352406 81.753233479101098475 (-0.0718245) 0.00000005145 0.9974217292756 (-0.0717627617149) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_28 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5620584184655:ℝ):ℂ) + (((-0.8270975361057):ℝ):ℂ) * I)‖ ≤ 0.00000014425 := by
  have hl := lg_28
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.65533284910414271 82.65533289871419232 (-0.9739239) 0.00000004424 0.5620584184655 (-0.8270975361057) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_29 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2701682477629):ℝ):ℂ) + (((-0.9628131271952):ℝ):ℂ) * I)‖ ≤ 0.00000015633 := by
  have hl := lg_29
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.52577303702269506 83.525773086632769475 (-1.8443641) 0.00000005632 (-0.2701682477629) (-0.9628131271952) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_30 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8976887243397):ℝ):ℂ) + (((-0.4406301783578):ℝ):ℂ) * I)‖ ≤ 0.00000016701 := by
  have hl := lg_30
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.366701026337962265 84.366701075948011875 (-2.6852921) 0.000000067 (-0.8976887243397) (-0.4406301783578) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_31 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.936931625491):ℝ):ℂ) + ((0.3495127021753:ℝ):ℂ) * I)‖ ≤ 0.00000013057 := by
  have hl := lg_31
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.180052581462229215 85.18005263107230363 2.7845417 0.00000003056 (-0.936931625491) 0.3495127021753 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_32 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4134309158864):ℝ):ℂ) + ((0.9105354895806:ℝ):ℂ) * I)‖ ≤ 0.00000016382 := by
  have hl := lg_32
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.9675790367075 85.96757909872 1.9970152 0.00000006381 (-0.4134309158864) 0.9105354895806 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_33 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3307254005621:ℝ):ℂ) + ((0.9437270312029:ℝ):ℂ) * I)‖ ≤ 0.00000016414 := by
  have hl := lg_33
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.730870036384219085 86.7308700859942935 1.2337242 0.00000006413 0.3307254005621 0.9437270312029 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_34 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8808121614851:ℝ):ℂ) + ((0.4734658764684:ℝ):ℂ) * I)‖ ≤ 0.00000014238 := by
  have hl := lg_34
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.47137278086414537 87.471372842876670175 0.4932215 0.00000004237 0.8808121614851 0.4734658764684 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_35 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9746120860029:ℝ):ℂ) + (((-0.2239001603774):ℝ):ℂ) * I)‖ ≤ 0.00000016108 := by
  have hl := lg_35
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.190408639453096955 88.19040868906317137 (-0.2258144) 0.00000006107 0.9746120860029 (-0.2239001603774) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_36 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6021595811771:ℝ):ℂ) + (((-0.7983757503811):ℝ):ℂ) * I)‖ ≤ 0.00000015792 := by
  have hl := lg_36
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.88918724261201604 88.88918729222206565 (-0.924593) 0.00000005791 0.6021595811771 (-0.7983757503811) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_37 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0334219478746):ℝ):ℂ) + (((-0.9994413306443):ℝ):ℂ) * I)‖ ≤ 0.00000014646 := by
  have hl := lg_37
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.56881879734818381 89.568818846958258225 (-1.6042245) 0.00000004645 (-0.0334219478746) (-0.9994413306443) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_38 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6403348028191):ℝ):ℂ) + (((-0.7680959186735):ℝ):ℂ) * I)‖ ≤ 0.00000013431 := by
  have hl := lg_38
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.230324666221187415 90.23032471583126183 (-2.2657304) 0.0000000343 (-0.6403348028191) (-0.7680959186735) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_39 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9733140739303):ℝ):ℂ) + (((-0.2294770428651):ℝ):ℂ) * I)‖ ≤ 0.00000015556 := by
  have hl := lg_39
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.87464660645407652 90.874646656064150935 (-2.9100523) 0.00000005555 (-0.9733140739303) (-0.2294770428651) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_40 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9224306894802):ℝ):ℂ) + ((0.3861626897545:ℝ):ℂ) * I)‖ ≤ 0.00000018065 := by
  have hl := lg_40
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.502654827056454245 91.50265488906897905 2.7451247 0.00000008064 (-0.9224306894802) 0.3861626897545 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_41 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.53273423848):ℝ):ℂ) + ((0.8462825953211:ℝ):ℂ) * I)‖ ≤ 0.00000013669 := by
  have hl := lg_41
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.1151550823606069 92.11515514437315651 2.1326245 0.00000003668 (-0.53273423848) 0.8462825953211 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_42 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.035903908418:ℝ):ℂ) + ((0.9993552468268:ℝ):ℂ) * I)‖ ≤ 0.00000015198 := by
  have hl := lg_42
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.71289485572715073 92.712894905337225145 1.5348847 0.00000005197 0.035903908418 0.9993552468268 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_43 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5806978612389:ℝ):ℂ) + ((0.8141191521838:ℝ):ℂ) * I)‖ ≤ 0.00000016372 := by
  have hl := lg_43
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.2965688439870129 93.29656889359711212 0.9512107 0.00000006371 0.5806978612389 0.8141191521838 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_44 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9283097228342:ℝ):ℂ) + ((0.3718078246777:ℝ):ℂ) * I)‖ ≤ 0.00000017061 := by
  have hl := lg_44
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.866823837102711065 93.866823899115260675 0.3809557 0.0000000706 0.9283097228342 0.3718078246777 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_45 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9844671659983:ℝ):ℂ) + (((-0.1755687872921):ℝ):ℂ) * I)‖ ≤ 0.00000017475 := by
  have hl := lg_45
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.424263032960970285 94.4242630825710447 (-0.1764835) 0.00000007474 0.9844671659983 (-0.1755687872921) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_46 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7507033767674:ℝ):ℂ) + (((-0.6606394176175):ℝ):ℂ) * I)‖ ≤ 0.00000016201 := by
  have hl := lg_46
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.96944980767222363 94.969449869684798045 (-0.7216702) 0.000000062 0.7507033767674 (-0.6606394176175) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_47 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3104483275036:ℝ):ℂ) + (((-0.9505902566039):ℝ):ℂ) * I)‖ ≤ 0.00000017953 := by
  have hl := lg_47
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.502911228178210845 95.502911290190810065 (-1.2551317) 0.00000007952 0.3104483275036 (-0.9505902566039) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_48 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2050993099523):ℝ):ℂ) + (((-0.9787411675495):ℝ):ℂ) * I)‖ ≤ 0.00000016438 := by
  have hl := lg_48
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.02514104333050802 96.025141105343032825 (-1.7773615) 0.00000006437 (-0.2050993099523) (-0.9787411675495) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_49 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6578997554043):ℝ):ℂ) + (((-0.7531055117454):ℝ):ℂ) * I)‖ ≤ 0.00000013887 := by
  have hl := lg_49
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.53660246884228542 96.53660251845238464 (-2.2888229) 0.00000003886 (-0.6578997554043) (-0.7531055117454) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_50 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9388085278066):ℝ):ℂ) + (((-0.344439469197):ℝ):ℂ) * I)‖ ≤ 0.00000017174 := by
  have hl := lg_50
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.03773061740540849 97.0377306794179581 (-2.789951) 0.00000007173 (-0.9388085278066) (-0.344439469197) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_51 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9902769439225):ℝ):ℂ) + ((0.1391099346768:ℝ):ℂ) * I)‖ ≤ 0.00000013464 := by
  have hl := lg_51
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.52893478748715339 97.528934849499703 3.0020301 0.00000003463 (-0.9902769439225) 0.1391099346768 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_52 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8131642426007):ℝ):ℂ) + ((0.5820342897983:ℝ):ℂ) * I)‖ ≤ 0.00000015433 := by
  have hl := lg_52
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.0106004071725685 98.01060046918511811 2.5203645 0.00000005432 (-0.8131642426007) 0.5820342897983 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_53 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4591851184068):ℝ):ℂ) + ((0.8883406030509:ℝ):ℂ) * I)‖ ≤ 0.00000013147 := by
  have hl := lg_53
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.48309088342063317 98.483090945433207585 2.047874 0.00000003146 (-0.4591851184068) 0.8883406030509 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_54 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0134188704586):ℝ):ℂ) + ((0.9999099629044:ℝ):ℂ) * I)‖ ≤ 0.00000016565 := by
  have hl := lg_54
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.94674924923502406 98.946749298845098475 1.5842156 0.00000006564 (-0.0134188704586) 0.9999099629044 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_55 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4275049755018:ℝ):ℂ) + ((0.9040129954382:ℝ):ℂ) * I)‖ ≤ 0.00000017461 := by
  have hl := lg_55
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.40189962745166531 99.401899689464239725 1.1290653 0.0000000746 0.4275049755018 0.9040129954382 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_56 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7762403268444:ℝ):ℂ) + ((0.6304371142156:ℝ):ℂ) * I)‖ ≤ 0.00000015844 := by
  have hl := lg_56
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.84884865644564271 99.84884871845819232 0.6821162 0.00000005843 0.7762403268444 0.6304371142156 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_57 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9706016779197:ℝ):ℂ) + ((0.2406914681067:ℝ):ℂ) * I)‖ ≤ 0.00000014204 := by
  have hl := lg_57
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.287886672844195435 100.287886722454294655 0.2430782 0.00000004203 0.9706016779197 0.2406914681067 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_58 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9823193832642:ℝ):ℂ) + (((-0.187212791399):ℝ):ℂ) * I)‖ ≤ 0.00000017052 := by
  have hl := lg_58
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.71928884436419506 100.719288906376769475 (-0.188324) 0.00000007051 0.9823193832642 (-0.187212791399) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_59 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8182987125916:ℝ):ℂ) + (((-0.5747931949588):ℝ):ℂ) * I)‖ ≤ 0.00000015105 := by
  have hl := lg_59
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.14331626384163156 101.14331632585423078 (-0.6123514) 0.00000005104 0.8182987125916 (-0.5747931949588) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p805_60 : ‖exp (-((((((24805:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5154600462238:ℝ):ℂ) + (((-0.8569136133514):ℝ):ℂ) * I)‖ ≤ 0.00000018083 := by
  have hl := lg_60
  refine (ecis_approx ((((24805:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.560216833679462265 101.560216895692011875 (-1.0292519) 0.00000008082 0.5154600462238 (-0.8569136133514) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_2 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.056794196424):ℝ):ℂ) + ((0.998385906978:ℝ):ℂ) * I)‖ ≤ 0.00000013263 := by
  have hl := lg_2
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.2219348417338 17.2219348541568 1.6276211 0.00000003262 (-0.056794196424) 0.998385906978 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_3 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5585057938852):ℝ):ℂ) + (((-0.8295006197632):ℝ):ℂ) * I)‖ ≤ 0.00000011094 := by
  have hl := lg_3
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.296120917789242744 27.29612093021226759 (-2.1633797) 0.00000001093 (-0.5585057938852) (-0.8295006197632) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_4 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9935488488284):ℝ):ℂ) + (((-0.1134049581798):ℝ):ℂ) * I)‖ ≤ 0.00000015245 := by
  have hl := lg_4
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.4438696834676 34.4438697083136 (-3.0279432) 0.00000005244 (-0.9935488488284) (-0.1134049581798) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_5 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6580199426644):ℝ):ℂ) + (((-0.7530005013532):ℝ):ℂ) * I)‖ ≤ 0.0000001412 := by
  have hl := lg_5
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.988094359420436814 39.98809438426646166 (-2.2889825) 0.00000004119 (-0.6580199426644) (-0.7530005013532) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_6 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8598816163683:ℝ):ℂ) + (((-0.5104934924482):ℝ):ℂ) * I)‖ ≤ 0.00000013413 := by
  have hl := lg_6
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.518055759523042744 44.51805578436906759 (-0.5357586) 0.00000003412 0.8598816163683 (-0.5104934924482) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_7 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3397043846215):ℝ):ℂ) + ((0.9405322594503:ℝ):ℂ) * I)‖ ≤ 0.00000011794 := by
  have hl := lg_7
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.348083550511095012 48.348083575357144704 1.9173989 0.00000001793 (-0.3397043846215) 0.9405322594503 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_8 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1696497207308:ℝ):ℂ) + (((-0.9855044252848):ℝ):ℂ) * I)‖ ≤ 0.00000013225 := by
  have hl := lg_8
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.6658045252014 51.6658045624704 (-1.4003221) 0.00000003224 0.1696497207308 (-0.9855044252848) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_9 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.37614254974):ℝ):ℂ) + ((0.9265618070438:ℝ):ℂ) * I)‖ ≤ 0.00000012905 := by
  have hl := lg_9
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.592241835578485488 54.59224186042453518 1.9564259 0.00000002904 (-0.37614254974) 0.9265618070438 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_10 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7891567409641:ℝ):ℂ) + (((-0.6141918578025):ℝ):ℂ) * I)‖ ≤ 0.00000016348 := by
  have hl := lg_10
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.210029201154236814 57.21002923842326166 (-0.6613615) 0.00000006347 0.7891567409641 (-0.6141918578025) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_11 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9937172788735):ℝ):ℂ) + (((-0.1119194764713):ℝ):ℂ) * I)‖ ≤ 0.00000013606 := by
  have hl := lg_11
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.578105928572470918 59.57810596584152061 (-3.0294382) 0.00000003605 (-0.9937172788735) (-0.1119194764713) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_12 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4608332230429:ℝ):ℂ) + ((0.8874867551349:ℝ):ℂ) * I)‖ ≤ 0.00000016675 := by
  have hl := lg_12
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.739990601256842744 61.73999063852586759 1.0918625 0.00000006674 0.4608332230429 0.8874867551349 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_13 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6240519345643:ℝ):ℂ) + (((-0.7813828658005):ℝ):ℂ) * I)‖ ≤ 0.0000001557 := by
  have hl := lg_13
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.7287317161135182 63.728731753382567892 (-0.8968787) 0.00000005569 0.6240519345643 (-0.7813828658005) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_14 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9197209124849):ℝ):ℂ) + (((-0.3925728505583):ℝ):ℂ) * I)‖ ≤ 0.00000015773 := by
  have hl := lg_14
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.570018392244895012 65.570018429513944704 (-2.7381653) 0.00000005772 (-0.9197209124849) (-0.3925728505583) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_15 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2571064251572):ℝ):ℂ) + ((0.9663830949171:ℝ):ℂ) * I)‖ ≤ 0.00000013552 := by
  have hl := lg_15
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.284215277209679558 67.28421531447872925 1.8308231 0.00000003551 (-0.2571064251572) 0.9663830949171 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_16 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9742786099065:ℝ):ℂ) + ((0.2253468222067:ℝ):ℂ) * I)‖ ≤ 0.00000013767 := by
  have hl := lg_16
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.8877393669352 68.8877394166272 0.227299 0.00000003766 0.9742786099065 0.2253468222067 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_17 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2876918534016:ℝ):ℂ) + (((-0.9577230275431):ℝ):ℂ) * I)‖ ≤ 0.0000001584 := by
  have hl := lg_17
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.394018720586319164 70.39401877027834401 (-1.2789804) 0.00000005839 0.2876918534016 (-0.9577230275431) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_18 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9037035331349):ℝ):ℂ) + (((-0.4281587603666):ℝ):ℂ) * I)‖ ≤ 0.00000013562 := by
  have hl := lg_18
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.814176677312285488 71.81417671458133518 (-2.6991383) 0.00000003561 (-0.9037035331349) (-0.4281587603666) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_19 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6209048371629):ℝ):ℂ) + ((0.7838859503614:ℝ):ℂ) * I)‖ ≤ 0.00000012918 := by
  have hl := lg_19
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.157530856993538138 73.157530894262612676 2.2406928 0.00000002917 (-0.6209048371629) 0.7838859503614 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_20 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5683809720551:ℝ):ℂ) + ((0.8227655015894:ℝ):ℂ) * I)‖ ≤ 0.00000014328 := by
  have hl := lg_20
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.431964042888036814 74.43196409258006166 0.9662596 0.00000004327 0.5683809720551 0.8227655015894 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_21 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9698989591466:ℝ):ℂ) + (((-0.2435077186586):ℝ):ℂ) * I)‖ ≤ 0.00000011943 := by
  have hl := lg_21
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.644204468300337756 75.644204505569412294 (-0.2459808) 0.00000001942 0.9698989591466 (-0.2435077186586) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_22 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1681762025781:ℝ):ℂ) + (((-0.9857569502095):ℝ):ℂ) * I)‖ ≤ 0.00000013386 := by
  have hl := lg_22
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.800040770306270918 76.80004081999832061 (-1.4018171) 0.00000003385 0.1681762025781 (-0.9857569502095) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_23 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8048776525739):ℝ):ℂ) + (((-0.5934407841865):ℝ):ℂ) * I)‖ ≤ 0.00000012669 := by
  have hl := lg_23
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.904489263141187636 77.904489312833262174 (-2.5062656) 0.00000002668 (-0.8048776525739) (-0.5934407841865) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_24 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9122268805356):ℝ):ℂ) + ((0.4096853894107:ℝ):ℂ) * I)‖ ≤ 0.00000015036 := by
  have hl := lg_24
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.961925442990642744 78.96192549268266759 2.7194835 0.00000005035 (-0.9122268805356) 0.4096853894107 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_25 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1340194038943):ℝ):ℂ) + ((0.9909787078335:ℝ):ℂ) * I)‖ ≤ 0.00000017451 := by
  have hl := lg_25
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.976188718840873628 79.97618876853292332 1.7052202 0.0000000745 (-0.1340194038943) 0.9909787078335 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_26 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.744679113019:ℝ):ℂ) + ((0.667422668654:ℝ):ℂ) * I)‖ ≤ 0.0000001355 := by
  have hl := lg_26
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.9506665578473182 80.950666607539367892 0.7307424 0.00000003549 0.744679113019 0.667422668654 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_27 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9786613865545:ℝ):ℂ) + (((-0.2054796594975):ℝ):ℂ) * I)‖ ≤ 0.00000013998 := by
  have hl := lg_27
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.888362753367728232 81.88836279063680277 (-0.2069538) 0.00000003997 0.9786613865545 (-0.2054796594975) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_28 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4441739221029:ℝ):ℂ) + (((-0.8959405822507):ℝ):ℂ) * I)‖ ≤ 0.00000015937 := by
  have hl := lg_28
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.791953233978695012 82.791953283670744704 (-1.1105443) 0.00000005936 0.4441739221029 (-0.8959405822507) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_29 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.400100839116):ℝ):ℂ) + (((-0.9164711225867):ℝ):ℂ) * I)‖ ≤ 0.00000012734 := by
  have hl := lg_29
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.663832166009509432 83.66383221570158397 (-1.9824232) 0.00000002733 (-0.400100839116) (-0.9164711225867) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_30 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9502211387436):ℝ):ℂ) + (((-0.3115762944783):ℝ):ℂ) * I)‖ ≤ 0.00000017441 := by
  have hl := lg_30
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.506150118943479558 84.50615016863552925 (-2.8247412) 0.0000000744 (-0.9502211387436) (-0.3115762944783) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_31 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8786139462725):ℝ):ℂ) + ((0.47753275628:ℝ):ℂ) * I)‖ ≤ 0.00000014373 := by
  have hl := lg_31
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.320846056803489098 85.320846106495563636 2.6437482 0.00000004372 (-0.8786139462725) 0.47753275628 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_32 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2803164622163):ℝ):ℂ) + ((0.9599076419162:ℝ):ℂ) * I)‖ ≤ 0.00000017028 := by
  have hl := lg_32
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.109674208669 86.109674270784 1.8549201 0.00000007027 (-0.2803164622163) 0.9599076419162 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_33 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4621595889405:ℝ):ℂ) + ((0.8867967717298:ℝ):ℂ) * I)‖ ≤ 0.00000015417 := by
  have hl := lg_33
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.874226846361713662 86.8742268960537882 1.0903674 0.00000005416 0.4621595889405 0.8867967717298 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_34 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9398379458558:ℝ):ℂ) + ((0.3416206017346:ℝ):ℂ) * I)‖ ≤ 0.00000013821 := by
  have hl := lg_34
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.615953562320119164 87.61595362443514401 0.3486407 0.0000000382 0.9398379458558 0.3416206017346 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_35 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9317535226075:ℝ):ℂ) + (((-0.3630914115049):ℝ):ℂ) * I)‖ ≤ 0.00000015912 := by
  have hl := lg_35
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.336177909931531826 88.336177959623606364 (-0.3715836) 0.00000005911 0.9317535226075 (-0.3630914115049) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
