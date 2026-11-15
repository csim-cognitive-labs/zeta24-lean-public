/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Base
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
namespace H22

open Complex Set

lemma cs_b1left_v20p767_2 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2545869672177):ℝ):ℂ) + (((-0.9670498829542):ℝ):ℂ) * I)‖ ≤ 0.00000012108 := by
  have hl := lg_2
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.3945874932901 14.3945875036736 (-1.8282169) 0.00000002107 (-0.2545869672177) (-0.9670498829542) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_3 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6794872001918):ℝ):ℂ) + ((0.733687361725:ℝ):ℂ) * I)‖ ≤ 0.00000013536 := by
  have hl := lg_3
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.814881393372341788 22.814881403755862555 2.3178598 0.00000003535 (-0.6794872001918) 0.733687361725 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_4 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8703709486874):ℝ):ℂ) + ((0.4923965998997:ℝ):ℂ) * I)‖ ≤ 0.00000014933 := by
  have hl := lg_4
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.7891749865802 28.7891750073472 2.6267515 0.00000004932 (-0.8703709486874) 0.4923965998997 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_5 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4227469171225):ℝ):ℂ) + (((-0.9062477829267):ℝ):ℂ) * I)‖ ≤ 0.00000011919 := by
  have hl := lg_5
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.423197116722378303 33.42319713748939907 (-2.0072706) 0.00000001918 (-0.4227469171225) (-0.9062477829267) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_6 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8825008628535:ℝ):ℂ) + ((0.4703107771068:ℝ):ℂ) * I)‖ ≤ 0.00000015643 := by
  have hl := lg_6
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.209468886662441788 37.209468907429462555 0.4896429 0.00000005642 0.8825008628535 0.4703107771068 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_7 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9089705629369):ℝ):ℂ) + (((-0.4168603070416):ℝ):ℂ) * I)‖ ≤ 0.00000013234 := by
  have hl := lg_7
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.410716054635108674 40.410716075402150208 (-2.7116042) 0.00000003233 (-0.9089705629369) (-0.4168603070416) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_8 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6977571029002:ℝ):ℂ) + ((0.7163344368047:ℝ):ℂ) * I)‖ ≤ 0.00000016078 := by
  have hl := lg_8
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.1837624798703 43.1837625110208 0.7985347 0.00000006077 0.6977571029002 0.7163344368047 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_9 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0765941826795):ℝ):ℂ) + (((-0.9970623506979):ℝ):ℂ) * I)‖ ≤ 0.00000015727 := by
  have hl := lg_9
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.629762786744683576 45.62976280751172511 (-1.6474656) 0.00000005726 (-0.0765941826795) (-0.9970623506979) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_10 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.76876095228):ℝ):ℂ) + ((0.6395362368238:ℝ):ℂ) * I)‖ ≤ 0.00000014744 := by
  have hl := lg_10
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.817784610012478303 47.81778464116299907 2.4476978 0.00000004743 (-0.76876095228) 0.6395362368238 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_11 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8922956923968:ℝ):ℂ) + ((0.4514514340768:ℝ):ℂ) * I)‖ ≤ 0.00000014344 := by
  have hl := lg_11
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.797091114008874811 49.797091145159416345 0.4683913 0.00000004343 0.8922956923968 0.4514514340768 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_12 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2301408610285:ℝ):ℂ) + (((-0.9731573275093):ℝ):ℂ) * I)‖ ≤ 0.00000015368 := by
  have hl := lg_12
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.604056379952541788 51.604056411103062555 (-1.3385739) 0.00000005367 0.2301408610285 (-0.9731573275093) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_13 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9901079942266):ℝ):ℂ) + (((-0.1403073745766):ℝ):ℂ) * I)‖ ≤ 0.00000016394 := by
  have hl := lg_13
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.2663032902088639 53.266303321359405434 (-3.0008208) 0.00000006393 (-0.9901079942266) (-0.1403073745766) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_14 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1717126452084):ℝ):ℂ) + ((0.9851470791079:ℝ):ℂ) * I)‖ ≤ 0.00000011671 := by
  have hl := lg_14
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.805303547925208674 54.805303579075750208 1.7433642 0.0000000167 (-0.1717126452084) 0.9851470791079 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_15 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9521536640431:ℝ):ℂ) + ((0.3056196983988:ℝ):ℂ) * I)‖ ≤ 0.00000015454 := by
  have hl := lg_15
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.238078510094720091 56.238078541245261625 0.3105892 0.00000005453 0.9521536640431 0.3056196983988 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_16 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5150912685866:ℝ):ℂ) + (((-0.8571353364702):ℝ):ℂ) * I)‖ ≤ 0.00000015009 := by
  have hl := lg_16
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.5783499731604 57.5783500146944 (-1.0296822) 0.00000005008 0.5150912685866 (-0.8571353364702) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_17 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6577874600601):ℝ):ℂ) + (((-0.7532035962275):ℝ):ℂ) * I)‖ ≤ 0.00000017021 := by
  have hl := lg_17
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.837341494422284878 58.837341535956305645 (-2.2886738) 0.0000000702 (-0.6577874600601) (-0.7532035962275) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_18 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.944709146446):ℝ):ℂ) + ((0.3279094820697:ℝ):ℂ) * I)‖ ≤ 0.0000001394 := by
  have hl := lg_18
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.024350280034783576 60.02435031118532511 2.8075028 0.00000003939 (-0.944709146446) 0.3279094820697 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_19 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1136464069021):ℝ):ℂ) + ((0.9935212600633:ℝ):ℂ) * I)‖ ≤ 0.00000012352 := by
  have hl := lg_19
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.147164264154584501 61.147164295305146802 1.6846888 0.00000002351 (-0.1136464069021) 0.9935212600633 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_20 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.814179962345:ℝ):ℂ) + ((0.5806125979652:ℝ):ℂ) * I)‖ ≤ 0.00000016851 := by
  have hl := lg_20
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.212372103302578303 62.21237214483659907 0.6194809 0.0000000685 0.814179962345 0.5806125979652 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_21 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9234790018316:ℝ):ℂ) + (((-0.3836489712955):ℝ):ℂ) * I)‖ ≤ 0.0000001238 := by
  have hl := lg_21
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.225597448007450462 63.225597479158012763 (-0.3937444) 0.00000002379 0.9234790018316 (-0.3836489712955) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_22 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2094092022952:ℝ):ℂ) + (((-0.9778280963411):ℝ):ℂ) * I)‖ ≤ 0.00000016451 := by
  have hl := lg_22
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.191678607298974811 64.191678648833016345 (-1.3598256) 0.0000000645 0.2094092022952 (-0.9778280963411) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_23 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6534695335659):ℝ):ℂ) + (((-0.7569528180038):ℝ):ℂ) * I)‖ ≤ 0.00000013036 := by
  have hl := lg_23
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.114808360607463722 65.114808402141526023 (-2.2829553) 0.00000003035 (-0.6534695335659) (-0.7569528180038) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_24 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.999682543019):ℝ):ℂ) + ((0.0251954868101:ℝ):ℂ) * I)‖ ≤ 0.00000013582 := by
  have hl := lg_24
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 65.998643873242641788 65.998643914776662555 3.1163945 0.00000003581 (-0.999682543019) 0.0251954868101 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_25 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6425700826242):ℝ):ℂ) + ((0.7662269173687:ℝ):ℂ) * I)‖ ≤ 0.00000014555 := by
  have hl := lg_25
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.846394233444756606 66.84639427497879814 2.2686441 0.00000004554 (-0.6425700826242) 0.7662269173687 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_26 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1163843682925:ℝ):ℂ) + ((0.9932042482879:ℝ):ℂ) * I)‖ ≤ 0.00000014607 := by
  have hl := lg_26
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.6608907834989639 67.660890825033005434 1.4541476 0.00000004606 0.1163843682925 0.9932042482879 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_27 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7835768123106:ℝ):ℂ) + ((0.6212949212806:ℝ):ℂ) * I)‖ ≤ 0.00000013231 := by
  have hl := lg_27
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.444644180117025364 68.444644211267587665 0.6703942 0.0000000323 0.7835768123106 0.6212949212806 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_28 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9964021691214:ℝ):ℂ) + (((-0.0847509136829):ℝ):ℂ) * I)‖ ≤ 0.00000013778 := by
  have hl := lg_28
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.199891041215308674 69.199891082749350208 (-0.0848527) 0.00000003777 0.9964021691214 (-0.0847509136829) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_29 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6868908247106:ℝ):ℂ) + (((-0.7267606173482):ℝ):ℂ) * I)‖ ≤ 0.00000014231 := by
  have hl := lg_29
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.928632479735952764 69.928632521270015065 (-0.8135941) 0.0000000423 0.6868908247106 (-0.7267606173482) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_30 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0531436797701:ℝ):ℂ) + (((-0.9985868761907):ℝ):ℂ) * I)‖ ≤ 0.00000016596 := by
  have hl := lg_30
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.632666003384820091 70.632666044918861625 (-1.5176276) 0.00000006595 0.0531436797701 (-0.9985868761907) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_31 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5873475224886):ℝ):ℂ) + (((-0.809334842828):ℝ):ℂ) * I)‖ ≤ 0.00000012504 := by
  have hl := lg_31
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.313612253949853421 71.313612295483915722 (-2.1985739) 0.00000002503 (-0.5873475224886) (-0.809334842828) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_32 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.960028150633):ℝ):ℂ) + (((-0.2799034650713):ℝ):ℂ) * I)‖ ≤ 0.00000013941 := by
  have hl := lg_32
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.9729374664505 71.972937518368 (-2.8578991) 0.0000000394 (-0.960028150633) (-0.2799034650713) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_33 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9375277481244):ℝ):ℂ) + ((0.3479105076348:ℝ):ℂ) * I)‖ ≤ 0.00000016278 := by
  have hl := lg_33
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.611972507381216599 72.6119725489152789 2.7862512 0.00000006277 (-0.9375277481244) 0.3479105076348 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_34 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5609214118944):ℝ):ℂ) + ((0.8278690534554:ℝ):ℂ) * I)‖ ≤ 0.00000015349 := by
  have hl := lg_34
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.231928987712384878 73.231929039629905645 2.1662947 0.00000005348 (-0.5609214118944) 0.8278690534554 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_35 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0064857813229:ℝ):ℂ) + ((0.999978967099:ℝ):ℂ) * I)‖ ≤ 0.00000012675 := by
  have hl := lg_35
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.833913171357486977 73.833913212891549278 1.5643105 0.00000002674 0.0064857813229 0.999978967099 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_36 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5576154628644:ℝ):ℂ) + ((0.8300993889737:ℝ):ℂ) * I)‖ ≤ 0.00000012872 := by
  have hl := lg_36
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.418937773324883576 74.41893781485892511 0.9792859 0.00000002871 0.5576154628644 0.8300993889737 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_37 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9170046291219:ℝ):ℂ) + ((0.3988765600647:ℝ):ℂ) * I)‖ ≤ 0.00000012568 := by
  have hl := lg_37
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.987932270289447014 74.987932311823509315 0.4102914 0.00000002567 0.9170046291219 0.3988765600647 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_38 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.989717512326:ℝ):ℂ) + (((-0.1430358199729):ℝ):ℂ) * I)‖ ≤ 0.00000012873 := by
  have hl := lg_38
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.541751757444684501 75.541751798978746802 (-0.1435281) 0.00000002872 0.989717512326 (-0.1430358199729) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_39 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7757074566374:ℝ):ℂ) + (((-0.6310926569983):ℝ):ℂ) * I)‖ ≤ 0.00000013898 := by
  have hl := lg_39
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.081184683581205688 76.081184725115267989 (-0.682961) 0.00000003897 0.7757074566374 (-0.6310926569983) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_40 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3542018310385:ℝ):ℂ) + (((-0.935169002314):ℝ):ℂ) * I)‖ ≤ 0.00000016237 := by
  have hl := lg_40
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.606959596592678303 76.60695964851019907 (-1.2087359) 0.00000006236 0.3542018310385 (-0.935169002314) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_41 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1501609565154):ℝ):ℂ) + (((-0.9886615634977):ℝ):ℂ) * I)‖ ≤ 0.00000014803 := by
  have hl := lg_41
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.11975108225691286 77.119751134174454394 (-1.7215274) 0.00000004802 (-0.1501609565154) (-0.9886615634977) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_42 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6061134111515):ℝ):ℂ) + (((-0.7953782325471):ℝ):ℂ) * I)‖ ≤ 0.00000014487 := by
  have hl := lg_42
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.620184941297550462 77.620184982831612763 (-2.2219613) 0.00000004486 (-0.6061134111515) (-0.7953782325471) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_43 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9085594728725):ℝ):ℂ) + (((-0.4177555315335):ℝ):ℂ) * I)‖ ≤ 0.00000013641 := by
  have hl := lg_43
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.10884278101504926 78.108842822549132328 (-2.7106191) 0.0000000364 (-0.9085594728725) (-0.4177555315335) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_44 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9989214038681):ℝ):ℂ) + ((0.0464330519532:ℝ):ℂ) * I)‖ ≤ 0.00000015919 := by
  have hl := lg_44
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.586266100589074811 78.586266152506616345 3.0951429 0.00000005918 (-0.9989214038681) 0.0464330519532 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_45 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8712055866166):ℝ):ℂ) + ((0.4909183493812:ℝ):ℂ) * I)‖ ≤ 0.00000015168 := by
  have hl := lg_45
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.052959903467061879 79.05295994500112418 2.6284491 0.00000005167 (-0.8712055866166) 0.4909183493812 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_46 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5656463014211):ℝ):ℂ) + ((0.8246479622718:ℝ):ℂ) * I)‖ ≤ 0.00000013945 := by
  have hl := lg_46
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.509395853897563722 79.509395905815126023 2.1720131 0.00000003944 (-0.5656463014211) 0.8246479622718 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_47 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1539822868729):ℝ):ℂ) + ((0.9880736082543:ℝ):ℂ) * I)‖ ≤ 0.00000017563 := by
  have hl := lg_47
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.956015217721302343 79.956015269638885411 1.7253937 0.00000007562 (-0.1539822868729) 0.9880736082543 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_48 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2788714397296:ℝ):ℂ) + ((0.9603284438686:ℝ):ℂ) * I)‖ ≤ 0.00000012682 := by
  have hl := lg_48
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.393231366532741788 80.393231418450262555 1.2881776 0.00000002681 0.2788714397296 0.9603284438686 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_49 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6524549741532:ℝ):ℂ) + ((0.7578274913876:ℝ):ℂ) * I)‖ ≤ 0.00000015748 := by
  have hl := lg_49
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.821432109270217348 80.821432150804300416 0.8599769 0.00000005747 0.6524549741532 0.7578274913876 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p767_50 : ‖exp (-((((((20767:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9045696193275:ℝ):ℂ) + ((0.4263259360978:ℝ):ℂ) * I)‖ ≤ 0.00000016661 := by
  have hl := lg_50
  refine (ecis_approx ((((20767:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.240981726734856606 81.24098177865239814 0.4404272 0.0000000666 0.9045696193275 0.4263259360978 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_2 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2819630583187):ℝ):ℂ) + (((-0.9594252621971):ℝ):ℂ) * I)‖ ≤ 0.00000012374 := by
  have hl := lg_2
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.4230065276824 14.4230065380864 (-1.8566359) 0.00000002373 (-0.2819630583187) (-0.9594252621971) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_3 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6457616380279):ℝ):ℂ) + ((0.763539067:ℝ):ℂ) * I)‖ ≤ 0.00000013154 := by
  have hl := lg_3
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.859924497197076512 22.85992450760109732 2.2728167 0.00000003153 (-0.6457616380279) 0.763539067 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_4 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8409936635865):ℝ):ℂ) + ((0.541044968315:ℝ):ℂ) * I)‖ ≤ 0.00000014029 := by
  have hl := lg_4
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.8460130553648 28.8460130761728 2.5699135 0.00000004028 (-0.8409936635865) 0.541044968315 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_5 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4815839670811):ℝ):ℂ) + (((-0.8763999558677):ℝ):ℂ) * I)‖ ≤ 0.00000015604 := by
  have hl := lg_5
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.489184071110860872 33.48918409191888168 (-2.0732575) 0.00000005603 (-0.4815839670811) (-0.8763999558677) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_6 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9146395959674:ℝ):ℂ) + ((0.4042702184042:ℝ):ℂ) * I)‖ ≤ 0.00000011821 := by
  have hl := lg_6
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.282931024879476512 37.28293104568749732 0.4161808 0.0000000182 0.9146395959674 0.4042702184042 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_7 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.939302003212):ℝ):ℂ) + (((-0.3430914551313):ℝ):ℂ) * I)‖ ≤ 0.00000014847 := by
  have hl := lg_7
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.490498370725060976 40.490498391533102592 (-2.7913865) 0.00000004846 (-0.939302003212) (-0.3430914551313) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_8 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7562213560389:ℝ):ℂ) + ((0.6543158722442:ℝ):ℂ) * I)‖ ≤ 0.00000016402 := by
  have hl := lg_8
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.2690195830472 43.2690196142592 0.7132776 0.00000006401 0.7562213560389 0.6543158722442 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_9 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1659838066189):ℝ):ℂ) + (((-0.9861284784143):ℝ):ℂ) * I)‖ ≤ 0.00000015588 := by
  have hl := lg_9
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.719848994394153024 45.71984901520219464 (-1.7375519) 0.00000005587 (-0.1659838066189) (-0.9861284784143) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_10 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7050512932457):ℝ):ℂ) + ((0.709156311308:ℝ):ℂ) * I)‖ ≤ 0.00000015866 := by
  have hl := lg_10
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.912190598793260872 47.91219063000528168 2.3532918 0.00000005865 (-0.7050512932457) 0.709156311308 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_11 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9322992814414:ℝ):ℂ) + ((0.3616877794781:ℝ):ℂ) * I)‖ ≤ 0.00000013729 := by
  have hl := lg_11
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.895404820161634664 49.89540485137367628 0.3700776 0.00000003728 0.9322992814414 0.3616877794781 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_12 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.129972482553:ℝ):ℂ) + (((-0.991517601346):ℝ):ℂ) * I)‖ ≤ 0.00000012635 := by
  have hl := lg_12
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.705937552561876512 51.70593758377389732 (-1.4404551) 0.00000002634 0.129972482553 (-0.991517601346) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_13 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993660714694):ℝ):ℂ) + (((-0.035601328512):ℝ):ℂ) * I)‖ ≤ 0.00000014362 := by
  have hl := lg_13
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.3714662138328136 53.371466245044855216 (-3.1059838) 0.00000004361 (-0.9993660714694) (-0.035601328512) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_14 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0643221366945):ℝ):ℂ) + ((0.9979291872326:ℝ):ℂ) * I)‖ ≤ 0.00000016502 := by
  have hl := lg_14
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.913504898407460976 54.913504929619502592 1.6351629 0.00000006501 (-0.0643221366945) 0.9979291872326 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_15 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9801540560637:ℝ):ℂ) + ((0.1982372981604:ℝ):ℂ) * I)‖ ≤ 0.00000013492 := by
  have hl := lg_15
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.349108568307937384 56.349108599519979 0.1995592 0.00000003491 0.9801540560637 0.1982372981604 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_16 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4145405999705:ℝ):ℂ) + (((-0.9100308186957):ℝ):ℂ) * I)‖ ≤ 0.0000001539 := by
  have hl := lg_16
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.6920261107296 57.6920261523456 (-1.1433584) 0.00000005389 0.4145405999705 (-0.9100308186957) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_17 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7406512841419):ℝ):ℂ) + (((-0.6718896302722):ℝ):ℂ) * I)‖ ≤ 0.00000012315 := by
  have hl := lg_17
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.953503241485958672 58.95350328310197948 (-2.4048355) 0.00000002314 (-0.7406512841419) (-0.6718896302722) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_18 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8993152690447):ℝ):ℂ) + ((0.437300865249:ℝ):ℂ) * I)‖ ≤ 0.00000014973 := by
  have hl := lg_18
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.142855522076553024 60.14285555328859464 2.6889975 0.00000004972 (-0.8993152690447) 0.437300865249 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_19 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.006829473704:ℝ):ℂ) + ((0.9999766788724:ℝ):ℂ) * I)‖ ≤ 0.0000001217 := by
  have hl := lg_19
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.267886262268435224 61.267886293480497648 1.5639668 0.00000002169 0.006829473704 0.9999766788724 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_20 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8791808988454:ℝ):ℂ) + ((0.4764881395223:ℝ):ℂ) * I)‖ ≤ 0.00000014534 := by
  have hl := lg_20
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.335197126475660872 62.33519716809168168 0.4966559 0.00000004533 0.8791808988454 0.4764881395223 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_21 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8685289298587:ℝ):ℂ) + (((-0.495638475099):ℝ):ℂ) * I)‖ ≤ 0.00000012735 := by
  have hl := lg_21
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.350422867922137488 63.350422899134199912 (-0.5185698) 0.00000002734 0.8685289298587 (-0.495638475099) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_22 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0841384359961:ℝ):ℂ) + (((-0.996454075002):ℝ):ℂ) * I)‖ ≤ 0.00000012397 := by
  have hl := lg_22
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.318411347844034664 64.31841138946007628 (-1.4865583) 0.00000002396 0.0841384359961 (-0.996454075002) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_23 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7451196807835):ℝ):ℂ) + (((-0.666930776975):ℝ):ℂ) * I)‖ ≤ 0.00000014839 := by
  have hl := lg_23
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.243363623417927728 65.243363665033990152 (-2.4115106) 0.00000004838 (-0.7451196807835) (-0.666930776975) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_24 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9879344720454):ℝ):ℂ) + ((0.1548724590064:ℝ):ℂ) * I)‖ ≤ 0.0000001429 := by
  have hl := lg_24
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.128944080244276512 66.12894412186029732 2.9860943 0.00000004289 (-0.9879344720454) 0.1548724590064 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_25 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5361536748279):ℝ):ℂ) + ((0.8441203924563:ℝ):ℂ) * I)‖ ≤ 0.00000013677 := by
  have hl := lg_25
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.978368142221721744 66.97836818383776336 2.1366702 0.00000003676 (-0.5361536748279) 0.8441203924563 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_26 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2476275067249:ℝ):ℂ) + ((0.9688553131986:ℝ):ℂ) * I)‖ ≤ 0.00000013748 := by
  have hl := lg_26
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.7944727415152136 67.794472783131255216 1.3205656 0.00000003747 0.2476275067249 0.9688553131986 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_27 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8601335422016:ℝ):ℂ) + ((0.5100689066976:ℝ):ℂ) * I)‖ ≤ 0.00000014384 := by
  have hl := lg_27
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.579773491591229536 68.57977352280329196 0.5352649 0.00000004383 0.8601335422016 0.5100689066976 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_28 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9755749165291:ℝ):ℂ) + (((-0.2196669803119):ℝ):ℂ) * I)‖ ≤ 0.0000001529 := by
  have hl := lg_28
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.336511426089860976 69.336511467705902592 (-0.2214731) 0.00000005289 0.9755749165291 (-0.2196669803119) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_29 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5803374752361:ℝ):ℂ) + (((-0.814376089308):ℝ):ℂ) * I)‖ ≤ 0.00000017027 := by
  have hl := lg_29
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.066691608722767136 70.06669165033882956 (-0.9516533) 0.00000007026 0.5803374752361 (-0.814376089308) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_30 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0861733635063):ℝ):ℂ) + (((-0.9962801570952):ℝ):ℂ) * I)‖ ≤ 0.00000015865 := by
  have hl := lg_30
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.772115095990337384 70.772115137606379 (-1.6570767) 0.00000005864 (-0.0861733635063) (-0.9962801570952) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_31 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6951086864859):ℝ):ℂ) + (((-0.7189046626285):ℝ):ℂ) * I)‖ ≤ 0.0000001497 := by
  have hl := lg_31
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.454405729291113304 71.454405770907175728 (-2.3393674) 0.00000004969 (-0.6951086864859) (-0.7189046626285) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_32 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9899916920228):ℝ):ℂ) + (((-0.1411256508192):ℝ):ℂ) * I)‖ ≤ 0.00000014058 := by
  have hl := lg_32
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.115032638412 72.115032690432 (-2.9999943) 0.00000004057 (-0.9899916920228) (-0.1411256508192) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_33 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.878205860783):ℝ):ℂ) + ((0.4782828305424:ℝ):ℂ) * I)‖ ≤ 0.00000016881 := by
  have hl := lg_33
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.755329317358711176 72.7553293589747736 2.6428943 0.0000000688 (-0.878205860783) 0.4782828305424 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_34 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4357915770215):ℝ):ℂ) + ((0.9000476106257:ℝ):ℂ) * I)‖ ≤ 0.00000013505 := by
  have hl := lg_34
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.376509769168358672 73.37650982118837948 2.0217139 0.00000003504 (-0.4357915770215) 0.9000476106257 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_35 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1516675547446:ℝ):ℂ) + ((0.9884315620405:ℝ):ℂ) * I)‖ ≤ 0.00000014433 := by
  have hl := lg_35
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.979682441835921848 73.979682483451984272 1.4185412 0.00000004432 0.1516675547446 0.9884315620405 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_36 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6731311810228:ℝ):ℂ) + ((0.7395230984458:ℝ):ℂ) * I)‖ ≤ 0.00000013641 := by
  have hl := lg_36
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.565862049758953024 74.56586209137499464 0.8323616 0.0000000364 0.6731311810228 0.7395230984458 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_37 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9658107085652:ℝ):ℂ) + ((0.259248288752:ℝ):ℂ) * I)‖ ≤ 0.00000016014 := by
  have hl := lg_37
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.135979904665229136 75.13597994628129156 0.2622438 0.00000006013 0.9658107085652 0.259248288752 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_38 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9574772280268:ℝ):ℂ) + (((-0.2885088522214):ℝ):ℂ) * I)‖ ≤ 0.00000014543 := by
  have hl := lg_38
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.690892789950835224 75.690892831566897648 (-0.2926691) 0.00000004542 0.9574772280268 (-0.2885088522214) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_39 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.672535350864:ℝ):ℂ) + (((-0.7400649983875):ℝ):ℂ) * I)‖ ≤ 0.00000016651 := by
  have hl := lg_39
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.231390711029890112 76.231390752645952536 (-0.833167) 0.0000000665 0.672535350864 (-0.7400649983875) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p808_40 : ‖exp (-((((((20808:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2092582231416:ℝ):ℂ) + (((-0.9778604174664):ℝ):ℂ) * I)‖ ≤ 0.00000013201 := by
  have hl := lg_40
  refine (ecis_approx ((((20808:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.758203654158060872 76.75820370617808168 (-1.35998) 0.000000032 0.2092582231416 (-0.9778604174664) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_2 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3091115353279):ℝ):ℂ) + (((-0.9510257928813):ℝ):ℂ) * I)‖ ≤ 0.0000001523 := by
  have hl := lg_2
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.4514255620747 14.4514255724992 (-1.885055) 0.00000005229 (-0.3091115353279) (-0.9510257928813) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_3 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6107261239383):ℝ):ℂ) + ((0.7918419043764:ℝ):ℂ) * I)‖ ≤ 0.00000012771 := by
  have hl := lg_3
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.904967601021811236 22.904967611446332085 2.2277736 0.0000000277 (-0.6107261239383) 0.7918419043764 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_4 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8089001720168):ℝ):ℂ) + ((0.5879460108363:ℝ):ℂ) * I)‖ ≤ 0.00000011176 := by
  have hl := lg_4
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.9028511241494 28.9028511449984 2.5130754 0.00000001175 (-0.8089001720168) 0.5879460108363 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_5 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5383249150043):ℝ):ℂ) + (((-0.8427373765756):ℝ):ℂ) * I)‖ ≤ 0.00000011047 := by
  have hl := lg_5
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.555171025499343441 33.55517104634836429 (-2.1392445) 0.00000001046 (-0.5383249150043) (-0.8427373765756) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_6 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9418445311847:ℝ):ℂ) + ((0.3360489236368:ℝ):ℂ) * I)‖ ≤ 0.00000014088 := by
  have hl := lg_6
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.356393163096511236 37.356393183945532085 0.3427187 0.00000004087 0.9418445311847 0.3360489236368 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_7 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9636577813418):ℝ):ℂ) + (((-0.2671398139802):ℝ):ℂ) * I)‖ ≤ 0.00000015628 := by
  have hl := lg_7
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.570280686815013278 40.570280707664054976 (-2.8711689) 0.00000005627 (-0.9636577813418) (-0.2671398139802) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_8 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8091921952581:ℝ):ℂ) + ((0.5875440333569:ℝ):ℂ) * I)‖ ≤ 0.00000016405 := by
  have hl := lg_8
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.3542766862241 43.3542767174976 0.6280204 0.00000006404 0.8091921952581 0.5875440333569 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_9 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2540271961322):ℝ):ℂ) + (((-0.9671970758971):ℝ):ℂ) * I)‖ ≤ 0.00000014823 := by
  have hl := lg_9
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.809935202043622472 45.80993522289266417 (-1.8276381) 0.00000004822 (-0.2540271961322) (-0.9671970758971) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_10 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.63506261247):ℝ):ℂ) + ((0.772460664518:ℝ):ℂ) * I)‖ ≤ 0.00000016143 := by
  have hl := lg_10
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.006596587574043441 48.00659661884756429 2.2588859 0.00000006142 (-0.63506261247) 0.772460664518 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_11 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9632989097181:ℝ):ℂ) + ((0.268431016345:ℝ):ℂ) * I)‖ ≤ 0.00000013114 := by
  have hl := lg_11
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.993718526314394517 49.993718557587936215 0.2717639 0.00000003113 0.9632989097181 0.268431016345 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_12 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0284561849743:ℝ):ℂ) + (((-0.9995950407723):ℝ):ℂ) * I)‖ ≤ 0.00000013228 := by
  have hl := lg_12
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.807818725171211236 51.807818756444732085 (-1.5423363) 0.00000003227 0.0284561849743 (-0.9995950407723) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_13 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9975820915734):ℝ):ℂ) + ((0.0694979858634:ℝ):ℂ) * I)‖ ≤ 0.00000012717 := by
  have hl := lg_13
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.4766291374567633 53.476629168730304998 3.0720386 0.00000002716 (-0.9975820915734) 0.0694979858634 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_14 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0438207900984:ℝ):ℂ) + ((0.9990394078088:ℝ):ℂ) * I)‖ ≤ 0.00000011574 := by
  have hl := lg_14
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.021706248889713278 55.021706280163254976 1.5269615 0.00000001573 0.0438207900984 0.9990394078088 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_15 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9960838579274:ℝ):ℂ) + ((0.0884135056231:ℝ):ℂ) * I)‖ ≤ 0.00000013811 := by
  have hl := lg_15
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.460138626521154677 56.460138657794696375 0.0885291 0.0000000381 0.9960838579274 0.0884135056231 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_16 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3086389834429:ℝ):ℂ) + (((-0.9511792564492):ℝ):ℂ) * I)‖ ≤ 0.0000001254 := by
  have hl := lg_16
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.8057022482988 57.8057022899968 (-1.2570345) 0.00000002539 0.3086389834429 (-0.9511792564492) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_17 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8135323329126):ℝ):ℂ) + (((-0.5815196843194):ℝ):ℂ) * I)‖ ≤ 0.00000016565 := by
  have hl := lg_17
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.069664988549632466 59.069665030247653315 (-2.5209972) 0.00000006564 (-0.8135323329126) (-0.5815196843194) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_18 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8413066795262):ℝ):ℂ) + ((0.540558110582:ℝ):ℂ) * I)‖ ≤ 0.00000012361 := by
  have hl := lg_18
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.261360764118322472 60.26136079539186417 2.5704923 0.0000000236 (-0.8413066795262) 0.540558110582 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_19 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.127205943738:ℝ):ℂ) + ((0.9918763269066:ℝ):ℂ) * I)‖ ≤ 0.00000011987 := by
  have hl := lg_19
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.388608260382285947 61.388608291655848494 1.4432448 0.00000001986 0.127205943738 0.9918763269066 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_20 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9309351951221:ℝ):ℂ) + ((0.3651844225634:ℝ):ℂ) * I)‖ ≤ 0.00000012216 := by
  have hl := lg_20
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.458022149648743441 62.45802219134676429 0.3738309 0.00000002215 0.9309351951221 0.3651844225634 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_21 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8000635407892:ℝ):ℂ) + (((-0.5999152696005):ℝ):ℂ) * I)‖ ≤ 0.00000014733 := by
  have hl := lg_21
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.475248287836824514 63.475248319110387061 (-0.6433952) 0.00000004732 0.8000635407892 (-0.5999152696005) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_22 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0424818848992):ℝ):ℂ) + (((-0.9990972372373):ℝ):ℂ) * I)‖ ≤ 0.00000015831 := by
  have hl := lg_22
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.445144088389094517 64.445144130087136215 (-1.613291) 0.0000000583 (-0.0424818848992) (-0.9990972372373) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_23 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.824472526799):ℝ):ℂ) + (((-0.5659019813483):ℝ):ℂ) * I)‖ ≤ 0.00000015615 := by
  have hl := lg_23
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.371918886228391734 65.371918927926454281 (-2.5400658) 0.00000005614 (-0.824472526799) (-0.5659019813483) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_24 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9594368273213):ℝ):ℂ) + ((0.2819237027077:ℝ):ℂ) * I)‖ ≤ 0.00000014998 := by
  have hl := lg_24
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.259244287245911236 66.259244328943932085 2.8557941 0.00000004997 (-0.9594368273213) 0.2819237027077 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_25 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4204125652562):ℝ):ℂ) + ((0.9073330562539:ℝ):ℂ) * I)‖ ≤ 0.00000012799 := by
  have hl := lg_25
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.110342050998686882 67.11034209269672858 2.0046963 0.00000002798 (-0.4204125652562) 0.9073330562539 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_26 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3744584166386:ℝ):ℂ) + ((0.9272437080986:ℝ):ℂ) * I)‖ ≤ 0.00000016227 := by
  have hl := lg_26
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.9280546995314633 67.928054741229504998 1.1869837 0.00000006226 0.3744584166386 0.9272437080986 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_27 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9210081804079:ℝ):ℂ) + ((0.3895432345989:ℝ):ℂ) * I)‖ ≤ 0.00000015538 := by
  have hl := lg_27
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.714902803065433708 68.714902834338996255 0.4001356 0.00000005537 0.9210081804079 0.3895432345989 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_28 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9365667332255:ℝ):ℂ) + (((-0.3504893068488):ℝ):ℂ) * I)‖ ≤ 0.00000016803 := by
  have hl := lg_28
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.473131810964413278 69.473131852662454976 (-0.3580935) 0.00000006802 0.9365667332255 (-0.3504893068488) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_29 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4627403416454:ℝ):ℂ) + (((-0.8864938669917):ℝ):ℂ) * I)‖ ≤ 0.00000014128 := by
  have hl := lg_29
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.204750737709581508 70.204750779407644055 (-1.0897124) 0.00000004127 0.4627403416454 (-0.8864938669917) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_30 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2238173888895):ℝ):ℂ) + (((-0.9746310976106):ℝ):ℂ) * I)‖ ≤ 0.00000015133 := by
  have hl := lg_30
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.911564188595854677 70.911564230293896375 (-1.7965258) 0.00000005132 (-0.2238173888895) (-0.9746310976106) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_31 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7891135284002):ℝ):ℂ) + (((-0.6142473762667):ℝ):ℂ) * I)‖ ≤ 0.00000016737 := by
  have hl := lg_31
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.595199204632373187 71.595199246330435734 (-2.4801608) 0.00000006736 (-0.7891135284002) (-0.6142473762667) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_32 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999998762252):ℝ):ℂ) + ((0.0004968532652:ℝ):ℂ) * I)‖ ≤ 0.0000001758 := by
  have hl := lg_32
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.2571278103735 72.257127862496 3.1410958 0.00000007579 (-0.9999998762252) 0.0004968532652 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_33 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8008667364951):ℝ):ℂ) + ((0.5988426089767:ℝ):ℂ) * I)‖ ≤ 0.00000015883 := by
  have hl := lg_33
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.898686127336205753 72.8986861690342683 2.4995375 0.00000005882 (-0.8008667364951) 0.5988426089767 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_34 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3015679835713):ℝ):ℂ) + ((0.9534446765718:ℝ):ℂ) * I)‖ ≤ 0.00000013555 := by
  have hl := lg_34
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.521090550624332466 73.521090602746853315 1.8771331 0.00000003554 (-0.3015679835713) 0.9534446765718 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_35 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2936321984362:ℝ):ℂ) + ((0.9559184756251:ℝ):ℂ) * I)‖ ≤ 0.00000016787 := by
  have hl := lg_35
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.125451712314356719 74.125451754012419266 1.272772 0.00000006786 0.2936321984362 0.9559184756251 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_36 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7741423051462:ℝ):ℂ) + ((0.6330116044614:ℝ):ℂ) * I)‖ ≤ 0.00000015998 := by
  have hl := lg_36
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.712786326193022472 74.71278636789106417 0.6854373 0.00000005997 0.7741423051462 0.6330116044614 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_37 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9934867081738:ℝ):ℂ) + ((0.1139480613347:ℝ):ℂ) * I)‖ ≤ 0.00000014713 := by
  have hl := lg_37
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.284027539041011258 75.284027580739073805 0.1141961 0.00000004712 0.9934867081738 0.1139480613347 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_38 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9039791456658:ℝ):ℂ) + (((-0.4275765477682):ℝ):ℂ) * I)‖ ≤ 0.00000016371 := by
  have hl := lg_38
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.840033822456985947 75.840033864155048494 (-0.4418102) 0.0000000637 0.9039791456658 (-0.4275765477682) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_39 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5542180325544:ℝ):ℂ) + (((-0.832371535068):ℝ):ℂ) * I)‖ ≤ 0.00000014769 := by
  have hl := lg_39
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.381596738478574536 76.381596780176637083 (-0.9833731) 0.00000004768 0.5542180325544 (-0.832371535068) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p849_40 : ‖exp (-((((((20849:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0595369975617:ℝ):ℂ) + (((-0.9982260995993):ℝ):ℂ) * I)‖ ≤ 0.00000017445 := by
  have hl := lg_40
  refine (ecis_approx ((((20849:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.909447711723443441 76.90944776384596429 (-1.5112241) 0.00000007444 0.0595369975617 (-0.9982260995993) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_2 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3360102824917):ℝ):ℂ) + (((-0.9418583174011):ℝ):ℂ) * I)‖ ≤ 0.00000011791 := by
  have hl := lg_2
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.479844596467 14.479844606912 (-1.913474) 0.0000000179 (-0.3360102824917) (-0.9418583174011) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_3 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5744517287894):ℝ):ℂ) + ((0.8185384604774:ℝ):ℂ) * I)‖ ≤ 0.00000012389 := by
  have hl := lg_3
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.95001070484654596 22.95001071529156685 2.1827305 0.00000002388 (-0.5744517287894) 0.8185384604774 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_4 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.774194175568):ℝ):ℂ) + ((0.6329481641304:ℝ):ℂ) * I)‖ ≤ 0.00000014298 := by
  have hl := lg_4
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.959689192934 28.959689213824 2.4562373 0.00000004297 (-0.774194175568) 0.6329481641304 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_5 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5927226936927):ℝ):ℂ) + (((-0.8054066105826):ℝ):ℂ) * I)‖ ≤ 0.00000015603 := by
  have hl := lg_5
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.62115797988782601 33.6211580007778469 (-2.2052315) 0.00000005602 (-0.5927226936927) (-0.8054066105826) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_6 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9639689447883:ℝ):ℂ) + ((0.2660147993699:ℝ):ℂ) * I)‖ ≤ 0.00000014178 := by
  have hl := lg_6
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.42985530131354596 37.42985532220356685 0.2692565 0.00000004177 0.9639689447883 0.2660147993699 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_7 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9818828887409):ℝ):ℂ) + (((-0.189488766055):ℝ):ℂ) * I)‖ ≤ 0.00000014019 := by
  have hl := lg_7
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.65006300290496558 40.65006302379500736 (-2.9509512) 0.00000004018 (-0.9818828887409) (-0.189488766055) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_8 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8562846965307:ℝ):ℂ) + ((0.5165041321106:ℝ):ℂ) * I)‖ ≤ 0.00000016087 := by
  have hl := lg_8
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.439533789401 43.439533820736 0.5427633 0.00000006086 0.8562846965307 0.5165041321106 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_9 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3400104158285):ℝ):ℂ) + (((-0.9404216698513):ℝ):ℂ) * I)‖ ≤ 0.00000014058 := by
  have hl := lg_9
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.90002140969309192 45.9000214305831337 (-1.9177243) 0.00000004057 (-0.3400104158285) (-0.9404216698513) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_10 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5594180722641):ℝ):ℂ) + ((0.8288856497823:ℝ):ℂ) * I)‖ ≤ 0.00000015027 := by
  have hl := lg_10
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.10100257635482601 48.1010026076898469 2.1644799 0.00000005026 (-0.5594180722641) 0.8288856497823 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_11 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9849951889913:ℝ):ℂ) + ((0.1725817999211:ℝ):ℂ) * I)‖ ≤ 0.00000012498 := by
  have hl := lg_11
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.09203223246715437 50.09203226380219615 0.1734502 0.00000002497 0.9849951889913 0.1725817999211 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_12 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0733552261129):ℝ):ℂ) + (((-0.9973058762494):ℝ):ℂ) * I)‖ ≤ 0.00000015967 := by
  have hl := lg_12
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.90969989778054596 51.90969992911556685 (-1.6442175) 0.00000005966 (-0.0733552261129) (-0.9973058762494) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_13 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9847757799908):ℝ):ℂ) + ((0.173829407136:ℝ):ℂ) * I)‖ ≤ 0.00000012781 := by
  have hl := lg_13
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.581792061080713 53.58179209241575478 2.9668757 0.0000000278 (-0.9847757799908) 0.173829407136 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_14 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1514511834436:ℝ):ℂ) + ((0.9884647383865:ℝ):ℂ) * I)‖ ≤ 0.00000016526 := by
  have hl := lg_14
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.12990759937196558 55.12990763070700736 1.4187601 0.00000006525 0.1514511834436 0.9884647383865 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_15 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997468654298:ℝ):ℂ) + (((-0.0224990013827):ℝ):ℂ) * I)‖ ≤ 0.00000015147 := by
  have hl := lg_15
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.57116868473437197 56.57116871606941375 (-0.0225009) 0.00000005146 0.9997468654298 (-0.0224990013827) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_16 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1987533480314:ℝ):ℂ) + (((-0.980049542955):ℝ):ℂ) * I)‖ ≤ 0.00000016305 := by
  have hl := lg_16
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.919378385868 57.919378427648 (-1.3707106) 0.00000006304 0.1987533480314 (-0.980049542955) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_17 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8754483366384):ℝ):ℂ) + (((-0.4833117107879):ℝ):ℂ) * I)‖ ≤ 0.00000012902 := by
  have hl := lg_17
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.18582673561330626 59.18582677739332715 (-2.637159) 0.00000002901 (-0.8754483366384) (-0.4833117107879) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_18 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7714969711682):ℝ):ℂ) + ((0.6362329946165:ℝ):ℂ) * I)‖ ≤ 0.00000016565 := by
  have hl := lg_18
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.37986600616009192 60.3798660374951337 2.451987 0.00000006564 (-0.7714969711682) 0.6362329946165 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_19 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2457307900318:ℝ):ℂ) + ((0.9693381137819:ℝ):ℂ) * I)‖ ≤ 0.00000011805 := by
  have hl := lg_19
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.50933025849613667 61.50933028983119934 1.3225228 0.00000001804 0.2457307900318 0.9693381137819 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_20 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9686630679204:ℝ):ℂ) + ((0.2483784629292:ℝ):ℂ) * I)‖ ≤ 0.00000014282 := by
  have hl := lg_20
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.58084717282182601 62.5808472146018469 0.2510059 0.00000004281 0.9686630679204 0.2483784629292 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_21 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.719148165968:ℝ):ℂ) + (((-0.694856758897):ℝ):ℂ) * I)‖ ≤ 0.00000016406 := by
  have hl := lg_21
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.60007370775151154 63.60007373908657421 (-0.7682207) 0.00000006405 0.719148165968 (-0.694856758897) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_22 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1684209080179):ℝ):ℂ) + (((-0.9857151706967):ℝ):ℂ) * I)‖ ≤ 0.00000014288 := by
  have hl := lg_22
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.57187682893415437 64.57187687071419615 (-1.7400238) 0.00000004287 (-0.1684209080179) (-0.9857151706967) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_23 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8902185779494):ℝ):ℂ) + (((-0.4555336248488):ℝ):ℂ) * I)‖ ≤ 0.00000012277 := by
  have hl := lg_23
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.50047414903885574 65.50047419081891841 (-2.6686211) 0.00000002276 (-0.8902185779494) (-0.4555336248488) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_24 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9146727617671):ℝ):ℂ) + ((0.4041951740759:ℝ):ℂ) * I)‖ ≤ 0.00000015707 := by
  have hl := lg_24
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.38954449424754596 66.38954453602756685 2.7254939 0.00000005706 (-0.9146727617671) 0.4041951740759 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_25 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2973597053833):ℝ):ℂ) + ((0.954765523892:ℝ):ℂ) * I)‖ ≤ 0.0000001226 := by
  have hl := lg_25
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.24231595977565202 67.2423160015556938 1.8727224 0.00000002259 (-0.2973597053833) 0.954765523892 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_26 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4946174611614:ℝ):ℂ) + ((0.869110791047:ℝ):ℂ) * I)‖ ≤ 0.00000012144 := by
  have hl := lg_26
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.061636657547713 68.06163669932775478 1.0534017 0.00000002143 0.4946174611614 0.869110791047 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_27 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9650908770253:ℝ):ℂ) + ((0.261915251718:ℝ):ℂ) * I)‖ ≤ 0.00000016445 := by
  have hl := lg_27
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.85003211453963788 68.85003214587470055 0.2650062 0.00000006444 0.9650908770253 0.261915251718 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_28 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8801046278536:ℝ):ℂ) + (((-0.4747797847746):ℝ):ℂ) * I)‖ ≤ 0.00000015866 := by
  have hl := lg_28
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.60975219583896558 69.60975223761900736 (-0.4947138) 0.00000005865 0.8801046278536 (-0.4747797847746) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_29 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3363372317337:ℝ):ℂ) + (((-0.9417416134746):ℝ):ℂ) * I)‖ ≤ 0.00000012952 := by
  have hl := lg_29
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.34280986669639588 70.34280990847645855 (-1.2277715) 0.00000002951 0.3363372317337 (-0.9417416134746) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_30 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3571160982589):ℝ):ℂ) + (((-0.9340600046902):ℝ):ℂ) * I)‖ ≤ 0.00000014402 := by
  have hl := lg_30
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.05101328120137197 71.05101332298141375 (-1.9359749) 0.00000004401 (-0.3571160982589) (-0.9340600046902) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_31 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8675018176409):ℝ):ℂ) + (((-0.4974340120094):ℝ):ℂ) * I)‖ ≤ 0.00000014279 := by
  have hl := lg_31
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.73599267997363307 71.73599272175369574 (-2.6209543) 0.00000004278 (-0.8675018176409) (-0.4974340120094) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_32 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9898509809198):ℝ):ℂ) + ((0.1421092367408:ℝ):ℂ) * I)‖ ≤ 0.00000014842 := by
  have hl := lg_32
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.399222982335 72.39922303456 2.9990007 0.00000004841 (-0.9898509809198) 0.1421092367408 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_33 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7070970299773):ℝ):ℂ) + ((0.7071165322437:ℝ):ℂ) * I)‖ ≤ 0.00000014886 := by
  have hl := lg_33
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.04204293731370033 73.042042979093763 2.3561807 0.00000004885 (-0.7070970299773) 0.7071165322437 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_34 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1610515047563):ℝ):ℂ) + ((0.9869460029886:ℝ):ℂ) * I)‖ ≤ 0.00000015409 := by
  have hl := lg_34
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.66567133208030626 73.66567138430532715 1.7325523 0.00000005408 (-0.1610515047563) 0.9869460029886 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_35 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4293686820132:ℝ):ℂ) + ((0.9031293013219:ℝ):ℂ) * I)‖ ≤ 0.00000013843 := by
  have hl := lg_35
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.27122098279279159 74.27122102457285426 1.1270027 0.00000003842 0.4293686820132 0.9031293013219 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_36 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8584722017464:ℝ):ℂ) + ((0.5128600967405:ℝ):ℂ) * I)‖ ≤ 0.00000015827 := by
  have hl := lg_36
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.85971060262709192 74.8597106444071337 0.5385131 0.00000005826 0.8584722017464 0.5128600967405 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_37 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.999427092686:ℝ):ℂ) + (((-0.0338450351624):ℝ):ℂ) * I)‖ ≤ 0.00000012906 := by
  have hl := lg_37
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.43207517341679338 75.43207521519685605 (-0.0338515) 0.00000002905 0.999427092686 (-0.0338450351624) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_38 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8304110926651:ℝ):ℂ) + (((-0.557151161875):ℝ):ℂ) * I)‖ ≤ 0.00000013121 := by
  have hl := lg_38
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.98917485496313667 75.98917489674319934 (-0.5909512) 0.0000000312 0.8304110926651 (-0.557151161875) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_39 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4234201004301:ℝ):ℂ) + (((-0.9059334515028):ℝ):ℂ) * I)‖ ≤ 0.00000012157 := by
  have hl := lg_39
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.53180276592725896 76.53180280770732163 (-1.1335791) 0.00000002156 0.4234201004301 (-0.9059334515028) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_40 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0915434299177):ℝ):ℂ) + (((-0.9958010847747):ℝ):ℂ) * I)‖ ≤ 0.00000013537 := by
  have hl := lg_40
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.06069176928882601 77.0606918215138469 (-1.6624681) 0.00000003536 (-0.0915434299177) (-0.9958010847747) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_41 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.570816940518):ℝ):ℂ) + (((-0.8210773534861):ℝ):ℂ) * I)‖ ≤ 0.00000013987 := by
  have hl := lg_41
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.5765204463016762 77.57652049852671798 (-2.1782968) 0.00000003986 (-0.570816940518) (-0.8210773534861) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_42 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8960977517524):ℝ):ℂ) + (((-0.4438567552626):ℝ):ℂ) * I)‖ ≤ 0.00000015986 := by
  have hl := lg_42
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.07991830421851154 78.07991834599857421 (-2.6816946) 0.00000005985 (-0.8960977517524) (-0.4438567552626) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_43 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9994990519782):ℝ):ℂ) + ((0.0316487674608:ℝ):ℂ) * I)‖ ≤ 0.00000014358 := by
  have hl := lg_43
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.5714703951174642 78.57147043689754776 3.1099386 0.00000004357 (-0.9994990519782) 0.0316487674608 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_44 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8718128716896):ℝ):ℂ) + ((0.4898390722136:ℝ):ℂ) * I)‖ ≤ 0.00000016795 := by
  have hl := lg_44
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.05172142540115437 79.05172147762619615 2.6296875 0.00000006794 (-0.8718128716896) 0.4898390722136 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_45 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5558900172439):ℝ):ℂ) + ((0.831255850337:ℝ):ℂ) * I)‖ ≤ 0.00000013804 := by
  have hl := lg_45
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.52117938958091793 79.5211794313609806 2.1602296 0.00000003803 (-0.5558900172439) 0.831255850337 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_46 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1299255304896):ℝ):ℂ) + ((0.9915237548977:ℝ):ℂ) * I)‖ ≤ 0.00000014784 := by
  have hl := lg_46
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.98031874550585574 79.98031879773091841 1.7010902 0.00000004783 (-0.1299255304896) 0.9915237548977 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_47 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.313589371581:ℝ):ℂ) + ((0.9495586901458:ℝ):ℂ) * I)‖ ≤ 0.00000013148 := by
  have hl := lg_47
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.42958337257177281 80.42958342479685637 1.2518256 0.00000003147 0.313589371581 0.9495586901458 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_48 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6880340397081:ℝ):ℂ) + ((0.7256784137639:ℝ):ℂ) * I)‖ ≤ 0.00000014962 := by
  have hl := lg_48
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.86938909071454596 80.86938914293956685 0.8120199 0.00000004961 0.6880340397081 0.7256784137639 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_49 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9281879804126:ℝ):ℂ) + ((0.3721116405295:ℝ):ℂ) * I)‖ ≤ 0.00000015427 := by
  have hl := lg_49
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.30012600580993116 81.30012604759001472 0.381283 0.00000005426 0.9281879804126 0.3721116405295 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p89_50 : ‖exp (-((((((20890:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9991697684549:ℝ):ℂ) + (((-0.0407403216211):ℝ):ℂ) * I)‖ ≤ 0.00000013711 := by
  have hl := lg_50
  refine (ecis_approx ((((20890:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.72216055624265202 81.7221606084676938 (-0.0407516) 0.0000000371 0.9991697684549 (-0.0407403216211) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_2 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3626376727224):ℝ):ℂ) + (((-0.931930211078):ℝ):ℂ) * I)‖ ≤ 0.00000012698 := by
  have hl := lg_2
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.5082636308593 14.5082636413248 (-1.941893) 0.00000002697 (-0.3626376727224) (-0.931930211078) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_3 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.537012036565):ℝ):ℂ) + ((0.8435745803284:ℝ):ℂ) * I)‖ ≤ 0.00000012006 := by
  have hl := lg_3
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.995053808671280684 22.995053819136801615 2.1376874 0.00000002005 (-0.537012036565) 0.8435745803284 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_4 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7369878317874):ℝ):ℂ) + ((0.6759060110448:ℝ):ℂ) * I)‖ ≤ 0.00000014677 := by
  have hl := lg_4
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.0165272617186 29.0165272826496 2.3993993 0.00000004676 (-0.7369878317874) 0.6759060110448 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_5 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6445404492375):ℝ):ℂ) + (((-0.7645702121326):ℝ):ℂ) * I)‖ ≤ 0.00000011932 := by
  have hl := lg_5
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.687144934276308579 33.68714495520732951 (-2.2712184) 0.00000001931 (-0.6445404492375) (-0.7645702121326) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_6 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9808934318749:ℝ):ℂ) + ((0.1945458180089:ℝ):ℂ) * I)‖ ≤ 0.0000001174 := by
  have hl := lg_6
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.503317439530580684 37.503317460461601615 0.1957944 0.00000001739 0.9808934318749 0.1945458180089 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_7 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9938614144995):ℝ):ℂ) + (((-0.1106322209494):ℝ):ℂ) * I)‖ ≤ 0.0000001241 := by
  have hl := lg_7
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.729845318994917882 40.729845339925959744 (-3.0307335) 0.00000002409 (-0.9938614144995) (-0.1106322209494) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_8 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8971568278761:ℝ):ℂ) + ((0.4417121530989:ℝ):ℂ) * I)‖ ≤ 0.00000015769 := by
  have hl := lg_8
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.5247908925779 43.5247909239744 0.4575062 0.00000005768 0.8971568278761 0.4417121530989 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_9 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4232361386631):ℝ):ℂ) + (((-0.9060194097953):ℝ):ℂ) * I)‖ ≤ 0.00000013293 := by
  have hl := lg_9
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.990107617342561368 45.99010763827360323 (-2.0078105) 0.00000003292 (-0.4232361386631) (-0.9060194097953) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_10 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4787914243956):ℝ):ℂ) + ((0.877928682707:ℝ):ℂ) * I)‖ ≤ 0.00000013911 := by
  have hl := lg_10
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.195408565135608579 48.19540859653212951 2.0700739 0.0000000391 (-0.4787914243956) 0.877928682707 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_11 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9971785809173:ℝ):ℂ) + ((0.0750658228479:ℝ):ℂ) * I)‖ ≤ 0.00000011883 := by
  have hl := lg_11
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.190345938619914223 50.190345970016456085 0.0751365 0.00000001882 0.9971785809173 0.0750658228479 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_12 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1744057860822):ℝ):ℂ) + (((-0.9846738656938):ℝ):ℂ) * I)‖ ≤ 0.00000014436 := by
  have hl := lg_12
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.011581070389880684 52.011581101786401615 (-1.7460986) 0.00000004435 (-0.1744057860822) (-0.9846738656938) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_13 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9610886344249):ℝ):ℂ) + ((0.2762401790877:ℝ):ℂ) * I)‖ ≤ 0.0000001515 := by
  have hl := lg_13
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.6869549847046627 53.686955016101204562 2.8617128 0.00000005149 (-0.9610886344249) 0.2762401790877 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_14 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.257310088152:ℝ):ℂ) + ((0.9663288873542:ℝ):ℂ) * I)‖ ≤ 0.00000011665 := by
  have hl := lg_14
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.238108949854217882 55.238108981250759744 1.3105588 0.00000001664 0.257310088152 0.9663288873542 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_15 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9910979751373:ℝ):ℂ) + (((-0.133134532255):ℝ):ℂ) * I)‖ ≤ 0.00000012168 := by
  have hl := lg_15
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.682198742947589263 56.682198774344131125 (-0.133531) 0.00000002167 0.9910979751373 (-0.133134532255) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_16 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0863020359458:ℝ):ℂ) + (((-0.9962690191868):ℝ):ℂ) * I)‖ ≤ 0.00000014119 := by
  have hl := lg_16
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.0330545234372 58.0330545652992 (-1.4843868) 0.00000004118 0.0863020359458 (-0.9962690191868) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_17 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9255646617515):ℝ):ℂ) + (((-0.3785895624088):ℝ):ℂ) * I)‖ ≤ 0.00000015994 := by
  have hl := lg_17
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.301988482676980054 59.301988524539000985 (-2.7533207) 0.00000005993 (-0.9255646617515) (-0.3785895624088) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_18 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6908654862842):ℝ):ℂ) + ((0.7229833191983:ℝ):ℂ) * I)‖ ≤ 0.00000012361 := by
  have hl := lg_18
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.498371248201861368 60.49837127959840323 2.3334818 0.0000000236 (-0.6908654862842) 0.7229833191983 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_19 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3606787518565:ℝ):ℂ) + ((0.9326901082135:ℝ):ℂ) * I)‖ ≤ 0.00000011623 := by
  have hl := lg_19
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.630052256609987393 61.630052288006550186 1.2018008 0.00000001622 0.3606787518565 0.9326901082135 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_20 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.991796070453:ℝ):ℂ) + ((0.1278301788859:ℝ):ℂ) * I)‖ ≤ 0.00000016608 := by
  have hl := lg_20
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.703672195994908579 62.70367223785692951 0.1281809 0.00000006607 0.991796070453 0.1278301788859 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_21 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6270420719157:ℝ):ℂ) + (((-0.7789853914212):ℝ):ℂ) * I)‖ ≤ 0.00000014414 := by
  have hl := lg_21
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.724899127666198566 63.724899159062761359 (-0.8930461) 0.00000004413 0.6270420719157 (-0.7789853914212) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_22 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.291658411741):ℝ):ℂ) + (((-0.9565225406958):ℝ):ℂ) * I)‖ ≤ 0.00000013956 := by
  have hl := lg_22
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.698609569479214223 64.698609611341256085 (-1.8667565) 0.00000003955 (-0.291658411741) (-0.9565225406958) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_23 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9412727132886):ℝ):ℂ) + (((-0.3376472701445):ℝ):ℂ) * I)‖ ≤ 0.00000015996 := by
  have hl := lg_23
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.629029411849319746 65.629029453711382539 (-2.7971764) 0.00000005995 (-0.9412727132886) (-0.3376472701445) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_24 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8544012113769):ℝ):ℂ) + ((0.5196138661748:ℝ):ℂ) * I)‖ ≤ 0.00000016415 := by
  have hl := lg_24
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.519844701249180684 66.519844743111201615 2.5951937 0.00000006414 (-0.8544012113769) 0.5196138661748 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_25 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1691352115131):ℝ):ℂ) + ((0.9855928572315:ℝ):ℂ) * I)‖ ≤ 0.00000013145 := by
  have hl := lg_25
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.374289868552617158 67.37428991041465902 1.7407485 0.00000003144 (-0.1691352115131) 0.9855928572315 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_26 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6059635937678:ℝ):ℂ) + ((0.795492377731:ℝ):ℂ) * I)‖ ≤ 0.00000016343 := by
  have hl := lg_26
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.1952186155639627 68.195218657426004562 0.9198197 0.00000006342 0.6059635937678 0.795492377731 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_27 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9915778441648:ℝ):ℂ) + ((0.1295120803687:ℝ):ℂ) * I)‖ ≤ 0.00000015298 := by
  have hl := lg_27
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.985161426013842052 68.985161457410404845 0.1298769 0.00000005297 0.9915778441648 0.1295120803687 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_28 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8072407524287:ℝ):ℂ) + (((-0.5902223035589):ℝ):ℂ) * I)‖ ≤ 0.00000014362 := by
  have hl := lg_28
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.746372580713517882 69.746372622575559744 (-0.6313342) 0.00000004361 0.8072407524287 (-0.5902223035589) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_29 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2035336042273:ℝ):ℂ) + (((-0.9790679608435):ℝ):ℂ) * I)‖ ≤ 0.00000015858 := by
  have hl := lg_29
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.480868995683210252 70.480869037545273045 (-1.3658306) 0.00000005857 0.2035336042273 (-0.9790679608435) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_30 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4834815558899):ℝ):ℂ) + (((-0.875354548231):ℝ):ℂ) * I)‖ ≤ 0.00000013671 := by
  have hl := lg_30
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.190462373806889263 71.190462415668931125 (-2.075424) 0.0000000367 (-0.4834815558899) (-0.875354548231) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_31 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9287221713275):ℝ):ℂ) + (((-0.3707763858817):ℝ):ℂ) * I)‖ ≤ 0.00000012368 := by
  have hl := lg_31
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.876786155314892953 71.876786197176955746 (-2.7617478) 0.00000002367 (-0.9287221713275) (-0.3707763858817) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_32 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9597495647067):ℝ):ℂ) + ((0.2808572107193:ℝ):ℂ) * I)‖ ≤ 0.00000013187 := by
  have hl := lg_32
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.5413181542965 72.541318206624 2.8569055 0.00000003186 (-0.9597495647067) 0.2808572107193 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_33 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5988205205631):ℝ):ℂ) + ((0.8008832525035:ℝ):ℂ) * I)‖ ≤ 0.00000013888 := by
  have hl := lg_33
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.185399747291194907 73.1853997891532577 2.2128239 0.00000003887 (-0.5988205205631) 0.8008832525035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_34 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.01717432881):ℝ):ℂ) + ((0.9998525103382:ℝ):ℂ) * I)‖ ≤ 0.00000017263 := by
  have hl := lg_34
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.810252113536280054 73.810252165863800985 1.5879715 0.00000007262 (-0.01717432881) 0.9998525103382 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_35 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5559977878768:ℝ):ℂ) + ((0.8311837702194:ℝ):ℂ) * I)‖ ≤ 0.0000001329 := by
  have hl := lg_35
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.416990253271226461 74.416990295133289254 0.9812334 0.00000003289 0.5559977878768 0.8311837702194 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_36 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9243038493905:ℝ):ℂ) + ((0.3816574301673:ℝ):ℂ) * I)‖ ≤ 0.00000013478 := by
  have hl := lg_36
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.006634879061161368 75.00663492092320323 0.3915888 0.00000003477 0.9243038493905 0.3816574301673 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_37 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9835019237742:ℝ):ℂ) + (((-0.1808976670175):ℝ):ℂ) * I)‖ ≤ 0.00000016351 := by
  have hl := lg_37
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.580122807792575502 75.580122849654638295 (-0.1818991) 0.0000000635 0.9835019237742 (-0.1808976670175) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_38 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7384063862454:ℝ):ℂ) + (((-0.6743559955632):ℝ):ℂ) * I)‖ ≤ 0.00000014319 := by
  have hl := lg_38
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.138315887469287393 76.138315929331350186 (-0.7400922) 0.00000004318 0.7384063862454 (-0.6743559955632) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_39 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2830869785785:ℝ):ℂ) + (((-0.959094240708):ℝ):ℂ) * I)‖ ≤ 0.0000001491 := by
  have hl := lg_39
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.682008793375943384 76.682008835238006177 (-1.2837851) 0.00000004909 0.2830869785785 (-0.959094240708) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_40 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2405339102769):ℝ):ℂ) + (((-0.9706407358059):ℝ):ℂ) * I)‖ ≤ 0.00000015932 := by
  have hl := lg_40
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.211935826854208579 77.21193587918172951 (-1.8137122) 0.00000005931 (-0.2405339102769) (-0.9706407358059) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_41 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6887451976921):ℝ):ℂ) + (((-0.7250034845669):ℝ):ℂ) * I)‖ ≤ 0.00000016717 := by
  have hl := lg_41
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.72877690098326398 77.728776953310805842 (-2.3305532) 0.00000006716 (-0.6887451976921) (-0.7250034845669) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_42 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9533490978367):ℝ):ℂ) + (((-0.3018700008966):ℝ):ℂ) * I)‖ ≤ 0.00000012764 := by
  have hl := lg_42
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.233162758525498566 78.233162800387561359 (-2.8349391) 0.00000002763 (-0.9533490978367) (-0.3018700008966) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_43 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9827770917564):ℝ):ℂ) + ((0.1847949879618:ℝ):ℂ) * I)‖ ≤ 0.00000014836 := by
  have hl := lg_43
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.72567959981826918 78.725679641680352904 2.9557294 0.00000004835 (-0.9827770917564) 0.1847949879618 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_44 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7856459211397):ℝ):ℂ) + ((0.6186763988973:ℝ):ℂ) * I)‖ ≤ 0.00000015935 := by
  have hl := lg_44
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.206873200338514223 79.206873252666056085 2.4745358 0.00000005934 (-0.7856459211397) 0.6186763988973 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_45 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4199226348895):ℝ):ℂ) + ((0.9075599047467:ℝ):ℂ) * I)‖ ≤ 0.00000014173 := by
  have hl := lg_45
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.677252551618869947 79.67725259348093274 2.0041564 0.00000004172 (-0.4199226348895) 0.9075599047467 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_46 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0266772615187:ℝ):ℂ) + ((0.9996440985259:ℝ):ℂ) * I)‖ ≤ 0.00000015064 := by
  have hl := lg_46
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.137293042708619746 80.137293095036182539 1.5441159 0.00000005063 0.0266772615187 0.9996440985259 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_47 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.458962266911:ℝ):ℂ) + ((0.8884557600421:ℝ):ℂ) * I)‖ ≤ 0.00000016916 := by
  have hl := lg_47
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.587439424188596299 80.587439476516180023 1.0939695 0.00000006915 0.458962266911 0.8884557600421 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_48 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7940819876763:ℝ):ℂ) + ((0.6078106587154:ℝ):ℂ) * I)‖ ≤ 0.00000016124 := by
  have hl := lg_48
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.028108332108480684 81.028108384436001615 0.6533006 0.00000006123 0.7940819876763 0.6078106587154 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_49 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9755210248588:ℝ):ℂ) + ((0.2199061846755:ℝ):ℂ) * I)‖ ≤ 0.00000015536 := by
  have hl := lg_49
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.459690637989835764 81.459690679851919488 0.2217183 0.00000005535 0.9755210248588 0.2199061846755 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p931_50 : ‖exp (-((((((20931:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9798385589569:ℝ):ℂ) + (((-0.199790886632):ℝ):ℂ) * I)‖ ≤ 0.00000015842 := by
  have hl := lg_50
  refine (ecis_approx ((((20931:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.882553499411917158 81.88255355173945902 (-0.2011445) 0.00000005841 0.9798385589569 (-0.199790886632) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_2 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3889722942586):ℝ):ℂ) + (((-0.9212494528064):ℝ):ℂ) * I)‖ ≤ 0.00000014912 := by
  have hl := lg_2
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.5366826652516 14.5366826757376 (-1.9703121) 0.00000004911 (-0.3889722942586) (-0.9212494528064) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_3 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4984829950979):ℝ):ℂ) + ((0.8668994772129:ℝ):ℂ) * I)‖ ≤ 0.00000011624 := by
  have hl := lg_3
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.040096912496015408 23.04009692298203638 2.0926443 0.00000001623 (-0.4984829950979) 0.8668994772129 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_4 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6974011751181):ℝ):ℂ) + ((0.7166809617401:ℝ):ℂ) * I)‖ ≤ 0.00000011559 := by
  have hl := lg_4
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.0733653305032 29.0733653514752 2.3425612 0.00000001558 (-0.6974011751181) 0.7166809617401 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_5 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.693552791263):ℝ):ℂ) + (((-0.7204058062708):ℝ):ℂ) * I)‖ ≤ 0.00000014725 := by
  have hl := lg_5
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.753131888664791148 33.75313190963681212 (-2.3372054) 0.00000004724 (-0.693552791263) (-0.7204058062708) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_6 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9925267310747:ℝ):ℂ) + ((0.1220274071765:ℝ):ℂ) * I)‖ ≤ 0.00000015566 := by
  have hl := lg_6
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.576779577747615408 37.57677959871963638 0.1223323 0.00000005565 0.9925267310747 0.1220274071765 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_7 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9995171531487):ℝ):ℂ) + (((-0.0310718513673):ℝ):ℂ) * I)‖ ≤ 0.00000011299 := by
  have hl := lg_7
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.809627635084870184 40.809627656056912128 (-3.1105158) 0.00000001298 (-0.9995171531487) (-0.0310718513673) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_8 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9315116789587:ℝ):ℂ) + ((0.3637114130236:ℝ):ℂ) * I)‖ ≤ 0.00000015452 := by
  have hl := lg_8
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.6100479957548 43.6100480272128 0.3722491 0.00000005451 0.9315116789587 0.3637114130236 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_9 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5030294009909):ℝ):ℂ) + (((-0.8642692993115):ℝ):ℂ) * I)‖ ≤ 0.00000012528 := by
  have hl := lg_9
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.080193824992030816 46.08019384596407276 (-2.0978967) 0.00000002527 (-0.5030294009909) (-0.8642692993115) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_10 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3939007197468):ℝ):ℂ) + ((0.9191529921508:ℝ):ℂ) * I)‖ ≤ 0.00000012795 := by
  have hl := lg_10
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.289814553916391148 48.28981458537441212 1.9756679 0.00000002794 (-0.3939007197468) 0.9191529921508 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_11 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997314207234:ℝ):ℂ) + (((-0.023175124991):ℝ):ℂ) * I)‖ ≤ 0.00000011881 := by
  have hl := lg_11
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.288659644772674076 50.28865967623071602 (-0.0231772) 0.0000000188 0.9997314207234 (-0.023175124991) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_12 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2736477176101):ℝ):ℂ) + (((-0.9618299884311):ℝ):ℂ) * I)‖ ≤ 0.00000011704 := by
  have hl := lg_12
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.113462242999215408 52.11346227445723638 (-1.8479798) 0.00000001703 (-0.2736477176101) (-0.9618299884311) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_13 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.926782337715):ℝ):ℂ) + ((0.3755988529609:ℝ):ℂ) * I)‖ ≤ 0.0000001563 := by
  have hl := lg_13
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.7921179083286124 53.792117939786654344 2.7565498 0.00000005629 (-0.926782337715) 0.3755988529609 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_14 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3601595606993:ℝ):ℂ) + ((0.932890717521:ℝ):ℂ) * I)‖ ≤ 0.00000016429 := by
  have hl := lg_14
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.346310300336470184 55.346310331794512128 1.2023574 0.00000006428 0.3601595606993 0.932890717521 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_15 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9702436894998:ℝ):ℂ) + (((-0.2421305081681):ℝ):ℂ) * I)‖ ≤ 0.00000016347 := by
  have hl := lg_15
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.793228801160806556 56.7932288326188485 (-0.2445611) 0.00000006346 0.9702436894998 (-0.2421305081681) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_16 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0272631947023):ℝ):ℂ) + (((-0.999628290023):ℝ):ℂ) * I)‖ ≤ 0.00000013835 := by
  have hl := lg_16
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.1467306610064 58.1467307029504 (-1.5980629) 0.00000003834 (-0.0272631947023) (-0.999628290023) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_17 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9632059066791):ℝ):ℂ) + (((-0.268764545828):ℝ):ℂ) * I)‖ ≤ 0.00000013489 := by
  have hl := lg_17
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.418150229740653848 59.41815027168467482 (-2.8694825) 0.00000003488 (-0.9632059066791) (-0.268764545828) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_18 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6005431931075):ℝ):ℂ) + ((0.7995923168716:ℝ):ℂ) * I)‖ ≤ 0.00000014992 := by
  have hl := lg_18
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.616876490243630816 60.61687652170167276 2.2149766 0.00000004991 (-0.6005431931075) 0.7995923168716 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_19 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4703766340081:ℝ):ℂ) + ((0.8824657626102:ℝ):ℂ) * I)‖ ≤ 0.00000011709 := by
  have hl := lg_19
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.750774254723838116 61.750774286181901032 1.0810788 0.00000001708 0.4703766340081 0.8824657626102 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_20 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999856577375:ℝ):ℂ) + ((0.0053557743952:ℝ):ℂ) * I)‖ ≤ 0.00000015264 := by
  have hl := lg_20
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.826497219167991148 62.82649726111201212 0.0053558 0.00000005263 0.9999856577375 0.0053557743952 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_21 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5251784762494:ℝ):ℂ) + (((-0.8509921081211):ℝ):ℂ) * I)‖ ≤ 0.00000012423 := by
  have hl := lg_21
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.849724547580885592 63.849724579038948508 (-1.0178715) 0.00000002422 0.5251784762494 (-0.8509921081211) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_22 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4102178955779):ℝ):ℂ) + (((-0.9119875427571):ℝ):ℂ) * I)‖ ≤ 0.00000016179 := by
  have hl := lg_22
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.825342310024274076 64.82534235196831602 (-1.9934893) 0.00000006178 (-0.4102178955779) (-0.9119875427571) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_23 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.976792328366):ℝ):ℂ) + (((-0.2141885779868):ℝ):ℂ) * I)‖ ≤ 0.00000014482 := by
  have hl := lg_23
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.757584674659783752 65.757584716603846668 (-2.9257316) 0.00000004481 (-0.976792328366) (-0.2141885779868) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_24 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7796439654959):ℝ):ℂ) + ((0.6262230329712:ℝ):ℂ) * I)‖ ≤ 0.00000017074 := by
  have hl := lg_24
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.650144908250815408 66.65014495019483638 2.4648934 0.00000007073 (-0.7796439654959) 0.6262230329712 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_25 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.037969144208):ℝ):ℂ) + ((0.99927891206:ℝ):ℂ) * I)‖ ≤ 0.00000014031 := by
  have hl := lg_25
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.506263777329582296 67.50626381927362424 1.6087746 0.0000000403 (-0.037969144208) 0.99927891206 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_26 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7065128192695:ℝ):ℂ) + ((0.7077002446007:ℝ):ℂ) * I)‖ ≤ 0.00000013656 := by
  have hl := lg_26
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.3288005735802124 68.328800615524254344 0.7862378 0.00000003655 0.7065128192695 0.7077002446007 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_27 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999862061788:ℝ):ℂ) + (((-0.0052523758498):ℝ):ℂ) * I)‖ ≤ 0.0000001415 := by
  have hl := lg_27
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.120290737488046224 69.12029076894610914 (-0.0052524) 0.00000004149 0.9999862061788 (-0.0052523758498) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_28 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7193330418882:ℝ):ℂ) + (((-0.6946653689712):ℝ):ℂ) * I)‖ ≤ 0.00000012857 := by
  have hl := lg_28
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.882992965588070184 69.882993007532112128 (-0.7679546) 0.00000002856 0.7193330418882 (-0.6946653689712) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_29 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0668566203078:ℝ):ℂ) + (((-0.9977625931658):ℝ):ℂ) * I)‖ ≤ 0.00000015432 := by
  have hl := lg_29
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.618928124670024624 70.61892816661408754 (-1.5038898) 0.00000005431 0.0668566203078 (-0.9977625931658) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_30 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6004604320862):ℝ):ℂ) + (((-0.7996544688093):ℝ):ℂ) * I)‖ ≤ 0.0000001294 := by
  have hl := lg_30
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.329911466412406556 71.3299115083564485 (-2.2148731) 0.00000002939 (-0.6004604320862) (-0.7996544688093) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_31 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9715630333842):ℝ):ℂ) + (((-0.2367810631843):ℝ):ℂ) * I)‖ ≤ 0.00000014833 := by
  have hl := lg_31
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.017579630656152836 72.017579672600215752 (-2.9025413) 0.00000004832 (-0.9715630333842) (-0.2367810631843) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_32 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9103023847918):ℝ):ℂ) + ((0.4139439190436:ℝ):ℂ) * I)‖ ≤ 0.00000015991 := by
  have hl := lg_32
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.683413326258 72.683413378688 2.7148103 0.0000000599 (-0.9103023847918) 0.4139439190436 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_33 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4782586091567):ℝ):ℂ) + ((0.8782190516961:ℝ):ℂ) * I)‖ ≤ 0.0000001289 := by
  have hl := lg_33
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.328756557268689484 73.3287565992127524 2.0694671 0.00000002889 (-0.4782586091567) 0.8782190516961 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_34 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.127061128439:ℝ):ℂ) + ((0.9918948884029:ℝ):ℂ) * I)‖ ≤ 0.00000016128 := by
  have hl := lg_34
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.954832894992253848 73.95483294742227482 1.4433908 0.00000006127 0.127061128439 0.9918948884029 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_35 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.670833574679:ℝ):ℂ) + ((0.7416079254454:ℝ):ℂ) * I)‖ ≤ 0.00000016242 := by
  have hl := lg_35
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.562759523749661332 74.562759565693724248 0.8354641 0.00000006241 0.670833574679 0.7416079254454 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_36 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9702186480186:ℝ):ℂ) + ((0.242230830071:ℝ):ℂ) * I)‖ ≤ 0.00000013067 := by
  have hl := lg_36
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.153559155495230816 75.15355919743927276 0.2446645 0.00000003066 0.9702186480186 0.242230830071 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_37 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9460595812787:ℝ):ℂ) + (((-0.3239926984837):ℝ):ℂ) * I)‖ ≤ 0.000000144 := by
  have hl := lg_37
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.728170442168357624 75.72817048411242054 (-0.3299468) 0.00000004399 0.9460595812787 (-0.3239926984837) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_38 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6300076224309:ℝ):ℂ) + (((-0.7765889489807):ℝ):ℂ) * I)‖ ≤ 0.00000016619 := by
  have hl := lg_38
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.287456919975438116 76.287456961919501032 (-0.8892333) 0.00000006618 0.6300076224309 (-0.7765889489807) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_39 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1363787932999:ℝ):ℂ) + (((-0.9906567643427):ℝ):ℂ) * I)‖ ≤ 0.00000016535 := by
  have hl := lg_39
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.832214820824627808 76.832214862768690724 (-1.4339912) 0.00000006534 0.1363787932999 (-0.9906567643427) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_40 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3840326189529):ℝ):ℂ) + (((-0.9233195262623):ℝ):ℂ) * I)‖ ≤ 0.00000015071 := by
  have hl := lg_40
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.363179884419591148 77.36317993684961212 (-1.9649562) 0.0000000507 (-0.3840326189529) (-0.9233195262623) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_41 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7907378378989):ℝ):ℂ) + (((-0.6121549409007):ℝ):ℂ) * I)‖ ≤ 0.00000013051 := by
  have hl := lg_41
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.88103335566485176 77.881033408094893704 (-2.4828097) 0.0000000305 (-0.7907378378989) (-0.6121549409007) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_42 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9882558753041):ℝ):ℂ) + (((-0.1528081298171):ℝ):ℂ) * I)‖ ≤ 0.00000016864 := by
  have hl := lg_42
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.386407212832485592 78.386407254776548508 (-2.9881835) 0.00000006863 (-0.9882558753041) (-0.1528081298171) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_43 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9427305006528):ℝ):ℂ) + ((0.3335553971283:ℝ):ℂ) * I)‖ ≤ 0.00000015314 := by
  have hl := lg_43
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.87988880451907416 78.879888846463158048 2.8015202 0.00000005313 (-0.9427305006528) 0.3335553971283 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_44 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6806046967482):ℝ):ℂ) + ((0.7326508354895:ℝ):ℂ) * I)‖ ≤ 0.00000013439 := by
  have hl := lg_44
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.362024975275874076 79.36202502770591602 2.319384 0.00000003438 (-0.6806046967482) 0.7326508354895 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_45 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2737472655481):ℝ):ℂ) + ((0.9618016607407:ℝ):ℂ) * I)‖ ≤ 0.00000016228 := by
  have hl := lg_45
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.833325713656821964 79.83332575560088488 1.8480833 0.00000006227 (-0.2737472655481) 0.9618016607407 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_46 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1826240496771:ℝ):ℂ) + ((0.9831828194591:ℝ):ℂ) * I)‖ ≤ 0.00000015344 := by
  have hl := lg_46
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.294267339911383752 80.294267392341446668 1.3871416 0.00000005343 0.1826240496771 0.9831828194591 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_47 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5929221373533:ℝ):ℂ) + ((0.8052597959891:ℝ):ℂ) * I)‖ ≤ 0.00000013492 := by
  have hl := lg_47
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.745295475805419788 80.745295528235503676 0.9361135 0.00000003491 0.5929221373533 0.8052597959891 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_48 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8801674809829:ℝ):ℂ) + ((0.4746632547608:ℝ):ℂ) * I)‖ ≤ 0.00000013261 := by
  have hl := lg_48
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.186827573502415408 81.18682762593243638 0.4945814 0.0000000326 0.8801674809829 0.4746632547608 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_49 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9980690805167:ℝ):ℂ) + ((0.0621136902512:ℝ):ℂ) * I)‖ ≤ 0.00000012318 := by
  have hl := lg_49
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.619255270169740368 81.619255312113824256 0.0621537 0.00000002317 0.9980690805167 0.0621136902512 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p972_50 : ‖exp (-((((((20972:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9353540960717:ℝ):ℂ) + (((-0.353712757703):ℝ):ℂ) * I)‖ ≤ 0.00000015077 := by
  have hl := lg_50
  refine (ecis_approx ((((20972:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.042946442581182296 82.04294649501122424 (-0.3615375) 0.00000005076 0.9353540960717 (-0.353712757703) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_2 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4149926943315):ℝ):ℂ) + (((-0.9098247433698):ℝ):ℂ) * I)‖ ≤ 0.00000011473 := by
  have hl := lg_2
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.5651016996439 14.5651017101504 (-1.9987311) 0.00000001472 (-0.4149926943315) (-0.9098247433698) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_3 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4589427620071):ℝ):ℂ) + ((0.8884658356946:ℝ):ℂ) * I)‖ ≤ 0.00000011241 := by
  have hl := lg_3
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.085140016320750132 23.085140026827271145 2.0476012 0.0000000124 (-0.4589427620071) 0.8884658356946 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_4 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6555621218796):ℝ):ℂ) + ((0.7551412479392:ℝ):ℂ) * I)‖ ≤ 0.00000013663 := by
  have hl := lg_4
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.1302033992878 29.1302034203008 2.2857231 0.00000003662 (-0.6555621218796) 0.7551412479392 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_5 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.73954623568):ℝ):ℂ) + (((-0.6731057608283):ℝ):ℂ) * I)‖ ≤ 0.00000012818 := by
  have hl := lg_5
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.819118843053273717 33.81911886406629473 (-2.4031923) 0.00000002817 (-0.73954623568) (-0.6731057608283) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_6 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9988060943071:ℝ):ℂ) + ((0.048850649688:ℝ):ℂ) * I)‖ ≤ 0.00000012713 := by
  have hl := lg_6
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.650241715964650132 37.650241736977671145 0.0488701 0.00000002712 0.9988060943071 0.048850649688 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_7 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9988141235778):ℝ):ℂ) + ((0.0486861989257:ℝ):ℂ) * I)‖ ≤ 0.00000012195 := by
  have hl := lg_7
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.889409951174822486 40.889409972187864512 3.0928872 0.00000002194 (-0.9988141235778) 0.0486861989257 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_8 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.959099683386:ℝ):ℂ) + ((0.2830685382179:ℝ):ℂ) * I)‖ ≤ 0.00000015134 := by
  have hl := lg_8
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.6953050989317 43.6953051304512 0.286992 0.00000005133 0.959099683386 0.2830685382179 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_9 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5787430765469):ℝ):ℂ) + (((-0.8155099333169):ℝ):ℂ) * I)‖ ≤ 0.00000011763 := by
  have hl := lg_9
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.170280032641500264 46.17028005365454229 (-2.1879829) 0.00000001762 (-0.5787430765469) (-0.8155099333169) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_10 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.305501984358):ℝ):ℂ) + ((0.9521914395496:ℝ):ℂ) * I)‖ ≤ 0.0000001168 := by
  have hl := lg_10
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.384220542697173717 48.38422057421669473 1.8812619 0.00000001679 (-0.305501984358) 0.9521914395496 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_11 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9926290535914:ℝ):ℂ) + (((-0.1211922520887):ℝ):ℂ) * I)‖ ≤ 0.00000012502 := by
  have hl := lg_11
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.386973350925433929 50.386973382444975955 (-0.1214909) 0.00000002501 0.9926290535914 (-0.1211922520887) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_12 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3700517023753):ℝ):ℂ) + (((-0.9290111611635):ℝ):ℂ) * I)‖ ≤ 0.00000014184 := by
  have hl := lg_12
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.215343415608550132 52.215343447128071145 (-1.949861) 0.00000004183 (-0.3700517023753) (-0.9290111611635) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_13 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8822360069412):ℝ):ℂ) + ((0.4708074213075:ℝ):ℂ) * I)‖ ≤ 0.00000013268 := by
  have hl := lg_13
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.8972808319525621 53.897280863472104126 2.6513869 0.00000003267 (-0.8822360069412) 0.4708074213075 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_14 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4587964730767:ℝ):ℂ) + ((0.8885413869327:ℝ):ℂ) * I)‖ ≤ 0.00000011774 := by
  have hl := lg_14
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.454511650818722486 55.454511682338264512 1.0941561 0.00000001773 0.4587964730767 0.8885413869327 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_15 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.93744086436:ℝ):ℂ) + (((-0.3481445473192):ℝ):ℂ) * I)‖ ≤ 0.00000012629 := by
  have hl := lg_15
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.904258859374023849 56.904258890893565875 (-0.3555911) 0.00000002628 0.93744086436 (-0.3481445473192) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_16 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1404766016001):ℝ):ℂ) + (((-0.9900839986599):ℝ):ℂ) * I)‖ ≤ 0.00000016606 := by
  have hl := lg_16
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.2604067985756 58.2604068406016 (-1.7117391) 0.00000006605 (-0.1404766016001) (-0.9900839986599) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_17 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9878646638814):ℝ):ℂ) + (((-0.1553171126098):ℝ):ℂ) * I)‖ ≤ 0.00000015423 := by
  have hl := lg_17
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.534311976804327642 59.534312018830348655 (-2.9856442) 0.00000005422 (-0.9878646638814) (-0.1553171126098) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_18 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5017969609301):ℝ):ℂ) + ((0.8649854391809:ℝ):ℂ) * I)‖ ≤ 0.00000013953 := by
  have hl := lg_18
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.735381732285400264 60.73538176380494229 2.0964713 0.00000003952 (-0.5017969609301) 0.8649854391809 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_19 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5732276620208:ℝ):ℂ) + ((0.8193961480836:ℝ):ℂ) * I)‖ ≤ 0.00000011897 := by
  have hl := lg_19
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.871496252837688839 61.871496284357251878 0.9603568 0.00000001896 0.5732276620208 0.8193961480836 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_20 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9931084237422:ℝ):ℂ) + (((-0.1171992265004):ℝ):ℂ) * I)‖ ≤ 0.00000012947 := by
  have hl := lg_20
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.949322242341073717 62.94932228436709473 (-0.1174692) 0.00000002946 0.9931084237422 (-0.1171992265004) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_21 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4151424946154:ℝ):ℂ) + (((-0.9097564010022):ℝ):ℂ) * I)‖ ≤ 0.00000012723 := by
  have hl := lg_21
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.974549967495572618 63.974549999015135657 (-1.1426969) 0.00000002722 0.4151424946154 (-0.9097564010022) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_22 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5221975150765):ℝ):ℂ) + (((-0.8528245747167):ℝ):ℂ) * I)‖ ≤ 0.00000012124 := by
  have hl := lg_22
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.952075050569333929 64.952075092595375955 (-2.120222) 0.00000002123 (-0.5221975150765) (-0.8528245747167) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_23 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9961912726573):ℝ):ℂ) + (((-0.0871948839232):ℝ):ℂ) * I)‖ ≤ 0.00000013434 := by
  have hl := lg_23
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.886139937470247758 65.886139979496310797 (-3.0542869) 0.00000003433 (-0.9961912726573) (-0.0871948839232) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_24 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6916685830978):ℝ):ℂ) + ((0.7222150449368:ℝ):ℂ) * I)‖ ≤ 0.00000016374 := by
  have hl := lg_24
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.780445115252450132 66.780445157278471145 2.3345932 0.00000006373 (-0.6916685830978) 0.7222150449368 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_25 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0938572765797:ℝ):ℂ) + ((0.9955856626293:ℝ):ℂ) * I)‖ ≤ 0.00000014917 := by
  have hl := lg_25
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.638237686106547434 67.63823772813258946 1.4768007 0.00000004916 0.0938572765797 0.9955856626293 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_26 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7944737388853:ℝ):ℂ) + ((0.6072985083314:ℝ):ℂ) * I)‖ ≤ 0.00000014739 := by
  have hl := lg_26
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.4623825315964621 68.462382573622504126 0.6526558 0.00000004738 0.7944737388853 0.6072985083314 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_27 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9901626604724:ℝ):ℂ) + (((-0.1399210699155):ℝ):ℂ) * I)‖ ≤ 0.00000013003 := by
  have hl := lg_27
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.255420048962250396 69.255420080481813435 (-0.1403817) 0.00000003002 0.9901626604724 (-0.1399210699155) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
