/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Base
/-!
# Certificat (V2), côté b1left (b1), angles 4

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

lemma cs_b1left_v14p701_6 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3549696723054:ℝ):ℂ) + (((-0.9348778164784):ℝ):ℂ) * I)‖ ≤ 0.00000013548 := by
  have hl := lg_6
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.340655949478718964 26.340655964179733665 (-1.2079147) 0.00000003547 0.3549696723054 (-0.9348778164784) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_7 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9452321352081):ℝ):ℂ) + ((0.3263988516809:ℝ):ℂ) * I)‖ ≤ 0.00000014229 := by
  have hl := lg_7
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.606825093619238822 28.606825108320268224 2.8091014 0.00000004228 (-0.9452321352081) 0.3263988516809 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_8 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6629407555953:ℝ):ℂ) + ((0.7486718604107:ℝ):ℂ) * I)‖ ≤ 0.00000014314 := by
  have hl := lg_8
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.5698700927709 30.5698701148224 0.8460564 0.00000004313 0.6629407555953 0.7486718604107 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_9 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6329241430847:ℝ):ℂ) + (((-0.7742138135557):ℝ):ℂ) * I)‖ ≤ 0.00000013214 := by
  have hl := lg_9
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.301398503776837928 32.30139851847786733 (-0.885472) 0.00000003213 0.6329241430847 (-0.7742138135557) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_10 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7601738000569):ℝ):ℂ) + (((-0.6497197808829):ℝ):ℂ) * I)‖ ≤ 0.00000012681 := by
  have hl := lg_10
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.850303440641086509 33.85030346269260121 (-2.4343769) 0.0000000268 (-0.7601738000569) (-0.6497197808829) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_11 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7687325561133):ℝ):ℂ) + ((0.6395703691797:ℝ):ℂ) * I)‖ ≤ 0.00000014915 := by
  have hl := lg_11
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.251458393944453633 35.251458415995983035 2.4476534 0.00000004914 (-0.7687325561133) 0.6395703691797 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_12 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3915331068977:ℝ):ℂ) + ((0.9201640213587:ℝ):ℂ) * I)‖ ≤ 0.00000012606 := by
  have hl := lg_12
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.530612647069018964 36.530612669120533665 1.1684992 0.00000002605 0.3915331068977 0.9201640213587 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_13 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999663088113:ℝ):ℂ) + (((-0.0082086078128):ℝ):ℂ) * I)‖ ≤ 0.00000015051 := by
  have hl := lg_13
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.7073204925776717 37.707320514629201102 (-0.0082087) 0.0000000505 0.9999663088113 (-0.0082086078128) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_14 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4556714014322:ℝ):ℂ) + (((-0.8901480629181):ℝ):ℂ) * I)‖ ≤ 0.00000015188 := by
  have hl := lg_14
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.796781791209538822 38.796781813261068224 (-1.09767) 0.00000005187 0.4556714014322 (-0.8901480629181) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_15 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5151116223285):ℝ):ℂ) + (((-0.857123104656):ℝ):ℂ) * I)‖ ≤ 0.00000014815 := by
  have hl := lg_15
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.811045994939205473 39.811046016990734875 (-2.1119342) 0.00000004814 (-0.5151116223285) (-0.857123104656) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_16 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9967311847504):ℝ):ℂ) + (((-0.0807895094366):ℝ):ℂ) * I)‖ ≤ 0.00000015273 := by
  have hl := lg_16
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.7598267903612 40.7598268197632 (-3.060715) 0.00000005272 (-0.9967311847504) (-0.0807895094366) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_17 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6892341282868):ℝ):ℂ) + ((0.7245386921226:ℝ):ℂ) * I)‖ ≤ 0.00000013484 := by
  have hl := lg_17
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.651069355684596234 41.651069385086610935 2.3312278 0.00000003483 (-0.6892341282868) 0.7245386921226 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_18 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0797695855037:ℝ):ℂ) + ((0.9968133291788:ℝ):ℂ) * I)‖ ≤ 0.0000001489 := by
  have hl := lg_18
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.491355201367137928 42.49135522341866733 1.4909419 0.00000004889 0.0797695855037 0.9968133291788 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_19 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7673490056471:ℝ):ℂ) + ((0.6412296807949:ℝ):ℂ) * I)‖ ≤ 0.00000012901 := by
  have hl := lg_19
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.286197421261450703 43.286197443312994806 0.6960997 0.000000029 0.7673490056471 0.6412296807949 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_20 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9983206155815:ℝ):ℂ) + (((-0.0579305489794):ℝ):ℂ) * I)‖ ≤ 0.00000011739 := by
  have hl := lg_20
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.040260138231386509 44.04026016763340121 (-0.057963) 0.00000001738 0.9983206155815 (-0.0579305489794) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_21 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7142620401258:ℝ):ℂ) + (((-0.6998783737445):ℝ):ℂ) * I)‖ ≤ 0.00000011732 := by
  have hl := lg_21
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.757524345507657786 44.757524367559201889 (-0.7752272) 0.00000001731 0.7142620401258 (-0.6998783737445) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_22 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1114463285955:ℝ):ℂ) + (((-0.9937704543014):ℝ):ℂ) * I)‖ ≤ 0.00000015874 := by
  have hl := lg_22
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.441415091534753633 45.441415120936783035 (-1.459118) 0.00000005873 0.1114463285955 (-0.9937704543014) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_23 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5156850080486):ℝ):ℂ) + (((-0.8567782516305):ℝ):ℂ) * I)‖ ≤ 0.00000013225 := by
  have hl := lg_23
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.094900453088569566 46.094900482490613669 (-2.1126033) 0.00000003224 (-0.5156850080486) (-0.8567782516305) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_24 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9197628732674):ℝ):ℂ) + (((-0.3924745301499):ℝ):ℂ) * I)‖ ≤ 0.00000012382 := by
  have hl := lg_24
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.720569344659318964 46.720569374061333665 (-2.7382722) 0.00000002381 (-0.9197628732674) (-0.3924745301499) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_25 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9806965861423):ℝ):ℂ) + ((0.1955356888142:ℝ):ℂ) * I)‖ ≤ 0.00000015808 := by
  have hl := lg_25
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.320693486101573018 47.32069351550360242 2.944789 0.00000005807 (-0.9806965861423) 0.1955356888142 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_26 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7155484992084):ℝ):ℂ) + ((0.6985630574645:ℝ):ℂ) * I)‖ ≤ 0.00000016215 := by
  have hl := lg_26
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.8972771901679717 47.897277219570001102 2.3682053 0.00000006214 (-0.7155484992084) 0.6985630574645 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_27 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2402160125423):ℝ):ℂ) + ((0.9707194586064:ℝ):ℂ) * I)‖ ≤ 0.0000001203 := by
  have hl := lg_27
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.452097755665256892 48.452097777716800995 1.8133847 0.00000002029 (-0.2402160125423) 0.9707194586064 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_28 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2879182510844:ℝ):ℂ) + ((0.9576549904284:ℝ):ℂ) * I)‖ ≤ 0.00000016078 := by
  have hl := lg_28
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.986738488799838822 48.986738518201868224 1.278744 0.00000006077 0.2879182510844 0.9576549904284 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_29 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7228582422006:ℝ):ℂ) + ((0.6909963543193:ℝ):ℂ) * I)‖ ≤ 0.00000015333 := by
  have hl := lg_29
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.502615981345319092 49.502616010747363195 0.7628665 0.00000005332 0.7228582422006 0.6909963543193 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_30 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9652286154956:ℝ):ℂ) + ((0.2614071916158:ℝ):ℂ) * I)‖ ≤ 0.00000016451 := by
  have hl := lg_30
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.001002692529505473 50.001002721931534875 0.2644798 0.0000000645 0.9652286154956 0.2614071916158 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_2 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6847966911366):ℝ):ℂ) + ((0.7287341708655:ℝ):ℂ) * I)‖ ≤ 0.00000012544 := by
  have hl := lg_2
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.2412495889325 10.24124959632 2.325121 0.00000002543 (-0.6847966911366) 0.7287341708655 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_3 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8658080830332):ℝ):ℂ) + ((0.5003762217269:ℝ):ℂ) * I)‖ ≤ 0.00000014709 := by
  have hl := lg_3
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.2319965612306231 16.231996568618137875 2.6175594 0.00000004708 (-0.8658080830332) 0.5003762217269 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_4 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0621069764438):ℝ):ℂ) + (((-0.99806949832):ℝ):ℂ) * I)‖ ≤ 0.00000014369 := by
  have hl := lg_4
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.482499177865 20.48249919264 (-1.6329433) 0.00000004368 (-0.0621069764438) (-0.99806949832) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_5 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2157894214833:ℝ):ℂ) + ((0.9764399242021:ℝ):ℂ) * I)‖ ≤ 0.0000001346 := by
  have hl := lg_5
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.779445148532437975 23.77944516330745275 1.3532961 0.00000003459 0.2157894214833 0.9764399242021 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_6 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2282612663269:ℝ):ℂ) + (((-0.9735999149008):ℝ):ℂ) * I)‖ ≤ 0.00000013623 := by
  have hl := lg_6
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.4732461501631231 26.473246164938137875 (-1.3405049) 0.00000003622 0.2282612663269 (-0.9735999149008) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_7 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8886109638143):ℝ):ℂ) + ((0.4586616998233:ℝ):ℂ) * I)‖ ≤ 0.0000001235 := by
  have hl := lg_7
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.75082244461086005 28.7508224593858896 2.6651041 0.00000002349 (-0.8886109638143) 0.4586616998233 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_8 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7698579364804:ℝ):ℂ) + ((0.638215290978:ℝ):ℂ) * I)‖ ≤ 0.00000015308 := by
  have hl := lg_8
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.7237487667975 30.72374878896 0.6921778 0.00000005307 0.7698579364804 0.638215290978 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_9 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4992471929424:ℝ):ℂ) + (((-0.8664596011004):ℝ):ℂ) * I)‖ ≤ 0.00000011345 := by
  have hl := lg_9
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.4639931224612462 32.46399313723627575 (-1.0480666) 0.00000001344 0.4992471929424 (-0.8664596011004) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_10 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8593370166979):ℝ):ℂ) + (((-0.5114097101667):ℝ):ℂ) * I)‖ ≤ 0.00000012374 := by
  have hl := lg_10
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.020694737464937975 34.02069475962745275 (-2.6047682) 0.00000002373 (-0.8593370166979) (-0.5114097101667) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_11 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6437685168832):ℝ):ℂ) + ((0.7652202928921:ℝ):ℂ) * I)‖ ≤ 0.00000012317 := by
  have hl := lg_11
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.428902644073825075 35.428902666236354625 2.2702092 0.00000002316 (-0.6437685168832) 0.7652202928921 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_12 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5531829668558:ℝ):ℂ) + ((0.8330597848778:ℝ):ℂ) * I)‖ ≤ 0.0000001182 := by
  have hl := lg_12
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.7144957390956231 36.714495761258137875 0.9846161 0.00000001819 0.5531829668558 0.8330597848778 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_13 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9804590250355:ℝ):ℂ) + (((-0.1967234104689):ℝ):ℂ) * I)‖ ≤ 0.00000012407 := by
  have hl := lg_13
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.8971267449721175 37.89712676713464705 (-0.1980149) 0.00000002406 0.9804590250355 (-0.1967234104689) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_14 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2742754010791:ℝ):ℂ) + (((-0.9616511864303):ℝ):ℂ) * I)‖ ≤ 0.00000011264 := by
  have hl := lg_14
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.99207203354336005 38.9920720557058896 (-1.2929602) 0.00000001263 0.2742754010791 (-0.9616511864303) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_15 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6754196138655):ℝ):ℂ) + (((-0.7374336208675):ℝ):ℂ) * I)‖ ≤ 0.00000013333 := by
  have hl := lg_15
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.011441709763061075 40.011441731925590625 (-2.3123299) 0.00000003332 (-0.6754196138655) (-0.7374336208675) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_16 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9922854582684):ℝ):ℂ) + ((0.1239740653314:ℝ):ℂ) * I)‖ ≤ 0.00000013504 := by
  have hl := lg_16
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.96499835573 40.96499838528 3.0172988 0.00000003503 (-0.9922854582684) 0.1239740653314 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_17 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5233466478115):ℝ):ℂ) + ((0.8521198778442:ℝ):ℂ) * I)‖ ≤ 0.00000012238 := by
  have hl := lg_17
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.86072714306781235 41.860727172617827125 2.12157 0.00000002237 (-0.5233466478115) 0.8521198778442 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_18 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2895358932194:ℝ):ℂ) + ((0.9571671570513:ℝ):ℂ) * I)‖ ≤ 0.00000013888 := by
  have hl := lg_18
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.7052427113937462 42.70524273355627575 1.2770544 0.00000003887 0.2895358932194 0.9571671570513 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_19 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8878195338228:ℝ):ℂ) + ((0.4601917810682:ℝ):ℂ) * I)‖ ≤ 0.00000014461 := by
  have hl := lg_19
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.504085905662059325 43.50408592782460365 0.4782112 0.0000000446 0.8878195338228 0.4601917810682 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p775_20 : ‖exp (-((((((14775:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9611528767713:ℝ):ℂ) + (((-0.2760165710138):ℝ):ℂ) * I)‖ ≤ 0.00000012387 := by
  have hl := lg_20
  refine (ecis_approx ((((14775:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.261944326397437975 44.26194435594745275 (-0.2796472) 0.00000002386 0.9611528767713 (-0.2760165710138) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_2 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6332174057801):ℝ):ℂ) + ((0.773973976954:ℝ):ℂ) * I)‖ ≤ 0.00000015288 := by
  have hl := lg_2
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.3098711597822 10.3098711672192 2.2564995 0.00000005287 (-0.6332174057801) 0.773973976954 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_3 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8063771307291):ℝ):ℂ) + ((0.5914016596065:ℝ):ℂ) * I)‖ ≤ 0.00000014377 := by
  have hl := lg_3
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.340759177783031336 16.34075918522004621 2.5087967 0.00000004376 (-0.8063771307291) 0.5914016596065 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_4 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1980715250121):ℝ):ℂ) + (((-0.9801875692838):ℝ):ℂ) * I)‖ ≤ 0.00000011291 := by
  have hl := lg_4
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.6197423195644 20.6197423344384 (-1.7701864) 0.0000000129 (-0.1980715250121) (-0.9801875692838) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_5 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3679790459344:ℝ):ℂ) + ((0.9298340829165:ℝ):ℂ) * I)‖ ≤ 0.00000012692 := by
  have hl := lg_5
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.938779501811944666 23.93877951668595954 1.1939617 0.00000002691 0.3679790459344 0.9298340829165 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_6 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0528825474879:ℝ):ℂ) + (((-0.99860073912):ℝ):ℂ) * I)‖ ≤ 0.00000012374 := by
  have hl := lg_6
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.650630337565231336 26.65063035243924621 (-1.5178891) 0.00000002373 0.0528825474879 (-0.99860073912) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_7 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7843593606347):ℝ):ℂ) + ((0.6203066929681:ℝ):ℂ) * I)‖ ≤ 0.00000012831 := by
  have hl := lg_7
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.943467549315866828 28.943467564189896576 2.472459 0.0000000283 (-0.7843593606347) 0.6203066929681 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_8 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8840620551325:ℝ):ℂ) + ((0.4673695354588:ℝ):ℂ) * I)‖ ≤ 0.00000015657 := by
  have hl := lg_8
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.9296134793466 30.9296135016576 0.486313 0.00000005656 0.8840620551325 0.4673695354588 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_9 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3004882561871:ℝ):ℂ) + (((-0.9537855146172):ℝ):ℂ) * I)‖ ≤ 0.00000013456 := by
  have hl := lg_9
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.681518355566062672 32.68151837044009242 (-1.2655918) 0.00000003455 0.3004882561871 (-0.9537855146172) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_10 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9526781176605):ℝ):ℂ) + (((-0.3039809269019):ℝ):ℂ) * I)‖ ≤ 0.00000014802 := by
  have hl := lg_10
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.248650661594144666 34.24865068390515954 (-2.8327241) 0.00000004801 (-0.9526781176605) (-0.3039809269019) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_11 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4457583657511):ℝ):ℂ) + ((0.8951533272901:ℝ):ℂ) * I)‖ ≤ 0.00000015525 := by
  have hl := lg_11
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.666294276003659842 35.66629429831468959 2.0328176 0.00000005524 (-0.4457583657511) 0.8951533272901 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_12 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7394049032492:ℝ):ℂ) + ((0.6732610110878:ℝ):ℂ) * I)‖ ≤ 0.00000014575 := by
  have hl := lg_12
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.960501497347431336 36.96050151965844621 0.7386103 0.00000004574 0.7394049032492 0.6732610110878 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_13 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8995994353874:ℝ):ℂ) + (((-0.4367159899186):ℝ):ℂ) * I)‖ ≤ 0.00000011181 := by
  have hl := lg_13
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.1510567312836058 38.151056753594635548 (-0.4519449) 0.0000000118 0.8995994353874 (-0.4367159899186) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_14 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0165686686272:ℝ):ℂ) + (((-0.9998627301884):ℝ):ℂ) * I)‖ ≤ 0.00000013399 := by
  have hl := lg_14
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.253338709098066828 39.253338731409096576 (-1.5542269) 0.00000003398 0.0165686686272 (-0.9998627301884) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_15 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8466352499999):ℝ):ℂ) + (((-0.5321736120721):ℝ):ℂ) * I)‖ ≤ 0.00000015884 := by
  have hl := lg_15
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.279538679594976002 40.27953870190600575 (-2.5804268) 0.00000005883 (-0.8466352499999) (-0.5321736120721) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_16 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9215353391248):ℝ):ℂ) + ((0.3882944998307:ℝ):ℂ) * I)‖ ≤ 0.00000011863 := by
  have hl := lg_16
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.2394846391288 41.2394846688768 2.7428125 0.00000001862 (-0.9215353391248) 0.3882944998307 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_17 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2670066529528):ℝ):ℂ) + ((0.9636946857162:ℝ):ℂ) * I)‖ ≤ 0.00000014353 := by
  have hl := lg_17
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.141215264026439316 42.14121529377445419 1.8410819 0.00000004352 (-0.2670066529528) 0.9636946857162 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_18 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5479308575193:ℝ):ℂ) + ((0.8365236251166:ℝ):ℂ) * I)‖ ≤ 0.00000013492 := by
  have hl := lg_18
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.991389515348262672 42.99138953765929242 0.9909076 0.00000003491 0.5479308575193 0.8365236251166 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_19 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9826199309793:ℝ):ℂ) + ((0.1856288534747:ℝ):ℂ) * I)‖ ≤ 0.00000013659 := by
  have hl := lg_19
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.795585364522333022 43.795585386833377644 0.1867118 0.00000003658 0.9826199309793 0.1856288534747 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p874_20 : ‖exp (-((((((14874:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.838525638771:ℝ):ℂ) + (((-0.5448621413933):ℝ):ℂ) * I)‖ ≤ 0.0000001289 := by
  have hl := lg_20
  refine (ecis_approx ((((14874:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.558521821376344666 44.55852185112435954 (-0.5762247) 0.00000002889 0.838525638771 (-0.5448621413933) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_2 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5598524143825):ℝ):ℂ) + ((0.8285923449446:ℝ):ℂ) * I)‖ ≤ 0.00000012679 := by
  have hl := lg_2
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.4013665875818 10.4013665950848 2.165004 0.00000002678 (-0.5598524143825) 0.8285923449446 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_3 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7124500816459):ℝ):ℂ) + ((0.7017227950814:ℝ):ℂ) * I)‖ ≤ 0.0000001217 := by
  have hl := lg_3
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.485775999852908984 16.48577600735592399 2.3637799 0.00000002169 (-0.7124500816459) 0.7017227950814 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_4 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.373130541558):ℝ):ℂ) + (((-0.9277788523963):ℝ):ℂ) * I)‖ ≤ 0.00000014639 := by
  have hl := lg_4
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.8027331751636 20.8027331901696 (-1.9531773) 0.00000004638 (-0.373130541558) (-0.9277788523963) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_5 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5557629562788:ℝ):ℂ) + ((0.8313408064255:ℝ):ℂ) * I)‖ ≤ 0.00000012255 := by
  have hl := lg_5
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.151225306184620254 24.15122532119063526 0.9815159 0.00000002254 0.5557629562788 0.8313408064255 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_6 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1825752308957):ℝ):ℂ) + (((-0.9831918861863):ℝ):ℂ) * I)‖ ≤ 0.0000001413 := by
  have hl := lg_6
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.887142587434708984 26.88714260244072399 (-1.7544014) 0.00000004129 (-0.1825752308957) (-0.9831918861863) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_7 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6010405831699):ℝ):ℂ) + ((0.7992185041468:ℝ):ℂ) * I)‖ ≤ 0.00000014699 := by
  have hl := lg_7
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.200327688922542532 29.200327703928572544 2.2155988 0.00000004698 (-0.6010405831699) 0.7992185041468 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_8 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9776484684498:ℝ):ℂ) + ((0.2102462178915:ℝ):ℂ) * I)‖ ≤ 0.00000014937 := by
  have hl := lg_8
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.2040997627454 31.2040997852544 0.2118268 0.00000004936 0.9776484684498 0.2102462178915 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_9 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0151702448638:ℝ):ℂ) + (((-0.9998849252142):ℝ):ℂ) * I)‖ ≤ 0.00000013621 := by
  have hl := lg_9
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.971551999705817968 32.97155201471184798 (-1.5556255) 0.0000000362 0.0151702448638 (-0.9998849252142) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_10 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999878607743):ℝ):ℂ) + (((-0.0049272333524):ℝ):ℂ) * I)‖ ≤ 0.00000014215 := by
  have hl := lg_10
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.552591893766420254 34.55259191627543526 (-3.1366654) 0.00000004214 (-0.9999878607743) (-0.0049272333524) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_11 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1449862475794):ℝ):ℂ) + ((0.9894336703449:ℝ):ℂ) * I)‖ ≤ 0.00000013136 := by
  have hl := lg_11
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.982816451910106198 35.98281647441913621 1.7162954 0.00000003135 (-0.1449862475794) 0.9894336703449 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_12 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9168804144184:ℝ):ℂ) + ((0.399162004274:ℝ):ℂ) * I)‖ ≤ 0.00000015446 := by
  have hl := lg_12
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.288509175016508984 37.28850919752552399 0.4106027 0.00000005445 0.9168804144184 0.399162004274 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_13 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7034771161007:ℝ):ℂ) + (((-0.7107179096678):ℝ):ℂ) * I)‖ ≤ 0.00000012581 := by
  have hl := lg_13
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.4896300463655902 38.489630068874620212 (-0.7905182) 0.0000000258 0.7034771161007 (-0.7107179096678) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_14 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3257322115195):ℝ):ℂ) + (((-0.9454620703003):ℝ):ℂ) * I)‖ ≤ 0.00000015595 := by
  have hl := lg_14
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.601694276504342532 39.601694299013372544 (-1.9025824) 0.00000005594 (-0.3257322115195) (-0.9454620703003) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p006_15 : ‖exp (-((((((15006:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9793241563579):ℝ):ℂ) + (((-0.2022972971982):ℝ):ℂ) * I)‖ ≤ 0.00000013705 := by
  have hl := lg_15
  refine (ecis_approx ((((15006:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.637001306037529238 40.63700132854655925 (-2.9378895) 0.00000003704 (-0.9793241563579) (-0.2022972971982) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_2 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4818040159255):ℝ):ℂ) + ((0.8762790025058:ℝ):ℂ) * I)‖ ≤ 0.00000010861 := by
  have hl := lg_2
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.4928620153814 10.4928620229504 2.0735086 0.0000000086 (-0.4818040159255) 0.8762790025058 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_3 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6035665370169):ℝ):ℂ) + ((0.7973126334012:ℝ):ℂ) * I)‖ ≤ 0.00000010797 := by
  have hl := lg_3
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.630792821922786632 16.63079282949180177 2.2187631 0.00000000796 (-0.6035665370169) 0.7973126334012 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_4 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5357297744133):ℝ):ℂ) + (((-0.8443894888019):ℝ):ℂ) * I)‖ ≤ 0.00000012438 := by
  have hl := lg_4
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.9857240307628 20.9857240459008 (-2.1361681) 0.00000002437 (-0.5357297744133) (-0.8443894888019) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_5 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7185576952824:ℝ):ℂ) + ((0.695467352613:ℝ):ℂ) * I)‖ ≤ 0.00000011818 := by
  have hl := lg_5
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.363671110557295842 24.36367112569531098 0.7690701 0.00000001817 0.7185576952824 0.695467352613 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_6 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.407867531122):ℝ):ℂ) + (((-0.9130411146564):ℝ):ℂ) * I)‖ ≤ 0.00000012374 := by
  have hl := lg_6
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.123654837304186632 27.12365485244220177 (-1.9909136) 0.00000002373 (-0.407867531122) (-0.9130411146564) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_7 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3782844939759):ℝ):ℂ) + ((0.9256893872215:ℝ):ℂ) * I)‖ ≤ 0.00000010778 := by
  have hl := lg_7
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.457187828529218236 29.457187843667248512 1.9587387 0.00000000777 (-0.3782844939759) 0.9256893872215 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_8 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9980375357437:ℝ):ℂ) + (((-0.0626185056252):ℝ):ℂ) * I)‖ ≤ 0.00000013297 := by
  have hl := lg_8
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.4785860461442 31.4785860688512 (-0.0626595) 0.00000003296 0.9980375357437 (-0.0626185056252) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_9 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2714148638747):ℝ):ℂ) + (((-0.9624624520814):ℝ):ℂ) * I)‖ ≤ 0.0000001231 := by
  have hl := lg_9
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.261585643845573264 33.26158565898360354 (-1.8456591) 0.00000002309 (-0.2714148638747) (-0.9624624520814) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_10 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9556274212066):ℝ):ℂ) + ((0.2945780569201:ℝ):ℂ) * I)‖ ≤ 0.00000011715 := by
  have hl := lg_10
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.856533125938695842 34.85653314864571098 2.8425787 0.00000001714 (-0.9556274212066) 0.2945780569201 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_11 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1701906385257:ℝ):ℂ) + ((0.9854111560959:ℝ):ℂ) * I)‖ ≤ 0.00000011528 := by
  have hl := lg_11
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.299338627816552554 36.29933865052358283 1.3997732 0.00000001527 0.1701906385257 0.9854111560959 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_12 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9965909716626:ℝ):ℂ) + ((0.0825011224203:ℝ):ℂ) * I)‖ ≤ 0.00000013233 := by
  have hl := lg_12
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.616516852685586632 37.61651687539260177 0.082595 0.00000003232 0.9965909716626 0.0825011224203 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_13 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4274812902146:ℝ):ℂ) + (((-0.9040241957583):ℝ):ℂ) * I)‖ ≤ 0.00000014109 := by
  have hl := lg_13
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.8282033614475746 38.828203384154604876 (-1.1290915) 0.00000004108 0.4274812902146 (-0.9040241957583) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_14 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6289031789257):ℝ):ℂ) + (((-0.7774836278164):ℝ):ℂ) * I)‖ ≤ 0.00000012356 := by
  have hl := lg_14
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.950049843910618236 39.950049866617648512 (-2.250938) 0.00000002355 (-0.6289031789257) (-0.7774836278164) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p138_15 : ‖exp (-((((((15138:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9882022859831):ℝ):ℂ) + ((0.1531543064679:ℝ):ℂ) * I)‖ ≤ 0.00000011779 := by
  have hl := lg_15
  refine (ecis_approx ((((15138:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.994463932480082474 40.99446395518711275 2.9878332 0.00000001778 (-0.9882022859831) 0.1531543064679 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_2 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3709438467609):ℝ):ℂ) + ((0.9286552980237:ℝ):ℂ) * I)‖ ≤ 0.00000014808 := by
  have hl := lg_2
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.6155490662945 10.615549073952 1.9508215 0.00000004807 (-0.3709438467609) 0.9286552980237 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_3 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4381255508521):ℝ):ℂ) + ((0.8989137899078:ℝ):ℂ) * I)‖ ≤ 0.00000012458 := by
  have hl := lg_3
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.82524719697103166 16.825247204628546975 2.0243087 0.00000002457 (-0.4381255508521) 0.8989137899078 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_4 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7248012512541):ℝ):ℂ) + (((-0.6889580147964):ℝ):ℂ) * I)‖ ≤ 0.00000012638 := by
  have hl := lg_4
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.231098132589 21.231098147904 (-2.3815422) 0.00000002637 (-0.7248012512541) (-0.6889580147964) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_5 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8850478188605:ℝ):ℂ) + ((0.4655001163591:ℝ):ℂ) * I)‖ ≤ 0.00000010777 := by
  have hl := lg_5
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.648541620966110835 24.64854163628112615 0.4841996 0.00000000776 0.8850478188605 0.4655001163591 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_6 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6722609969218):ℝ):ℂ) + (((-0.7403142251761):ℝ):ℂ) * I)‖ ≤ 0.00000014988 := by
  have hl := lg_6
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.44079626326553166 27.440796278580546975 (-2.308055) 0.00000004987 (-0.6722609969218) (-0.7403142251761) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_7 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0435025402907):ℝ):ℂ) + ((0.9990533163891:ℝ):ℂ) * I)‖ ≤ 0.00000011109 := by
  have hl := lg_7
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.80161392481998793 29.80161394013501856 1.6143126 0.00000001108 (-0.0435025402907) 0.9990533163891 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_8 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9086650748513:ℝ):ℂ) + (((-0.4175257857252):ℝ):ℂ) * I)‖ ≤ 0.00000013703 := by
  have hl := lg_8
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.8466471988835 31.846647221856 (-0.4307207) 0.00000003702 0.9086650748513 (-0.4175257857252) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_9 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6160919977248):ℝ):ℂ) + (((-0.7876742031615):ℝ):ℂ) * I)‖ ≤ 0.00000014197 := by
  have hl := lg_9
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.65049439394206332 33.65049440925709395 (-2.2345679) 0.00000004196 (-0.6160919977248) (-0.7876742031615) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_10 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7605921917772):ℝ):ℂ) + ((0.6492299421399:ℝ):ℂ) * I)‖ ≤ 0.00000015583 := by
  have hl := lg_10
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.264090687260610835 35.26409071023312615 2.4350211 0.00000005582 (-0.7605921917772) 0.6492299421399 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_11 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5608818834801:ℝ):ℂ) + ((0.8278958345008:ℝ):ℂ) * I)‖ ≤ 0.00000015213 := by
  have hl := lg_11
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.723766090963832895 36.723766113936363525 0.9753457 0.00000005212 0.5608818834801 0.8278958345008 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_12 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9368678076498:ℝ):ℂ) + (((-0.3496837299466):ℝ):ℂ) * I)‖ ≤ 0.00000011353 := by
  have hl := lg_12
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.05634532956003166 38.056345352532546975 (-0.3572335) 0.00000001352 0.9368678076498 (-0.3496837299466) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_13 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0122909637227):ℝ):ℂ) + (((-0.9999244632524):ℝ):ℂ) * I)‖ ≤ 0.00000014551 := by
  have hl := lg_13
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.2821993975802355 39.28219942055276613 (-1.5830876) 0.0000000455 (-0.0122909637227) (-0.9999244632524) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_14 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9116391526443):ℝ):ℂ) + (((-0.4109915512941):ℝ):ℂ) * I)‖ ≤ 0.00000015198 := by
  have hl := lg_14
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.41716299111448793 40.41716301408701856 (-2.7180512) 0.00000005197 (-0.9116391526443) (-0.4109915512941) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p315_15 : ‖exp (-((((((15315:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8062065369578):ℝ):ℂ) + ((0.5916341941731:ℝ):ℂ) * I)‖ ≤ 0.00000013233 := by
  have hl := lg_15
  refine (ecis_approx ((((15315:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.473788817937142495 41.473788840909673125 2.5085083 0.00000003232 (-0.8062065369578) 0.5916341941731 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_2 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2545072814431):ℝ):ℂ) + ((0.9670708576372:ℝ):ℂ) * I)‖ ≤ 0.00000011061 := by
  have hl := lg_2
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.7382361172076 10.7382361249536 1.8281345 0.0000000106 (-0.2545072814431) 0.9670708576372 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_3 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2561700727047):ℝ):ℂ) + ((0.9666317260721:ℝ):ℂ) * I)‖ ≤ 0.00000014953 := by
  have hl := lg_3
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.019701572019276688 17.01970157976529218 1.8298543 0.00000004952 (-0.2561700727047) 0.9666317260721 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_4 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8704520838275):ℝ):ℂ) + (((-0.4922531560815):ℝ):ℂ) * I)‖ ≤ 0.00000012838 := by
  have hl := lg_4
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.4764722344152 21.4764722499072 (-2.6269163) 0.00000002837 (-0.8704520838275) (-0.4922531560815) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_5 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.980199644518:ℝ):ℂ) + ((0.1980117594661:ℝ):ℂ) * I)‖ ≤ 0.00000011816 := by
  have hl := lg_5
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.933412131374925828 24.93341214686694132 0.1993291 0.00000001815 0.980199644518 0.1980117594661 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_6 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8696042199941):ℝ):ℂ) + (((-0.4937494308663):ℝ):ℂ) * I)‖ ≤ 0.00000013951 := by
  have hl := lg_6
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.757937689226876688 27.75793770471889218 (-2.6251965) 0.0000000395 (-0.8696042199941) (-0.4937494308663) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_7 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2963892749638:ℝ):ℂ) + ((0.9550672215538:ℝ):ℂ) * I)‖ ≤ 0.0000001148 := by
  have hl := lg_7
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.146040021110757624 30.146040036602788608 1.2698865 0.00000001479 0.2963892749638 0.9550672215538 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_8 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6975800753607:ℝ):ℂ) + (((-0.7165068307139):ℝ):ℂ) * I)‖ ≤ 0.00000013898 := by
  have hl := lg_8
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.2147083516228 32.2147083748608 (-0.7987818) 0.00000003897 0.6975800753607 (-0.7165068307139) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_9 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8687537345981):ℝ):ℂ) + (((-0.4952443321583):ℝ):ℂ) * I)‖ ≤ 0.00000012365 := by
  have hl := lg_9
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.039403144038553376 34.03940315953058436 (-2.6234766) 0.00000002364 (-0.8687537345981) (-0.4952443321583) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_10 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.440959348847):ℝ):ℂ) + ((0.8975270762825:ℝ):ℂ) * I)‖ ≤ 0.00000012876 := by
  have hl := lg_10
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.671648248582525828 35.67164827182054132 2.0274636 0.00000002875 (-0.440959348847) 0.8975270762825 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_11 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8520441789884:ℝ):ℂ) + ((0.5234698817047:ℝ):ℂ) * I)‖ ≤ 0.00000013429 := by
  have hl := lg_11
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.148193554111113236 37.14819357734914422 0.5509183 0.00000003428 0.8520441789884 0.5234698817047 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_12 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6988112915805:ℝ):ℂ) + (((-0.7153060734815):ℝ):ℂ) * I)‖ ≤ 0.00000013666 := by
  have hl := lg_12
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.496173806434476688 38.49617382967249218 (-0.797062) 0.00000003665 0.6988112915805 (-0.7153060734815) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_13 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.449573022145):ℝ):ℂ) + (((-0.8932435825434):ℝ):ℂ) * I)‖ ≤ 0.00000011389 := by
  have hl := lg_13
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.7361954337128964 39.736195456950927384 (-2.0370836) 0.00000001388 (-0.449573022145) (-0.8932435825434) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_14 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9990509053878):ℝ):ℂ) + ((0.0435578679137:ℝ):ℂ) * I)‖ ≤ 0.00000011195 := by
  have hl := lg_14
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.884276138318357624 40.884276161556388608 3.098021 0.00000001194 (-0.9990509053878) 0.0435578679137 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p492_15 : ‖exp (-((((((15492:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4425022630366):ℝ):ℂ) + ((0.8967673874551:ℝ):ℂ) * I)‖ ≤ 0.00000014688 := by
  have hl := lg_15
  refine (ecis_approx ((((15492:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.953113703394202516 41.9531137266322335 2.0291834 0.00000004687 (-0.4425022630366) 0.8967673874551 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_2 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0936181804047):ℝ):ℂ) + ((0.9956081740812:ℝ):ℂ) * I)‖ ≤ 0.00000014528 := by
  have hl := lg_2
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.9018188517584 10.9018188596224 1.6645518 0.00000004527 (-0.0936181804047) 0.9956081740812 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_3 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0002145267932:ℝ):ℂ) + ((0.999999976989:ℝ):ℂ) * I)‖ ≤ 0.00000014947 := by
  have hl := lg_3
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.278974072083603392 17.27897407994761912 1.5705818 0.00000004946 0.0002145267932 0.999999976989 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_4 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9824712897568):ℝ):ℂ) + (((-0.1864139599459):ℝ):ℂ) * I)‖ ≤ 0.00000011804 := by
  have hl := lg_4
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.8036377035168 21.8036377192448 (-2.9540818) 0.00000001803 (-0.9824712897568) (-0.1864139599459) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_5 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9837543602098:ℝ):ℂ) + (((-0.1795198004909):ℝ):ℂ) * I)‖ ≤ 0.00000015015 := by
  have hl := lg_5
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.313239478586679152 25.31323949431469488 (-0.1804983) 0.00000005014 0.9837543602098 (-0.1795198004909) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_6 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9956282338857):ℝ):ℂ) + (((-0.0934046005411):ℝ):ℂ) * I)‖ ≤ 0.00000011087 := by
  have hl := lg_6
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.180792923842003392 28.18079293957001912 (-3.0480517) 0.00000001086 (-0.9956282338857) (-0.0934046005411) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_7 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6890262686142:ℝ):ℂ) + ((0.72473636666:ℝ):ℂ) * I)‖ ≤ 0.00000011975 := by
  have hl := lg_7
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.605274816165117216 30.605274831893148672 0.8106517 0.00000001974 0.6890262686142 0.72473636666 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_8 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2775724369121:ℝ):ℂ) + (((-0.9607047112754):ℝ):ℂ) * I)‖ ≤ 0.00000014298 := by
  have hl := lg_8
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.7054565552752 32.7054565788672 (-1.28953) 0.00000004297 0.2775724369121 (-0.9607047112754) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_9 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999999076563):ℝ):ℂ) + ((0.0004289532724:ℝ):ℂ) * I)‖ ≤ 0.00000011683 := by
  have hl := lg_9
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.557948144167206784 34.55794815989523824 3.1411637 0.00000001682 (-0.9999999076563) 0.0004289532724 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_10 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0866340876102:ℝ):ℂ) + ((0.9962401993816:ℝ):ℂ) * I)‖ ≤ 0.00000011275 := by
  have hl := lg_10
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.215058330345079152 36.21505835393709488 1.4840535 0.00000001274 0.0866340876102 0.9962401993816 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_11 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9998877269884:ℝ):ℂ) + (((-0.0149844391921):ℝ):ℂ) * I)‖ ≤ 0.00000011884 := by
  have hl := lg_11
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.714096838307487024 37.71409686189951848 (-0.014985) 0.00000001883 0.9998877269884 (-0.0149844391921) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_12 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1862032876599:ℝ):ℂ) + (((-0.9825112394597):ℝ):ℂ) * I)‖ ≤ 0.00000015613 := by
  have hl := lg_12
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.082611775600403392 39.08261179919241912 (-1.3834999) 0.00000005612 0.1862032876599 (-0.9825112394597) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_13 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8779749392297):ℝ):ℂ) + (((-0.4787065969778):ℝ):ℂ) * I)‖ ≤ 0.0000001612 := by
  have hl := lg_13
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.3415234818897776 40.341523505481809056 (-2.6424117) 0.00000006119 (-0.8779749392297) (-0.4787065969778) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_14 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7860588362109):ℝ):ℂ) + ((0.6181516852445:ℝ):ℂ) * I)‖ ≤ 0.00000014127 := by
  have hl := lg_14
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.507093667923517216 41.507093691515548672 2.4752035 0.00000004126 (-0.7860588362109) 0.6181516852445 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p728_15 : ‖exp (-((((((15728:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1797307396566:ℝ):ℂ) + ((0.9837158437386:ℝ):ℂ) * I)‖ ≤ 0.00000012402 := by
  have hl := lg_15
  refine (ecis_approx ((((15728:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.592213550670282544 42.592213574262314 1.3900836 0.00000002401 0.1797307396566 0.9837158437386 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p964_2 : ‖exp (-((((((15964:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0697705959672:ℝ):ℂ) + ((0.9975630626373:ℝ):ℂ) * I)‖ ≤ 0.00000012806 := by
  have hl := lg_2
  refine (ecis_approx ((((15964:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.0654015863092 11.0654015942912 1.500969 0.00000002805 0.0697705959672 0.9975630626373 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p964_3 : ‖exp (-((((((15964:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2565847859251:ℝ):ℂ) + ((0.9665217264147:ℝ):ℂ) * I)‖ ≤ 0.00000014941 := by
  have hl := lg_3
  refine (ecis_approx ((((15964:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.538246572147930096 17.53824658012994606 1.3113093 0.0000000494 0.2565847859251 0.9665217264147 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p964_4 : ‖exp (-((((((15964:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9902641276976):ℝ):ℂ) + ((0.1392011385933:ℝ):ℂ) * I)‖ ≤ 0.00000015611 := by
  have hl := lg_4
  refine (ecis_approx ((((15964:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.1308031726184 22.1308031885824 3.001938 0.0000000561 (-0.9902641276976) 0.1392011385933 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p964_5 : ‖exp (-((((((15964:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8470821118794:ℝ):ℂ) + (((-0.5314620360232):ℝ):ℂ) * I)‖ ≤ 0.00000011306 := by
  have hl := lg_5
  refine (ecis_approx ((((15964:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.693066825798432476 25.69306684176244844 (-0.5603256) 0.00000001305 0.8470821118794 (-0.5314620360232) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p964_6 : ‖exp (-((((((15964:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9462643323492):ℝ):ℂ) + ((0.3233942070135:ℝ):ℂ) * I)‖ ≤ 0.00000013854 := by
  have hl := lg_6
  refine (ecis_approx ((((15964:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.603648158457130096 28.60364817442114606 2.8122784 0.00000003853 (-0.9462643323492) 0.3233942070135 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p964_7 : ‖exp (-((((((15964:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9388859181618:ℝ):ℂ) + ((0.3442284600052:ℝ):ℂ) * I)‖ ≤ 0.00000012469 := by
  have hl := lg_7
  refine (ecis_approx ((((15964:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.064509611219476808 31.064509627183508736 0.3514169 0.00000002468 0.9388859181618 0.3442284600052 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p964_8 : ‖exp (-((((((15964:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2079531278646):ℝ):ℂ) + (((-0.9781387920998):ℝ):ℂ) * I)‖ ≤ 0.00000014699 := by
  have hl := lg_8
  refine (ecis_approx ((((15964:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.1962047589276 33.1962047828736 (-1.7802782) 0.00000004698 (-0.2079531278646) (-0.9781387920998) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p964_9 : ‖exp (-((((((15964:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8683285448397):ℝ):ℂ) + ((0.4959894536479:ℝ):ℂ) * I)‖ ≤ 0.0000001172 := by
  have hl := lg_9
  refine (ecis_approx ((((15964:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.076493144295860192 35.07649316025989212 2.6226187 0.00000001719 (-0.8683285448397) 0.4959894536479 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p964_10 : ‖exp (-((((((15964:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5892683201098:ℝ):ℂ) + ((0.8079374028444:ℝ):ℂ) * I)‖ ≤ 0.00000013098 := by
  have hl := lg_10
  refine (ecis_approx ((((15964:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.758468412107632476 36.75846843605364844 0.9406434 0.00000003097 0.5892683201098 0.8079374028444 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_2 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2312964201044:ℝ):ℂ) + ((0.9728833260195:ℝ):ℂ) * I)‖ ≤ 0.00000011462 := by
  have hl := lg_2
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.22898432086 11.22898432896 1.3373863 0.00000001461 0.2312964201044 0.9728833260195 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_3 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4958032493875:ℝ):ℂ) + ((0.8684348783281:ℝ):ℂ) * I)‖ ≤ 0.00000014934 := by
  have hl := lg_3
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.7975190722122568 17.797519080312273 1.0520368 0.00000004933 0.4958032493875 0.8684348783281 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_4 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8930039320626):ℝ):ℂ) + ((0.4500488609163:ℝ):ℂ) * I)‖ ≤ 0.00000012922 := by
  have hl := lg_4
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.45796864172 22.45796865792 2.6747726 0.00000002921 (-0.8930039320626) 0.4500488609163 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_5 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.589664461739:ℝ):ℂ) + (((-0.8076483285205):ℝ):ℂ) * I)‖ ≤ 0.00000015572 := by
  have hl := lg_5
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.0728941730101858 26.072894189210202 (-0.940153) 0.00000005571 0.589664461739 (-0.8076483285205) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_6 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7302082961952):ℝ):ℂ) + ((0.68322459275:ℝ):ℂ) * I)‖ ≤ 0.00000014284 := by
  have hl := lg_6
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.0265033930722568 29.026503409272273 2.3894231 0.00000004283 (-0.7302082961952) 0.68322459275 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_7 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9941932786068:ℝ):ℂ) + (((-0.1076091295992):ℝ):ℂ) * I)‖ ≤ 0.00000012964 := by
  have hl := lg_7
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.5237444062738364 31.5237444224738688 (-0.1078179) 0.00000002963 0.9941932786068 (-0.1076091295992) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_8 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6443936398775):ℝ):ℂ) + (((-0.7646939498055):ℝ):ℂ) * I)‖ ≤ 0.000000151 := by
  have hl := lg_8
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.68695296258 33.68695298688 (-2.2710264) 0.00000005099 (-0.6443936398775) (-0.7646939498055) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_9 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5083583619079):ℝ):ℂ) + ((0.8611456182735:ℝ):ℂ) * I)‖ ≤ 0.00000011756 := by
  have hl := lg_9
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.5950381444245136 35.595038160624546 2.1040737 0.00000001755 (-0.5083583619079) 0.8611456182735 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_10 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9221348711682:ℝ):ℂ) + ((0.3868685556821:ℝ):ℂ) * I)‖ ≤ 0.00000014922 := by
  have hl := lg_10
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.3018784938701858 37.301878518170202 0.3972333 0.00000004921 0.9221348711682 0.3868685556821 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_11 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4114138452374:ℝ):ℂ) + (((-0.911448653489):ℝ):ℂ) * I)‖ ≤ 0.00000013639 := by
  have hl := lg_11
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.8459034067002346 38.845903431000267 (-1.1467916) 0.00000003638 0.4114138452374 (-0.911448653489) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_12 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8335923750899):ℝ):ℂ) + (((-0.5523800794088):ℝ):ℂ) * I)‖ ≤ 0.00000012916 := by
  have hl := lg_12
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.2554877139322568 40.255487738232273 (-2.5563759) 0.00000002915 (-0.8335923750899) (-0.5523800794088) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_13 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7573995615738):ℝ):ℂ) + ((0.652951685879:ℝ):ℂ) * I)‖ ≤ 0.0000001523 := by
  have hl := lg_13
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.55217957824354 41.5521796025435724 2.4301176 0.00000005229 (-0.7573995615738) 0.652951685879 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_14 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3346444741481:ℝ):ℂ) + ((0.9423444571504:ℝ):ℂ) * I)‖ ≤ 0.00000012314 := by
  have hl := lg_14
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.7527287271338364 42.7527287514338688 1.2295684 0.00000002313 0.3346444741481 0.9423444571504 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p2_15 : ‖exp (-((((((16200:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9937475229241:ℝ):ℂ) + ((0.1116506188166:ℝ):ℂ) * I)‖ ≤ 0.00000011928 := by
  have hl := lg_15
  refine (ecis_approx ((((16200:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.8704132452224426 43.870413269522475 0.1118839 0.00000001927 0.9937475229241 0.1116506188166 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_2 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3866467035476:ℝ):ℂ) + ((0.9222279146912:ℝ):ℂ) * I)‖ ≤ 0.00000014928 := by
  have hl := lg_2
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.3925670554108 11.3925670636288 1.1738036 0.00000004927 0.3866467035476 0.9222279146912 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_3 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.701878999438:ℝ):ℂ) + ((0.7122961955169:ℝ):ℂ) * I)‖ ≤ 0.00000014928 := by
  have hl := lg_3
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.056791572276583504 18.05679158049459994 0.7927643 0.00000004927 0.701878999438 0.7122961955169 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_4 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.701008581953):ℝ):ℂ) + ((0.7131528363573:ℝ):ℂ) * I)‖ ≤ 0.00000011791 := by
  have hl := lg_4
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.7851341108216 22.7851341272576 2.3476071 0.0000000179 (-0.701008581953) 0.7131528363573 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_5 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2481945352917:ℝ):ℂ) + (((-0.9687102108739):ℝ):ℂ) * I)‖ ≤ 0.00000010851 := by
  have hl := lg_5
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.452721520221939124 26.45272153665795556 (-1.3199803) 0.0000000085 0.2481945352917 (-0.9687102108739) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_6 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3855202336121):ℝ):ℂ) + ((0.9226993819618:ℝ):ℂ) * I)‖ ≤ 0.00000010824 := by
  have hl := lg_6
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.449358627687383504 29.44935864412339994 1.9665679 0.00000000823 (-0.3855202336121) 0.9226993819618 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_7 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8434877737806:ℝ):ℂ) + (((-0.5371483738062):ℝ):ℂ) * I)‖ ≤ 0.00000013458 := by
  have hl := lg_7
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.982979201328195992 31.982979217764228864 (-0.5670527) 0.00000003457 0.8434877737806 (-0.5371483738062) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_8 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9287321078011):ℝ):ℂ) + (((-0.3707514959944):ℝ):ℂ) * I)‖ ≤ 0.000000155 := by
  have hl := lg_8
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.1777011662324 34.1777011908864 (-2.7617746) 0.00000005499 (-0.9287321078011) (-0.3707514959944) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_9 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.014731840285):ℝ):ℂ) + ((0.9998914805526:ℝ):ℂ) * I)‖ ≤ 0.00000011793 := by
  have hl := lg_9
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.113583144553167008 36.11358316098919988 1.5855287 0.00000001792 (-0.014731840285) 0.9998914805526 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_10 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9893351966234:ℝ):ℂ) + (((-0.1456566810075):ℝ):ℂ) * I)‖ ≤ 0.00000015722 := by
  have hl := lg_10
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.845288575632739124 37.84528860028675556 (-0.1461767) 0.00000005721 0.9893351966234 (-0.1456566810075) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_11 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1414228595755):ℝ):ℂ) + (((-0.9899492788971):ℝ):ℂ) * I)‖ ≤ 0.0000001522 := by
  have hl := lg_11
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.411806690896608388 39.41180671555064126 (-1.7126949) 0.00000005219 (-0.1414228595755) (-0.9899492788971) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_12 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999992540501):ℝ):ℂ) + ((0.0012211529828:ℝ):ℂ) * I)‖ ≤ 0.00000015751 := by
  have hl := lg_12
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.841925683098183504 40.84192570775219994 3.1403715 0.0000000575 (-0.9999992540501) 0.0012211529828 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_13 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.251271011614):ℝ):ℂ) + ((0.9679167726211:ℝ):ℂ) * I)‖ ≤ 0.00000012385 := by
  have hl := lg_13
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.1575076264204212 42.157507651074454072 1.8247895 0.00000002384 (-0.251271011614) 0.9679167726211 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_14 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8215049918701:ℝ):ℂ) + ((0.5702013226331:ℝ):ℂ) * I)‖ ≤ 0.00000013115 := by
  have hl := lg_14
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.375546256738995992 43.375546281393028864 0.6067509 0.00000003114 0.8215049918701 0.5702013226331 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p436_15 : ‖exp (-((((((16436:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8642111298604:ℝ):ℂ) + (((-0.5031293303172):ℝ):ℂ) * I)‖ ≤ 0.00000015777 := by
  have hl := lg_15
  refine (ecis_approx ((((16436:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.509513092498522628 44.5095131171525555 (-0.527216) 0.00000005776 0.8642111298604 (-0.5031293303172) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_2 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5316737279398:ℝ):ℂ) + ((0.8469492588217:ℝ):ℂ) * I)‖ ≤ 0.00000012441 := by
  have hl := lg_2
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.5561497899616 11.5561497982976 1.0102208 0.0000000244 0.5316737279398 0.8469492588217 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_3 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8610365928267:ℝ):ℂ) + ((0.5085430029147:ℝ):ℂ) * I)‖ ≤ 0.00000014921 := by
  have hl := lg_3
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.316064072340910208 18.31606408067692688 0.5334918 0.0000000492 0.8610365928267 0.5085430029147 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_4 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4346460940373):ℝ):ℂ) + ((0.9006013396248:ℝ):ℂ) * I)‖ ≤ 0.00000014881 := by
  have hl := lg_4
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.1122995799232 23.1122995965952 2.0204416 0.0000000488 (-0.4346460940373) 0.9006013396248 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_5 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1286536956025):ℝ):ℂ) + (((-0.9916895817781):ℝ):ℂ) * I)‖ ≤ 0.0000001554 := by
  have hl := lg_5
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.832548867433692448 26.83254888410570912 (-1.6998076) 0.00000005539 (-0.1286536956025) (-0.9916895817781) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_6 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0270803158398:ℝ):ℂ) + ((0.9996332609982:ℝ):ℂ) * I)‖ ≤ 0.00000014309 := by
  have hl := lg_6
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.872213862302510208 29.87221387897452688 1.5437127 0.00000004308 0.0270803158398 0.9996332609982 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_7 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5179980123748:ℝ):ℂ) + (((-0.8553818206952):ℝ):ℂ) * I)‖ ≤ 0.00000013953 := by
  have hl := lg_7
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.442213996382555584 32.442214013054588928 (-1.0262875) 0.00000003952 0.5179980123748 (-0.8553818206952) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_8 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9938535571069):ℝ):ℂ) + ((0.110702784831:ℝ):ℂ) * I)‖ ≤ 0.00000015183 := by
  have hl := lg_8
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.6684493698848 34.6684493948928 3.0306625 0.00000005182 (-0.9938535571069) 0.110702784831 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_9 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4827679407983:ℝ):ℂ) + ((0.8757483173477:ℝ):ℂ) * I)‖ ≤ 0.00000011829 := by
  have hl := lg_9
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.632128144681820416 36.63212816135385376 1.0669837 0.00000001828 0.4827679407983 0.8757483173477 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_10 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7715089663143:ℝ):ℂ) + (((-0.6362184490383):ℝ):ℂ) * I)‖ ≤ 0.00000013934 := by
  have hl := lg_10
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.388698657395292448 38.38869868240330912 (-0.6895868) 0.00000003933 0.7715089663143 (-0.6362184490383) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_11 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6501651460711):ℝ):ℂ) + (((-0.7597929210104):ℝ):ℂ) * I)‖ ≤ 0.00000015704 := by
  have hl := lg_11
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.977709975092982176 39.97771000010101552 (-2.2785981) 0.00000005703 (-0.6501651460711) (-0.7597929210104) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_12 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8322407570049):ℝ):ℂ) + ((0.5544143958414:ℝ):ℂ) * I)‖ ≤ 0.00000012703 := by
  have hl := lg_12
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.428363652264110208 41.42836367727212688 2.5539335 0.00000002702 (-0.8322407570049) 0.5544143958414 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_13 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3441514014694:ℝ):ℂ) + ((0.9389141669325:ℝ):ℂ) * I)‖ ≤ 0.00000014936 := by
  have hl := lg_13
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.7628356745973024 42.762835699605335744 1.2194615 0.00000004935 0.3441514014694 0.9389141669325 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_14 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9998709349586:ℝ):ℂ) + (((-0.0160659087819):ℝ):ℂ) * I)‖ ≤ 0.00000016111 := by
  have hl := lg_14
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.998363786344155584 43.998363811352188928 (-0.0160666) 0.0000000611 0.9998709349586 (-0.0160659087819) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p672_15 : ‖exp (-((((((16672:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3935412581607:ℝ):ℂ) + (((-0.9193069553339):ℝ):ℂ) * I)‖ ≤ 0.00000011454 := by
  have hl := lg_15
  refine (ecis_approx ((((16672:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.148612939774602656 45.148612964782636 (-1.1663158) 0.00000001453 0.3935412581607 (-0.9193069553339) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_2 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7025089642892:ℝ):ℂ) + ((0.7116748942412:ℝ):ℂ) * I)‖ ≤ 0.00000014591 := by
  have hl := lg_2
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.7744911517561 11.7744911602496 0.7918795 0.0000000459 0.7025089642892 0.7116748942412 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_3 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.982486545259:ℝ):ℂ) + ((0.1863335406873:ℝ):ℂ) * I)‖ ≤ 0.00000013016 := by
  have hl := lg_3
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.662126943189481868 18.662126951682998855 0.187429 0.00000003015 0.982486545259 0.1863335406873 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_4 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.012962210195):ℝ):ℂ) + ((0.9999159870242:ℝ):ℂ) * I)‖ ≤ 0.00000012522 := by
  have hl := lg_4
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.5489823035122 23.5489823204992 1.5837589 0.00000002521 (-0.012962210195) 0.9999159870242 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_5 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5939696373927):ℝ):ℂ) + (((-0.8044874578537):ℝ):ℂ) * I)‖ ≤ 0.00000011905 := by
  have hl := lg_5
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.339521809686668283 27.33952182667368527 (-2.2067806) 0.00000001904 (-0.5939696373927) (-0.8044874578537) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_6 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.557596785487:ℝ):ℂ) + ((0.8301119351115:ℝ):ℂ) * I)‖ ≤ 0.00000014097 := by
  have hl := lg_6
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.436618094945581868 30.436618111932598855 0.9793084 0.00000004096 0.557596785487 0.8301119351115 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_7 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0683994263639):ℝ):ℂ) + (((-0.9976580167937):ℝ):ℂ) * I)‖ ≤ 0.00000014274 := by
  have hl := lg_7
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.055175693171213514 33.055175710158247488 (-1.6392492) 0.00000004273 (-0.0683994263639) (-0.9976580167937) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_8 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7207211731705):ℝ):ℂ) + ((0.6932250648355:ℝ):ℂ) * I)‖ ≤ 0.00000013769 := by
  have hl := lg_8
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.3234734552683 35.3234734807488 2.3756384 0.00000003768 (-0.7207211731705) 0.6932250648355 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_9 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9305596598439:ℝ):ℂ) + ((0.3661403002555:ℝ):ℂ) * I)‖ ≤ 0.00000015671 := by
  have hl := lg_9
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.324253886378963736 37.32425390336599771 0.3748579 0.0000000567 0.9305596598439 0.3661403002555 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_10 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1552645317065:ℝ):ℂ) + (((-0.9878729296797):ℝ):ℂ) * I)‖ ≤ 0.00000014386 := by
  have hl := lg_10
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.114012961442768283 39.11401298692328527 (-1.4149011) 0.00000004385 0.1552645317065 (-0.9878729296797) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_11 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9942105310996):ℝ):ℂ) + (((-0.1074496132536):ℝ):ℂ) * I)‖ ≤ 0.00000015731 := by
  have hl := lg_11
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.733046985778820071 40.733047011259354045 (-3.0339352) 0.0000000573 (-0.9942105310996) (-0.1074496132536) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_12 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1990530833655):ℝ):ℂ) + ((0.9799887091196:ℝ):ℂ) * I)‖ ≤ 0.00000012194 := by
  have hl := lg_12
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.211109246701681868 42.211109272182198855 1.7711879 0.00000002193 (-0.1990530833655) 0.9799887091196 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_13 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9165209173225:ℝ):ℂ) + ((0.3999867599187:ℝ):ℂ) * I)‖ ≤ 0.00000012832 := by
  have hl := lg_13
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.5707947219520379 43.570794747432571874 0.4115024 0.00000002831 0.9165209173225 0.3999867599187 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_14 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6619569534179:ℝ):ℂ) + (((-0.7495418546164):ℝ):ℂ) * I)‖ ≤ 0.00000012017 := by
  have hl := lg_14
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.829666844927313514 44.829666870407847488 (-0.8473697) 0.00000002016 0.6619569534179 (-0.7495418546164) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p987_15 : ‖exp (-((((((16987:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.43366418057):ℝ):ℂ) + (((-0.9010745687714):ℝ):ℂ) * I)‖ ≤ 0.00000012811 := by
  have hl := lg_15
  refine (ecis_approx ((((16987:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.001648752876150151 46.001648778356684125 (-2.0193516) 0.0000000281 (-0.43366418057) (-0.9010745687714) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p302_2 : ‖exp (-((((((17302:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8399864374775:ℝ):ℂ) + ((0.5426073947651:ℝ):ℂ) * I)‖ ≤ 0.00000010786 := by
  have hl := lg_2
  refine (ecis_approx ((((17302:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.9928325135506 11.9928325222016 0.5735381 0.00000000785 0.8399864374775 0.5426073947651 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p302_3 : ‖exp (-((((((17302:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9874440067139:ℝ):ℂ) + (((-0.1579694071798):ℝ):ℂ) * I)‖ ≤ 0.00000010752 := by
  have hl := lg_3
  refine (ecis_approx ((((17302:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.008189814038053528 19.00818982268907083 (-0.1586339) 0.00000000751 0.9874440067139 (-0.1579694071798) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p302_4 : ‖exp (-((((((17302:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4111544302924:ℝ):ℂ) + ((0.9115657049554:ℝ):ℂ) * I)‖ ≤ 0.0000001157 := by
  have hl := lg_4
  refine (ecis_approx ((((17302:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.9856650271012 23.9856650444032 1.1470762 0.00000001569 0.4111544302924 0.9115657049554 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p302_5 : ‖exp (-((((((17302:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.909864420615):ℝ):ℂ) + (((-0.4149056952735):ℝ):ℂ) * I)‖ ≤ 0.00000014054 := by
  have hl := lg_5
  refine (ecis_approx ((((17302:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.846494751939644118 27.84649476924166142 (-2.7137535) 0.00000004053 (-0.909864420615) (-0.4149056952735) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p302_6 : ‖exp (-((((((17302:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9151549418906:ℝ):ℂ) + ((0.4031022603921:ℝ):ℂ) * I)‖ ≤ 0.00000010901 := by
  have hl := lg_6
  refine (ecis_approx ((((17302:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.001022327588653528 31.00102234489067083 0.4149042 0.000000009 0.9151549418906 0.4031022603921 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p302_7 : ‖exp (-((((((17302:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6298923280705):ℝ):ℂ) + (((-0.7766824673078):ℝ):ℂ) * I)‖ ≤ 0.00000014595 := by
  have hl := lg_7
  refine (ecis_approx ((((17302:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.668137389959871444 33.668137407261906048 (-2.2522109) 0.00000004594 (-0.6298923280705) (-0.7766824673078) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p302_8 : ‖exp (-((((((17302:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1492581471687):ℝ):ℂ) + ((0.988798263299:ℝ):ℂ) * I)‖ ≤ 0.00000012354 := by
  have hl := lg_8
  refine (ecis_approx ((((17302:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.9784975406518 35.9784975666048 1.7206143 0.00000002353 (-0.1492581471687) 0.988798263299 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p302_9 : ‖exp (-((((((17302:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9500913327905:ℝ):ℂ) + (((-0.3119718887277):ℝ):ℂ) * I)‖ ≤ 0.00000011502 := by
  have hl := lg_9
  refine (ecis_approx ((((17302:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.016379628076107056 38.01637964537814166 (-0.3172678) 0.00000001501 0.9500913327905 (-0.3119718887277) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p302_10 : ‖exp (-((((((17302:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5391428748696):ℝ):ℂ) + (((-0.8422143197959):ℝ):ℂ) * I)‖ ≤ 0.00000014838 := by
  have hl := lg_10
  refine (ecis_approx ((((17302:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.839327265490244118 39.83932729144326142 (-2.1402154) 0.00000004837 (-0.5391428748696) (-0.8422143197959) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p723_2 : ‖exp (-((((((17723:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9605778234066:ℝ):ℂ) + ((0.2780112321104:ℝ):ℂ) * I)‖ ≤ 0.00000013792 := by
  have hl := lg_2
  refine (ecis_approx ((((17723:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.2846474764569 12.2846474853184 0.2817231 0.00000003791 0.9605778234066 0.2780112321104 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p723_3 : ‖exp (-((((((17723:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8132099027893:ℝ):ℂ) + (((-0.5819704923838):ℝ):ℂ) * I)‖ ≤ 0.0000001341 := by
  have hl := lg_3
  refine (ecis_approx ((((17723:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.470705587457890572 19.470705596319408295 (-0.6211497) 0.00000003409 0.8132099027893 (-0.5819704923838) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p723_4 : ‖exp (-((((((17723:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8454194562307:ℝ):ℂ) + ((0.5341029329883:ℝ):ℂ) * I)‖ ≤ 0.00000014193 := by
  have hl := lg_4
  refine (ecis_approx ((((17723:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.5692949529138 24.5692949706368 0.5634463 0.00000004192 0.8454194562307 0.5341029329883 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p723_5 : ‖exp (-((((((17723:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9689781341077):ℝ):ℂ) + ((0.2471464653887:ℝ):ℂ) * I)‖ ≤ 0.00000012306 := by
  have hl := lg_5
  refine (ecis_approx ((((17723:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.524068112855526107 28.52406813057854383 2.8918584 0.00000002305 (-0.9689781341077) 0.2471464653887 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p723_6 : ‖exp (-((((((17723:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9429457653281:ℝ):ℂ) + (((-0.3329463675274):ℝ):ℂ) * I)‖ ≤ 0.00000014575 := by
  have hl := lg_6
  refine (ecis_approx ((((17723:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.755353063914790572 31.755353081637808295 (-0.3394265) 0.00000004574 0.9429457653281 (-0.3329463675274) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p723_7 : ‖exp (-((((((17723:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9975402412587):ℝ):ℂ) + (((-0.0700961235573):ℝ):ℂ) * I)‖ ≤ 0.00000014433 := by
  have hl := lg_7
  refine (ecis_approx ((((17723:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.487365562493284106 34.487365580216319552 (-3.071439) 0.00000004432 (-0.9975402412587) (-0.0700961235573) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p723_8 : ‖exp (-((((((17723:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6636045666578:ℝ):ℂ) + ((0.7480835375217:ℝ):ℂ) * I)‖ ≤ 0.00000011372 := by
  have hl := lg_8
  refine (ecis_approx ((((17723:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.8539424293707 36.8539424559552 0.8451694 0.00000001371 0.6636045666578 0.7480835375217 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p723_9 : ‖exp (-((((((17723:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.322620786642:ℝ):ℂ) + (((-0.9465283028132):ℝ):ℂ) * I)‖ ≤ 0.00000014958 := by
  have hl := lg_9
  refine (ecis_approx ((((17723:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.941411174915781144 38.94141119263881659 (-1.2422993) 0.00000004957 0.322620786642 (-0.9465283028132) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p723_10 : ‖exp (-((((((17723:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.999488399954):ℝ):ℂ) + (((-0.0319833979638):ℝ):ℂ) * I)‖ ≤ 0.00000015378 := by
  have hl := lg_10
  refine (ecis_approx ((((17723:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.808715589312426107 40.80871561589694383 (-3.1096038) 0.00000005377 (-0.999488399954) (-0.0319833979638) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p144_2 : ‖exp (-((((((18144:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999490782186:ℝ):ℂ) + (((-0.0100916287019):ℝ):ℂ) * I)‖ ≤ 0.00000013409 := by
  have hl := lg_2
  refine (ecis_approx ((((18144:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.5764624393632 12.5764624484352 (-0.0100918) 0.00000003408 0.9999490782186 (-0.0100916287019) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p144_3 : ‖exp (-((((((18144:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4680924770853:ℝ):ℂ) + (((-0.8836794853883):ℝ):ℂ) * I)‖ ≤ 0.00000014843 := by
  have hl := lg_3
  refine (ecis_approx ((((18144:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.933221360877727616 19.93322136994974576 (-1.0836654) 0.00000004842 0.4680924770853 (-0.8836794853883) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p144_4 : ‖exp (-((((((18144:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997963160421:ℝ):ℂ) + (((-0.0201823296161):ℝ):ℂ) * I)‖ ≤ 0.00000015001 := by
  have hl := lg_4
  refine (ecis_approx ((((18144:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.1529248787264 25.1529248968704 (-0.0201837) 0.00000005 0.9997963160421 (-0.0201823296161) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p144_5 : ‖exp (-((((((18144:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5999901314829):ℝ):ℂ) + ((0.8000074012852:ℝ):ℂ) * I)‖ ≤ 0.00000015603 := by
  have hl := lg_5
  refine (ecis_approx ((((18144:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.201641473771408096 29.20164149191542624 2.2142851 0.00000005602 (-0.5999901314829) 0.8000074012852 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p144_6 : ‖exp (-((((((18144:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4591507868886:ℝ):ℂ) + (((-0.8883583482467):ℝ):ℂ) * I)‖ ≤ 0.00000013567 := by
  have hl := lg_6
  refine (ecis_approx ((((18144:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.509683800240927616 32.50968381838494576 (-1.0937573) 0.00000003566 0.4591507868886 (-0.8883583482467) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p144_7 : ‖exp (-((((((18144:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7323193755948):ℝ):ℂ) + ((0.6809613293709:ℝ):ℂ) * I)‖ ≤ 0.00000011011 := by
  have hl := lg_7
  refine (ecis_approx ((((18144:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.306593735026696768 35.306593753170733056 2.3925181 0.0000000101 (-0.7323193755948) 0.6809613293709 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p144_8 : ‖exp (-((((((18144:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9995417320557:ℝ):ℂ) + (((-0.030270875095):ℝ):ℂ) * I)‖ ≤ 0.000000125 := by
  have hl := lg_8
  refine (ecis_approx ((((18144:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.7293873180896 37.7293873453056 (-0.0302755) 0.00000002499 0.9995417320557 (-0.030270875095) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p144_9 : ‖exp (-((((((18144:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5617789485205):ℝ):ℂ) + (((-0.8272873823465):ℝ):ℂ) * I)‖ ≤ 0.00000012134 := by
  have hl := lg_9
  refine (ecis_approx ((((18144:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.866442721755455232 39.86644273989949152 (-2.1673309) 0.00000002133 (-0.5617789485205) (-0.8272873823465) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p144_10 : ‖exp (-((((((18144:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5918861206618):ℝ):ℂ) + ((0.8060216003039:ℝ):ℂ) * I)‖ ≤ 0.00000013714 := by
  have hl := lg_10
  refine (ecis_approx ((((18144:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.778103913134608096 41.77810394035062624 2.2041932 0.00000003713 (-0.5918861206618) 0.8060216003039 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_2 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9547712547901:ℝ):ℂ) + (((-0.2973413039362):ℝ):ℂ) * I)‖ ≤ 0.0000001121 := by
  have hl := lg_2
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.8682774022695 12.868277411552 (-0.3019068) 0.00000001209 0.9547712547901 (-0.2973413039362) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_3 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0246126411343:ℝ):ℂ) + (((-0.9996970630627):ℝ):ℂ) * I)‖ ≤ 0.00000012206 := by
  have hl := lg_3
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.39573713429756466 20.395737143580083225 (-1.5461812) 0.00000002205 0.0246126411343 (-0.9996970630627) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_4 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8231762979471:ℝ):ℂ) + (((-0.5677858597201):ℝ):ℂ) * I)‖ ≤ 0.00000012419 := by
  have hl := lg_4
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.736554804539 25.736554823104 (-0.6038136) 0.00000002418 0.8231762979471 (-0.5677858597201) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_5 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0340780274754:ℝ):ℂ) + ((0.999419175343:ℝ):ℂ) * I)‖ ≤ 0.00000011737 := by
  have hl := lg_5
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.879214834687290085 29.87921485325230865 1.5367117 0.00000001736 0.0340780274754 0.999419175343 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_6 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2737517860128):ℝ):ℂ) + (((-0.9618003741179):ℝ):ℂ) * I)‖ ≤ 0.00000011925 := by
  have hl := lg_6
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.26401453656706466 33.264014555132083225 (-1.848088) 0.00000001924 (-0.2737517860128) (-0.9618003741179) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_7 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.002493570621):ℝ):ℂ) + ((0.9999968910478:ℝ):ℂ) * I)‖ ≤ 0.00000013553 := by
  have hl := lg_7
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.12582190756010943 36.12582192612514656 1.5732899 0.00000003552 (-0.002493570621) 0.9999968910478 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_8 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6171188790187:ℝ):ℂ) + (((-0.786869931538):ℝ):ℂ) * I)‖ ≤ 0.00000013628 := by
  have hl := lg_8
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.6048322068085 38.604832234656 (-0.9057204) 0.00000003627 0.6171188790187 (-0.786869931538) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_9 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9987884355181):ℝ):ℂ) + (((-0.0492103698498):ℝ):ℂ) * I)‖ ≤ 0.0000001441 := by
  have hl := lg_9
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.79147426859512932 40.79147428716016645 (-3.0923624) 0.00000004409 (-0.9987884355181) (-0.0492103698498) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_10 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3297053218288:ℝ):ℂ) + ((0.9440838949785:ℝ):ℂ) * I)‖ ≤ 0.00000011456 := by
  have hl := lg_10
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.747492236956790085 42.74749226480430865 1.2348049 0.00000001455 0.3297053218288 0.9440838949785 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_11 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8604579249006:ℝ):ℂ) + (((-0.5095215005039):ℝ):ℂ) * I)‖ ≤ 0.00000012525 := by
  have hl := lg_11
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.516925725024065145 44.516925752871602275 (-0.5346286) 0.00000002524 0.8604579249006 (-0.5095215005039) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_12 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5473533135988):ℝ):ℂ) + (((-0.8369016370422):ℝ):ℂ) * I)‖ ≤ 0.00000011644 := by
  have hl := lg_12
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.13229193883656466 46.132291966684083225 (-2.1499948) 0.00000001643 (-0.5473533135988) (-0.8369016370422) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_13 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8802559174677):ℝ):ℂ) + ((0.4744992304174:ℝ):ℂ) * I)‖ ≤ 0.00000015066 := by
  have hl := lg_13
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.6182848067957605 47.61828483464329763 2.6471976 0.00000005065 (-0.8802559174677) 0.4744992304174 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_14 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2949595899656:ℝ):ℂ) + ((0.955509727992:ℝ):ℂ) * I)‖ ≤ 0.00000014762 := by
  have hl := lg_14
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.99409930982960943 48.99409933767714656 1.2713831 0.00000004761 0.2949595899656 0.955509727992 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p565_15 : ‖exp (-((((((18565:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999551646199:ℝ):ℂ) + (((-0.0094693584767):ℝ):ℂ) * I)‖ ≤ 0.00000013941 := by
  have hl := lg_15
  refine (ecis_approx ((((18565:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.274951968984854745 50.274951996832391875 (-0.0094695) 0.0000000394 0.9999551646199 (-0.0094693584767) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_2 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8676958272985:ℝ):ℂ) + (((-0.4970955152572):ℝ):ℂ) * I)‖ ≤ 0.00000015031 := by
  have hl := lg_2
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.086618764064 13.086618773504 (-0.5202482) 0.0000000503 0.8676958272985 (-0.4970955152572) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_3 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3159405080667):ℝ):ℂ) + (((-0.9487790023818):ℝ):ℂ) * I)‖ ≤ 0.00000011641 := by
  have hl := lg_3
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.74180000514613632 20.7418000145861552 (-1.8922441) 0.0000000164 (-0.3159405080667) (-0.9487790023818) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_4 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5057921836879:ℝ):ℂ) + (((-0.8626553581357):ℝ):ℂ) * I)‖ ≤ 0.0000001183 := by
  have hl := lg_4
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.173237528128 26.173237547008 (-1.0404963) 0.00000001829 0.5057921836879 (-0.8626553581357) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_5 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.515042839618:ℝ):ℂ) + ((0.8571644377587:ℝ):ℂ) * I)‖ ≤ 0.00000015897 := by
  have hl := lg_5
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.38618777694026592 30.3861877958202848 1.0297387 0.00000005896 0.515042839618 0.8571644377587 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_6 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7457739809533):ℝ):ℂ) + (((-0.6661990463069):ℝ):ℂ) * I)‖ ≤ 0.00000015221 := by
  have hl := lg_6
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.82841876921013632 33.8284187880901552 (-2.4124922) 0.0000000522 (-0.7457739809533) (-0.6661990463069) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_7 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5732510965161:ℝ):ℂ) + ((0.8193797534373:ℝ):ℂ) * I)‖ ≤ 0.00000013874 := by
  have hl := lg_7
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.73878360434876736 36.73878362322880512 0.9603282 0.00000003873 0.5732510965161 0.8193797534373 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_8 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0100516575243:ℝ):ℂ) + (((-0.9999494808143):ℝ):ℂ) * I)‖ ≤ 0.0000001509 := by
  have hl := lg_8
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.259856292192 39.259856320512 (-1.5607445) 0.00000005089 0.0100516575243 (-0.9999494808143) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_9 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8003631864109):ℝ):ℂ) + ((0.59951544583:ℝ):ℂ) * I)‖ ≤ 0.00000013998 := by
  have hl := lg_9
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.48360001029227264 41.4836000291723104 2.4986971 0.00000003997 (-0.8003631864109) 0.59951544583 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_10 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.872993071891:ℝ):ℂ) + ((0.4877326075118:ℝ):ℂ) * I)‖ ≤ 0.00000011908 := by
  have hl := lg_10
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.47280654100426592 43.4728065693242848 0.5094906 0.00000001907 0.872993071891 0.4877326075118 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_11 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2771539276188:ℝ):ℂ) + (((-0.9608255306795):ℝ):ℂ) * I)‖ ≤ 0.00000011456 := by
  have hl := lg_11
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.27226273570990304 45.2722627640299408 (-1.2899656) 0.00000001455 0.2771539276188 (-0.9608255306795) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_12 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9782695294553):ℝ):ℂ) + (((-0.2073372311609):ℝ):ℂ) * I)‖ ≤ 0.000000117 := by
  have hl := lg_12
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.91503753327413632 46.9150375615941552 (-2.9327404) 0.00000001699 (-0.9782695294553) (-0.2073372311609) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_13 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2652298219331):ℝ):ℂ) + ((0.9641852216021:ℝ):ℂ) * I)‖ ≤ 0.00000012505 := by
  have hl := lg_13
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.426243854150496 48.42624388247053376 1.8392386 0.00000002504 (-0.2652298219331) 0.9641852216021 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_14 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9047175425664:ℝ):ℂ) + ((0.4260119343077:ℝ):ℂ) * I)‖ ≤ 0.00000013931 := by
  have hl := lg_14
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.82540236841276736 49.82540239673280512 0.4400801 0.0000000393 0.9047175425664 0.4260119343077 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p88_15 : ‖exp (-((((((18880:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6505367996574:ℝ):ℂ) + (((-0.7594747344656):ℝ):ℂ) * I)‖ ≤ 0.00000015298 := by
  have hl := lg_15
  refine (ecis_approx ((((18880:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.12798778208640224 51.12798781040644 (-0.8625053) 0.00000005297 0.6505367996574 (-0.7594747344656) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_2 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7751581757053:ℝ):ℂ) + (((-0.6317672060476):ℝ):ℂ) * I)‖ ≤ 0.00000011576 := by
  have hl := lg_2
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.2502014986148 13.2502015081728 (-0.6838309) 0.00000001575 0.7751581757053 (-0.6317672060476) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_3 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5486262762176):ℝ):ℂ) + (((-0.8360677060113):ℝ):ℂ) * I)‖ ≤ 0.00000011634 := by
  have hl := lg_3
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.001072505210463024 21.00107251476848214 (-2.1515166) 0.00000001633 (-0.5486262762176) (-0.8360677060113) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_4 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2017403947255:ℝ):ℂ) + (((-0.9794390298206):ℝ):ℂ) * I)‖ ≤ 0.0000001315 := by
  have hl := lg_4
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.5004029972296 26.5004030163456 (-1.3676618) 0.00000003149 0.2017403947255 (-0.9794390298206) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_5 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7961374149399:ℝ):ℂ) + ((0.6051158703362:ℝ):ℂ) * I)‖ ≤ 0.00000011176 := by
  have hl := lg_5
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.766015124152019244 30.76601514326803836 0.6499114 0.00000001175 0.7961374149399 0.6051158703362 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_6 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9534723020367):ℝ):ℂ) + (((-0.3014806279611):ℝ):ℂ) * I)‖ ≤ 0.00000013209 := by
  have hl := lg_6
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.251274003825263024 34.25127402294128214 (-2.8353475) 0.00000003208 (-0.9534723020367) (-0.3014806279611) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_7 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8770578335257:ℝ):ℂ) + ((0.4803848006039:ℝ):ℂ) * I)‖ ≤ 0.00000014369 := by
  have hl := lg_7
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.198018399403126952 37.198018418519165184 0.5010934 0.00000004368 0.8770578335257 0.4803848006039 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_8 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4623967430222):ℝ):ℂ) + (((-0.8866731370903):ℝ):ℂ) * I)‖ ≤ 0.00000014725 := by
  have hl := lg_8
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.7506044958444 39.7506045245184 (-2.0514927) 0.00000004724 (-0.4623967430222) (-0.8866731370903) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_9 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3980184115001):ℝ):ℂ) + ((0.9173774272913:ℝ):ℂ) * I)‖ ≤ 0.00000013985 := by
  have hl := lg_9
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.002145010420926048 42.00214502953696428 1.9801521 0.00000003984 (-0.3980184115001) 0.9173774272913 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_10 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.999424788913:ℝ):ℂ) + (((-0.0339129961264):ℝ):ℂ) * I)‖ ≤ 0.00000012751 := by
  have hl := lg_10
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.016216622766819244 44.01621665144083836 (-0.0339195) 0.0000000275 0.999424788913 (-0.0339129961264) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_11 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2812270962769):ℝ):ℂ) + (((-0.959641245632):ℝ):ℂ) * I)‖ ≤ 0.00000013037 := by
  have hl := lg_11
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.838166019906276828 45.83816604858031506 (-1.8558689) 0.00000003036 (-0.2812270962769) (-0.959641245632) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_12 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9295574216668):ℝ):ℂ) + ((0.3686773652739:ℝ):ℂ) * I)‖ ≤ 0.00000015501 := by
  have hl := lg_12
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.501475502440063024 47.50147553111408214 2.7640069 0.000000055 (-0.9295574216668) 0.3686773652739 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_13 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3305495784778:ℝ):ℂ) + ((0.9437886289674:ℝ):ℂ) * I)‖ ≤ 0.00000015512 := by
  have hl := lg_13
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.0315719023273772 49.031571931001415432 1.2339105 0.00000005511 0.3305495784778 0.9437886289674 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_14 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9833499135291:ℝ):ℂ) + (((-0.181722171356):ℝ):ℂ) * I)‖ ≤ 0.00000015943 := by
  have hl := lg_14
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.448219898017926952 50.448219926691965184 (-0.1827375) 0.00000005942 0.9833499135291 (-0.181722171356) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p116_15 : ‖exp (-((((((19116:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0691359322697:ℝ):ℂ) + (((-0.9976072488054):ℝ):ℂ) * I)‖ ≤ 0.00000012809 := by
  have hl := lg_15
  refine (ecis_approx ((((19116:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.767087629362482268 51.7670876580365205 (-1.5016052) 0.00000002808 0.0691359322697 (-0.9976072488054) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_2 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6619240478926:ℝ):ℂ) + (((-0.7495709138043):ℝ):ℂ) * I)‖ ≤ 0.0000001285 := by
  have hl := lg_2
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.4137842331656 13.4137842428416 (-0.8474136) 0.00000002849 0.6619240478926 (-0.7495709138043) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_3 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7446382963291):ℝ):ℂ) + (((-0.6674682071886):ℝ):ℂ) * I)‖ ≤ 0.00000011628 := by
  have hl := lg_3
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.260345005274789728 21.26034501495080908 (-2.4107891) 0.00000001627 (-0.7446382963291) (-0.6674682071886) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_4 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.123713109643):ℝ):ℂ) + (((-0.9923180268956):ℝ):ℂ) * I)‖ ≤ 0.00000015698 := by
  have hl := lg_4
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.8275684663312 26.8275684856832 (-1.6948272) 0.00000005697 (-0.123713109643) (-0.9923180268956) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_5 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9637484608438:ℝ):ℂ) + ((0.2668124888778:ℝ):ℂ) * I)‖ ≤ 0.00000015483 := by
  have hl := lg_5
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.145842471363772568 31.14584249071579192 0.2700841 0.00000005482 0.9637484608438 0.2668124888778 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_6 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9932087483015):ℝ):ℂ) + ((0.1163459576016:ℝ):ℂ) * I)‖ ≤ 0.00000011473 := by
  have hl := lg_6
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.674129238440389728 34.67412925779240908 3.0249826 0.00000001472 (-0.9932087483015) 0.1163459576016 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_7 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9991240567123:ℝ):ℂ) + ((0.0418463773662:ℝ):ℂ) * I)‖ ≤ 0.00000014864 := by
  have hl := lg_7
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.657253194457486544 37.657253213809525248 0.0418586 0.00000004863 0.9991240567123 0.0418463773662 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_8 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8257014689142):ℝ):ℂ) + (((-0.5641073339113):ℝ):ℂ) * I)‖ ≤ 0.0000001436 := by
  have hl := lg_8
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.2413526994968 40.2413527285248 (-2.5422409) 0.00000004359 (-0.8257014689142) (-0.5641073339113) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_9 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1089723918726:ℝ):ℂ) + ((0.9940447765616:ℝ):ℂ) * I)‖ ≤ 0.00000013972 := by
  have hl := lg_9
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.520690010549579456 42.52069002990161816 1.4616071 0.00000003971 0.1089723918726 0.9940447765616 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_10 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8379231088758:ℝ):ℂ) + (((-0.5457882955982):ℝ):ℂ) * I)‖ ≤ 0.00000014574 := by
  have hl := lg_10
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.559626704529372568 44.55962673355739192 (-0.5773296) 0.00000004573 0.8379231088758 (-0.5457882955982) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_11 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7519241071673):ℝ):ℂ) + (((-0.6592496773047):ℝ):ℂ) * I)‖ ≤ 0.00000014617 := by
  have hl := lg_11
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.404069304102650616 46.40406933313068932 (-2.4217722) 0.00000004616 (-0.7519241071673) (-0.6592496773047) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_12 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.570219209294):ℝ):ℂ) + ((0.8214925765594:ℝ):ℂ) * I)‖ ≤ 0.00000014321 := by
  have hl := lg_12
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.087913471605989728 48.08791350063400908 2.177569 0.0000000432 (-0.570219209294) 0.8214925765594 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_13 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8088618089396:ℝ):ℂ) + ((0.5879987874468:ℝ):ℂ) * I)‖ ≤ 0.00000012211 := by
  have hl := lg_13
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.6368999505042584 49.636899979532297104 0.6285825 0.0000000221 0.8088618089396 0.5879987874468 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_14 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6927110672877:ℝ):ℂ) + (((-0.7212152086979):ℝ):ℂ) * I)‖ ≤ 0.00000012983 := by
  have hl := lg_14
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.071037427623086544 51.071037456651125248 (-0.805555) 0.00000002982 0.6927110672877 (-0.7212152086979) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p352_15 : ‖exp (-((((((19352:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5395551583656):ℝ):ℂ) + (((-0.8419502545121):ℝ):ℂ) * I)‖ ≤ 0.00000014824 := by
  have hl := lg_15
  refine (ecis_approx ((((19352:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.406187476638562296 52.406187505666601 (-2.140705) 0.00000004823 (-0.5395551583656) (-0.8419502545121) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_2 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5310166742449:ℝ):ℂ) + (((-0.8473613701803):ℝ):ℂ) * I)‖ ≤ 0.00000014666 := by
  have hl := lg_2
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.5773669677164 13.5773669775104 (-1.0109964) 0.00000004665 0.5310166742449 (-0.8473613701803) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_3 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8908738502893):ℝ):ℂ) + (((-0.4542507928052):ℝ):ℂ) * I)‖ ≤ 0.00000011621 := by
  have hl := lg_3
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.519617505339116432 21.51961751513313602 (-2.6700616) 0.0000000162 (-0.8908738502893) (-0.4542507928052) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_4 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4360424933552):ℝ):ℂ) + (((-0.8999260769555):ℝ):ℂ) * I)‖ ≤ 0.00000012632 := by
  have hl := lg_4
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.1547339354328 27.1547339550208 (-2.0219927) 0.00000002631 (-0.4360424933552) (-0.8999260769555) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_5 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9939842452979:ℝ):ℂ) + (((-0.1095231486927):ℝ):ℂ) * I)‖ ≤ 0.00000011734 := by
  have hl := lg_5
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.525669818575525892 31.52566983816354548 (-0.1097433) 0.00000001733 0.9939842452979 (-0.1095231486927) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_6 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8579834910741):ℝ):ℂ) + ((0.5136772614835:ℝ):ℂ) * I)‖ ≤ 0.00000014958 := by
  have hl := lg_6
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.096984473055516432 35.09698449264353602 2.6021274 0.00000004957 (-0.8579834910741) 0.5136772614835 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_7 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9141556779621:ℝ):ℂ) + (((-0.4053632894696):ℝ):ℂ) * I)‖ ≤ 0.00000015358 := by
  have hl := lg_7
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.116487989511846136 38.116488009099885312 (-0.4173762) 0.00000005357 0.9141556779621 (-0.4053632894696) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_8 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9941084280749):ℝ):ℂ) + (((-0.1083901876083):ℝ):ℂ) * I)‖ ≤ 0.00000013994 := by
  have hl := lg_8
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.7321009031492 40.7321009325312 (-3.0329891) 0.00000003993 (-0.9941084280749) (-0.1083901876083) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_9 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5873124401775:ℝ):ℂ) + ((0.8093603014806:ℝ):ℂ) * I)‖ ≤ 0.00000013959 := by
  have hl := lg_9
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.039235010678232864 43.03923503026627204 0.9430621 0.00000003958 0.5873124401775 0.8093603014806 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_10 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4350165228472:ℝ):ℂ) + (((-0.9004224702049):ℝ):ℂ) * I)‖ ≤ 0.00000016398 := by
  have hl := lg_10
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.103036786291925892 45.10303681567394548 (-1.1207397) 0.00000006397 0.4350165228472 (-0.9004224702049) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_11 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9881781212612):ℝ):ℂ) + (((-0.1533101440634):ℝ):ℂ) * I)‖ ≤ 0.00000016197 := by
  have hl := lg_11
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.969972588299024404 46.96997261768106358 (-2.9876755) 0.00000006196 (-0.9881781212612) (-0.1533101440634) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_12 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0203332718398):ℝ):ℂ) + ((0.9997932576568:ℝ):ℂ) * I)‖ ≤ 0.00000011668 := by
  have hl := lg_12
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.674351440771916432 48.67435147015393602 1.591131 0.00000001667 (-0.0203332718398) 0.9997932576568 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_13 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997296286246:ℝ):ℂ) + ((0.0232523041875:ℝ):ℂ) * I)‖ ≤ 0.00000015877 := by
  have hl := lg_13
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.2422279986811396 50.242228028063178776 0.0232544 0.00000005876 0.9997296286246 0.0232523041875 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_14 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1419428144552:ℝ):ℂ) + (((-0.9898748594769):ℝ):ℂ) * I)‖ ≤ 0.00000012919 := by
  have hl := lg_14
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.693854957228246136 51.693854986610285312 (-1.4283725) 0.00000002918 0.1419428144552 (-0.9898748594769) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p588_15 : ‖exp (-((((((19588:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9352655488392):ℝ):ℂ) + (((-0.3539468222556):ℝ):ℂ) * I)‖ ≤ 0.00000013354 := by
  have hl := lg_15
  refine (ecis_approx ((((19588:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.045287323914642324 53.0452873532966815 (-2.7798049) 0.00000003353 (-0.9352655488392) (-0.3539468222556) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p765_2 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4233256092682:ℝ):ℂ) + (((-0.9059776092916):ℝ):ℂ) * I)‖ ≤ 0.00000011417 := by
  have hl := lg_2
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.7000540186295 13.700054028512 (-1.1336834) 0.00000001416 0.4233256092682 (-0.9059776092916) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p765_3 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9618592137986):ℝ):ℂ) + (((-0.2735449736173):ℝ):ℂ) * I)‖ ≤ 0.00000014117 := by
  have hl := lg_3
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.71407188038736146 21.714071890269881225 (-2.864516) 0.00000004116 (-0.9618592137986) (-0.2735449736173) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p765_4 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6415908570738):ℝ):ℂ) + (((-0.7670470468644):ℝ):ℂ) * I)‖ ≤ 0.00000012832 := by
  have hl := lg_4
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.400108037259 27.400108057024 (-2.2673668) 0.00000002831 (-0.6415908570738) (-0.7670470468644) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p765_5 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9231451084493:ℝ):ℂ) + (((-0.3844516988468):ℝ):ℂ) * I)‖ ≤ 0.00000011287 := by
  have hl := lg_5
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.810540328984340885 31.81054034874936065 (-0.3946138) 0.00000001286 0.9231451084493 (-0.3844516988468) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p765_6 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6550052536649):ℝ):ℂ) + ((0.7556243230958:ℝ):ℂ) * I)‖ ≤ 0.00000014408 := by
  have hl := lg_6
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.41412589901686146 35.414125918781881225 2.2849859 0.00000004407 (-0.6550052536649) 0.7556243230958 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
