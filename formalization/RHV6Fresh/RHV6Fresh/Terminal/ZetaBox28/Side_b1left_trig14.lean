/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 14

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

lemma cs_b1left_v25p1_23 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9870532879751):ℝ):ℂ) + ((0.1603926629246:ℝ):ℂ) * I)‖ ≤ 0.0000001506 := by
  have hl := lg_23
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.7009047937230866 78.7009048439231619 2.9805042 0.00000005059 (-0.9870532879751) 0.1603926629246 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_24 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3348646404116):ℝ):ℂ) + ((0.9422662429483:ℝ):ℂ) * I)‖ ≤ 0.00000017252 := by
  have hl := lg_24
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.7691511156349164 79.7691511658349415 1.9122579 0.00000007251 (-0.3348646404116) 0.9422662429483 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_25 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6312551746413:ℝ):ℂ) + ((0.7755752087893:ℝ):ℂ) * I)‖ ≤ 0.00000013497 := by
  have hl := lg_25
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.7937831780932918 80.793783228293342 0.8876258 0.00000003496 0.6312551746413 0.7755752087893 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_26 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9953171744007:ℝ):ℂ) + (((-0.0966629315871):ℝ):ℂ) * I)‖ ≤ 0.00000013512 := by
  have hl := lg_26
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.77822307824067 81.7782231284407202 (-0.0968141) 0.00000003511 0.9953171744007 (-0.0966629315871) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_27 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5026833535768:ℝ):ℂ) + (((-0.8644706160633):ℝ):ℂ) * I)‖ ≤ 0.00000016147 := by
  have hl := lg_27
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.7255053171347492 82.7255053547848245 (-1.0440963) 0.00000006146 0.5026833535768 (-0.8644706160633) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_28 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3766042087707):ℝ):ℂ) + (((-0.926374260185):ℝ):ℂ) * I)‖ ≤ 0.00000013618 := by
  have hl := lg_28
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.6383331792990922 83.6383332294991424 (-1.9569242) 0.00000003617 (-0.3766042087707) (-0.926374260185) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_29 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9541837736126):ℝ):ℂ) + (((-0.2992211990475):ℝ):ℂ) * I)‖ ≤ 0.00000016344 := by
  have hl := lg_29
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.5191253065619692 84.5191253567620445 (-2.8377163) 0.00000006343 (-0.9541837736126) (-0.2992211990475) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_30 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8540613572639):ℝ):ℂ) + ((0.5201722771853:ℝ):ℂ) * I)‖ ≤ 0.00000014691 := by
  have hl := lg_30
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.3700542536215623 85.3700543038216125 2.59454 0.0000000469 (-0.8540613572639) 0.5201722771853 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_31 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1993741169795):ℝ):ℂ) + ((0.9799234467436:ℝ):ℂ) * I)‖ ≤ 0.00000015618 := by
  have hl := lg_31
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.1930788064786113 86.1930788566786866 1.7715155 0.00000005617 (-0.1993741169795) 0.9799234467436 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_32 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5614799745256:ℝ):ℂ) + ((0.8274903251439:ℝ):ℂ) * I)‖ ≤ 0.00000017288 := by
  have hl := lg_32
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.98997112765 86.9899711904 0.9746231 0.00000007287 0.5614799745256 0.8274903251439 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_33 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9796161874888:ℝ):ℂ) + ((0.200878384128:ℝ):ℂ) * I)‖ ≤ 0.00000013382 := by
  have hl := lg_33
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.7623397667100947 87.76233981691017 0.2022545 0.00000003381 0.9796161874888 0.200878384128 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_34 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8540601887605:ℝ):ℂ) + (((-0.5201741957983):ℝ):ℂ) * I)‖ ≤ 0.00000016529 := by
  have hl := lg_34
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.5116491352424934 88.5116491979925185 (-0.5470549) 0.00000006528 0.8540601887605 (-0.5201741957983) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_35 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2918441185276:ℝ):ℂ) + (((-0.956465896141):ℝ):ℂ) * I)‖ ≤ 0.00000016699 := by
  have hl := lg_35
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.2392363172857381 89.2392363674858134 (-1.274642) 0.00000006698 0.2918441185276 (-0.956465896141) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_36 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3994664536781):ℝ):ℂ) + (((-0.9167478128595):ℝ):ℂ) * I)‖ ≤ 0.00000017138 := by
  have hl := lg_36
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.9463253291498328 89.946325379349883 (-1.9817311) 0.00000007137 (-0.3994664536781) (-0.9167478128595) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_37 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8905937263551):ℝ):ℂ) + (((-0.4547997520565):ℝ):ℂ) * I)‖ ≤ 0.00000013097 := by
  have hl := lg_37
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.6340395812714942 90.6340396314715695 (-2.6694453) 0.00000003096 (-0.8905937263551) (-0.4547997520565) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_38 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9806139827611):ℝ):ℂ) + ((0.1959495253507:ℝ):ℂ) * I)‖ ≤ 0.00000012556 := by
  have hl := lg_38
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.3034125830337353 91.3034126332338106 2.944367 0.00000002555 (-0.9806139827611) 0.1959495253507 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_39 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6605761859329):ℝ):ℂ) + ((0.750759017635:ℝ):ℂ) * I)‖ ≤ 0.00000013428 := by
  have hl := lg_39
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.9553972917555864 91.9553973419556617 2.2923823 0.00000003427 (-0.6605761859329) 0.750759017635 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_40 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0860025998224):ℝ):ℂ) + ((0.9962949125753:ℝ):ℂ) * I)‖ ≤ 0.00000014207 := by
  have hl := lg_40
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.5908742656366459 92.590874328386671 1.6569053 0.00000004206 (-0.0860025998224) 0.9962949125753 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_41 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5087012759185:ℝ):ℂ) + ((0.8609430944487:ℝ):ℂ) * I)‖ ≤ 0.00000016605 := by
  have hl := lg_41
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.210658841654958 93.2106589044050082 1.0371207 0.00000006604 0.5087012759185 0.8609430944487 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_42 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9080161902073:ℝ):ℂ) + ((0.4189350764992:ℝ):ℂ) * I)‖ ≤ 0.00000013534 := by
  have hl := lg_42
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.8155073928140086 93.8155074430140839 0.4322722 0.00000003533 0.9080161902073 0.4189350764992 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_43 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.987489870929:ℝ):ℂ) + (((-0.1576824492853):ℝ):ℂ) * I)‖ ≤ 0.0000001299 := by
  have hl := lg_43
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.406122877809878 94.4061229280099784 (-0.1583433) 0.00000002989 0.987489870929 (-0.1576824492853) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_44 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7415757425553:ℝ):ℂ) + (((-0.6708691512162):ℝ):ℂ) * I)‖ ≤ 0.0000001338 := by
  have hl := lg_44
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.9831597787251783 94.9831598414752285 (-0.7353802) 0.00000003379 0.7415757425553 (-0.6708691512162) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_45 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2680298048925:ℝ):ℂ) + (((-0.9634106204985):ℝ):ℂ) * I)‖ ≤ 0.00000014057 := by
  have hl := lg_45
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.5472284671364787 95.547228517336554 (-1.2994489) 0.00000004056 0.2680298048925 (-0.9634106204985) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_46 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2766661253971):ℝ):ℂ) + (((-0.9609661050507):ℝ):ℂ) * I)‖ ≤ 0.00000017432 := by
  have hl := lg_46
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.0988990192530866 96.0988990820031619 (-1.8511194) 0.00000007431 (-0.2766661253971) (-0.9609661050507) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_47 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7312337436841):ℝ):ℂ) + (((-0.6821269764994):ℝ):ℂ) * I)‖ ≤ 0.00000013741 := by
  have hl := lg_47
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.6387047702992579 96.6387048330493583 (-2.3909252) 0.0000000374 (-0.7312337436841) (-0.6821269764994) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_48 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.975409064517):ℝ):ℂ) + (((-0.2204022607877):ℝ):ℂ) * I)‖ ≤ 0.00000016654 := by
  have hl := lg_48
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.1671453411649164 97.1671454039149415 (-2.9193658) 0.00000006653 (-0.975409064517) (-0.2204022607877) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_49 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9567098558289):ℝ):ℂ) + ((0.291043384287:ℝ):ℂ) * I)‖ ≤ 0.00000015841 := by
  have hl := lg_49
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.6846894564781844 97.6846895066782848 2.8462754 0.0000000584 (-0.9567098558289) 0.291043384287 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_50 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6949793442895):ℝ):ℂ) + ((0.7190297010472:ℝ):ℂ) * I)‖ ≤ 0.00000015151 := by
  have hl := lg_50
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.1917774036232918 98.191777466373342 2.3391875 0.0000000515 (-0.6949793442895) 0.7190297010472 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_51 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2680276337596):ℝ):ℂ) + ((0.9634112245245:ℝ):ℂ) * I)‖ ≤ 0.00000016613 := by
  have hl := lg_51
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.6888233487574098 98.68882341150746 1.8421415 0.00000006612 (-0.2680276337596) 0.9634112245245 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_52 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2143718921128:ℝ):ℂ) + ((0.9767521138303:ℝ):ℂ) * I)‖ ≤ 0.00000015166 := by
  have hl := lg_52
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.17621730377067 99.1762173665207202 1.3547476 0.00000005165 0.2143718921128 0.9767521138303 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_53 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6397388394169:ℝ):ℂ) + ((0.76859236097:ℝ):ℂ) * I)‖ ≤ 0.00000014543 := by
  have hl := lg_53
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.6543269975350894 99.6543270602851647 0.8766379 0.00000004542 0.6397388394169 0.76859236097 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_54 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.918128230685:ℝ):ℂ) + ((0.3962834238512:ℝ):ℂ) * I)‖ ≤ 0.00000017222 := by
  have hl := lg_54
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.1234995426647492 100.1234995928648245 0.4074653 0.00000007221 0.918128230685 0.3962834238512 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_55 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9985906323753:ℝ):ℂ) + (((-0.0530730527881):ℝ):ℂ) * I)‖ ≤ 0.0000001646 := by
  have hl := lg_55
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.5840629167118242 100.5840629794618995 (-0.053098) 0.00000006459 0.9985906323753 (-0.0530730527881) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_56 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8749990367312:ℝ):ℂ) + (((-0.4841246592763):ℝ):ℂ) * I)‖ ≤ 0.00000015272 := by
  have hl := lg_56
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.0363274048290922 101.0363274675791424 (-0.5053625) 0.00000005271 0.8749990367312 (-0.4841246592763) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_57 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5819906002803:ℝ):ℂ) + (((-0.8131955122757):ℝ):ℂ) * I)‖ ≤ 0.00000013189 := by
  have hl := lg_57
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.4805867965486517 101.4805868467487521 (-0.9496219) 0.00000003188 0.5819906002803 (-0.8131955122757) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_58 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.183594362009:ℝ):ℂ) + (((-0.9830020906582):ℝ):ℂ) * I)‖ ≤ 0.00000017998 := by
  have hl := lg_58
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.9171195320919692 101.9171195948420445 (-1.3861546) 0.00000007997 0.183594362009 (-0.9830020906582) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_59 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2420019227558):ℝ):ℂ) + (((-0.9702757697589):ℝ):ℂ) * I)‖ ≤ 0.0000001573 := by
  have hl := lg_59
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.3461898094103992 102.3461898721604996 (-1.8152249) 0.00000005729 (-0.2420019227558) (-0.9702757697589) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p1_60 : ‖exp (-((((((25100:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6180715980836):ℝ):ℂ) + (((-0.7861218096636):ℝ):ℂ) * I)‖ ≤ 0.00000013574 := by
  have hl := lg_60
  refine (ecis_approx ((((25100:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.7680484791515623 102.7680485419016125 (-2.2370836) 0.00000003573 (-0.6180715980836) (-0.7861218096636) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_2 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.147117697276:ℝ):ℂ) + ((0.989118993422:ℝ):ℂ) * I)‖ ≤ 0.00000015097 := by
  have hl := lg_2
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.4264132599223 17.4264132724928 1.4231427 0.00000005096 0.147117697276 0.989118993422 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_3 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.793582249019):ℝ):ℂ) + (((-0.6084629931188):ℝ):ℂ) * I)‖ ≤ 0.00000012674 := by
  have hl := lg_3
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.620211542869651124 27.620211555440176265 (-2.4874703) 0.00000002673 (-0.793582249019) (-0.6084629931188) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_4 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9567127371115):ℝ):ℂ) + ((0.2910339128451:ℝ):ℂ) * I)‖ ≤ 0.00000012325 := by
  have hl := lg_4
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.8528265198446 34.8528265449856 2.8462853 0.00000002324 (-0.9567127371115) 0.2910339128451 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_5 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9294688385487):ℝ):ℂ) + (((-0.3689006343289):ℝ):ℂ) * I)‖ ≤ 0.00000012551 := by
  have hl := lg_5
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.462878543435128469 40.46287856857615361 (-2.7637667) 0.0000000255 (-0.9294688385487) (-0.3689006343289) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_6 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4850922227918:ℝ):ℂ) + (((-0.8744629982949):ℝ):ℂ) * I)‖ ≤ 0.00000014748 := by
  have hl := lg_6
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.046624802791951124 45.046624827932976265 (-1.0643277) 0.00000004747 0.4850922227918 (-0.8744629982949) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_7 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2254850961771:ℝ):ℂ) + ((0.9742466173418:ℝ):ℂ) * I)‖ ≤ 0.00000011312 := by
  have hl := lg_7
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.922127044329044502 48.922127069470094784 1.3433554 0.00000001311 0.2254850961771 0.9742466173418 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_8 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4286165394021):ℝ):ℂ) + (((-0.9034865035777):ℝ):ℂ) * I)‖ ≤ 0.00000016006 := by
  have hl := lg_8
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.2792397797669 52.2792398174784 (-2.0137573) 0.00000006005 (-0.4286165394021) (-0.9034865035777) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_9 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2595455788794:ℝ):ℂ) + ((0.9657308592378:ℝ):ℂ) * I)‖ ≤ 0.00000014628 := by
  have hl := lg_9
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.240423085739302248 55.24042311088035253 1.3082447 0.00000004627 0.2595455788794 0.9657308592378 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_10 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2281452115957:ℝ):ℂ) + (((-0.9736271167269):ℝ):ℂ) * I)‖ ≤ 0.00000016127 := by
  have hl := lg_10
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.889291803357428469 57.88929184106895361 (-1.3406241) 0.00000006126 0.2281452115957 (-0.9736271167269) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_11 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8280225576249):ℝ):ℂ) + ((0.5606947868519:ℝ):ℂ) * I)‖ ≤ 0.00000013799 := by
  have hl := lg_11
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.285485033817938153 60.285485071529488435 2.546368 0.00000003798 (-0.8280225576249) 0.5606947868519 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_12 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9363136114419:ℝ):ℂ) + ((0.3511649484625:ℝ):ℂ) * I)‖ ≤ 0.00000012864 := by
  have hl := lg_12
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.473038062714251124 62.473038100425776265 0.358815 0.00000002863 0.9363136114419 0.3511649484625 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_13 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0826479923295):ℝ):ℂ) + (((-0.9965788023852):ℝ):ℂ) * I)‖ ≤ 0.00000014227 := by
  have hl := lg_13
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.4853917763346197 64.485391814046169982 (-1.6535387) 0.00000004226 (-0.0826479923295) (-0.9965788023852) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_14 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9304729853175):ℝ):ℂ) + ((0.3663605101998:ℝ):ℂ) * I)‖ ≤ 0.000000163 := by
  have hl := lg_14
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.348540304251344502 66.348540341962894784 2.7664981 0.00000006299 (-0.9304729853175) 0.3663605101998 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_15 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5131475933129:ℝ):ℂ) + ((0.8583003830112:ℝ):ℂ) * I)‖ ≤ 0.00000014506 := by
  have hl := lg_15
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.083090086304779593 68.083090124016329875 1.0319483 0.00000004505 0.5131475933129 0.8583003830112 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_16 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8305985270129:ℝ):ℂ) + (((-0.5568716970039):ℝ):ℂ) * I)‖ ≤ 0.0000001393 := by
  have hl := lg_16
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.7056530396892 69.7056530899712 (-0.5906147) 0.00000003929 0.8305985270129 (-0.5568716970039) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_17 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5175472795209):ℝ):ℂ) + (((-0.8556546110747):ℝ):ℂ) * I)‖ ≤ 0.0000001281 := by
  have hl := lg_17
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.229816656776167194 71.229816707058192335 (-2.1147783) 0.00000002809 (-0.5175472795209) (-0.8556546110747) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_18 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9170389475799):ℝ):ℂ) + ((0.3987976535577:ℝ):ℂ) * I)‖ ≤ 0.00000014051 := by
  have hl := lg_18
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.666836345661602248 72.66683638337315253 2.7313873 0.0000000405 (-0.9170389475799) 0.3987976535577 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_19 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1974078471904:ℝ):ℂ) + ((0.980321448234:ℝ):ℂ) * I)‖ ≤ 0.00000013055 := by
  have hl := lg_19
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.026140355617586023 74.026140393329161446 1.3720833 0.00000003054 0.1974078471904 0.980321448234 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_20 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9965972718398:ℝ):ℂ) + ((0.0824249826293:ℝ):ℂ) * I)‖ ≤ 0.00000012742 := by
  have hl := lg_20
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.315705063279728469 75.31570511356175361 0.0825186 0.00000002741 0.9965972718398 0.0824249826293 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_21 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4138520431027:ℝ):ℂ) + (((-0.9103441582279):ℝ):ℂ) * I)‖ ≤ 0.00000013877 := by
  have hl := lg_21
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.542338587198695626 76.542338624910271049 (-1.1441149) 0.00000003876 0.4138520431027 (-0.9103441582279) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_22 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6764106299038):ℝ):ℂ) + (((-0.736524717666):ℝ):ℂ) * I)‖ ≤ 0.00000015788 := by
  have hl := lg_22
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.711898293740238153 77.711898344022288435 (-2.3136746) 0.00000005787 (-0.6764106299038) (-0.736524717666) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_23 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9583456840742):ℝ):ℂ) + ((0.2856108359091:ℝ):ℂ) * I)‖ ≤ 0.00000013682 := by
  have hl := lg_23
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.829460056533550606 78.829460106815626029 2.8519489 0.00000003681 (-0.9583456840742) 0.2856108359091 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_24 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2095955201261):ℝ):ℂ) + ((0.9777881764176:ℝ):ℂ) * I)‖ ≤ 0.00000017071 := by
  have hl := lg_24
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.899451322636551124 79.899451372918576265 1.7819576 0.0000000707 (-0.2095955201261) 0.9777881764176 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_25 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7278246487831:ℝ):ℂ) + ((0.685763283228:ℝ):ℂ) * I)‖ ≤ 0.00000014383 := by
  have hl := lg_25
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.925757086870256938 80.92575713715230722 0.7556519 0.00000004382 0.7278246487831 0.685763283228 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_26 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9735760167289:ℝ):ℂ) + (((-0.2283631748999):ℝ):ℂ) * I)‖ ≤ 0.00000015709 := by
  have hl := lg_26
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.9118050362569197 81.911805086538969982 (-0.2303961) 0.00000005708 0.9735760167289 (-0.2283631748999) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_27 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3816406325408:ℝ):ℂ) + (((-0.9243107851766):ℝ):ℂ) * I)‖ ≤ 0.00000016474 := by
  have hl := lg_27
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.860634628608953372 82.860634666320528795 (-1.1792257) 0.00000006473 0.3816406325408 (-0.9243107851766) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_28 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4992632625716):ℝ):ℂ) + (((-0.8664503417047):ℝ):ℂ) * I)‖ ≤ 0.00000012918 := by
  have hl := lg_28
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.774953564173644502 83.774953614455694784 (-2.0935446) 0.00000002917 (-0.4992632625716) (-0.8664503417047) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_29 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9862838064862):ℝ):ℂ) + (((-0.1650583311815):ℝ):ℂ) * I)‖ ≤ 0.0000001578 := by
  have hl := lg_29
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.657184435548783572 84.657184485830858995 (-2.9757755) 0.00000005779 (-0.9862838064862) (-0.1650583311815) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_30 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7734680552159):ℝ):ℂ) + ((0.6338352842184:ℝ):ℂ) * I)‖ ≤ 0.0000001543 := by
  have hl := lg_30
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.509503346227079593 85.509503396509129875 2.4550909 0.00000005429 (-0.7734680552159) 0.6338352842184 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_31 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0598898132671):ℝ):ℂ) + ((0.9982049941102:ℝ):ℂ) * I)‖ ≤ 0.0000001316 := by
  have hl := lg_31
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.333872281819871183 86.333872332101946606 1.630722 0.00000003159 (-0.0598898132671) 0.9982049941102 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_32 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6730081150606:ℝ):ℂ) + ((0.7396350972355:ℝ):ℂ) * I)‖ ≤ 0.00000016196 := by
  have hl := lg_32
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.1320662996115 87.132066362464 0.832528 0.00000006195 0.6730081150606 0.7396350972355 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_33 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9982660318068:ℝ):ℂ) + ((0.058863653817:ℝ):ℂ) * I)‖ ≤ 0.00000012647 := by
  have hl := lg_33
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.905696576687589277 87.9056966269696647 0.0588977 0.00000002646 0.9982660318068 0.058863653817 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_34 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7702038636325:ℝ):ℂ) + (((-0.6377977802137):ℝ):ℂ) * I)‖ ≤ 0.00000017905 := by
  have hl := lg_34
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.656229916698467194 88.656229979550992335 (-0.6916356) 0.00000007904 0.7702038636325 (-0.6377977802137) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_35 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1498188247464:ℝ):ℂ) + (((-0.9887134669618):ℝ):ℂ) * I)‖ ≤ 0.00000013755 := by
  have hl := lg_35
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.385005587764172971 89.385005638046248394 (-1.4204113) 0.00000003754 0.1498188247464 (-0.9887134669618) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_36 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5293709859345):ℝ):ℂ) + (((-0.8483904521169):ℝ):ℂ) * I)‖ ≤ 0.00000015537 := by
  have hl := lg_36
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.093249605583902248 90.09324965586595253 (-2.1286553) 0.00000005536 (-0.5293709859345) (-0.8483904521169) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_37 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9479377988856):ℝ):ℂ) + (((-0.3184555373139):ℝ):ℂ) * I)‖ ≤ 0.00000016543 := by
  have hl := lg_37
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.782087215647276322 90.782087265929351745 (-2.8174929) 0.00000006542 (-0.9479377988856) (-0.3184555373139) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_38 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9406123761425):ℝ):ℂ) + ((0.3394824850663:ℝ):ℂ) * I)‖ ≤ 0.00000015814 := by
  have hl := lg_38
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.452553615539886023 91.452553665821961446 2.795226 0.00000005813 (-0.9406123761425) 0.3394824850663 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_39 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5407933353343):ℝ):ℂ) + ((0.8411554959993:ℝ):ℂ) * I)‖ ≤ 0.00000016181 := by
  have hl := lg_39
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.105603319204270824 92.105603369486346247 2.1421763 0.0000000618 (-0.5407933353343) 0.8411554959993 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_40 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0650889798934:ℝ):ℂ) + ((0.9978794640117:ℝ):ℂ) * I)‖ ≤ 0.00000017838 := by
  have hl := lg_40
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.742118323202028469 92.74211838605455361 1.5056613 0.00000007837 0.0650889798934 0.9978794640117 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_41 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.633394515921:ℝ):ℂ) + ((0.7738290426194:ℝ):ℂ) * I)‖ ≤ 0.00000015151 := by
  have hl := lg_41
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.36291529633654578 93.362915359189096062 0.8848643 0.0000000515 0.633394515921 0.7738290426194 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_42 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9613236845904:ℝ):ℂ) + ((0.2754210838799:ℝ):ℂ) * I)‖ ≤ 0.00000016059 := by
  have hl := lg_42
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.968751847120995626 93.968751897403071049 0.2790277 0.00000006058 0.9613236845904 0.2754210838799 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_43 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9515518062148:ℝ):ℂ) + (((-0.3074884714739):ℝ):ℂ) * I)‖ ≤ 0.0000001252 := by
  have hl := lg_43
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.56033208251068298 94.560332132792783544 (-0.3125525) 0.00000002519 0.9515518062148 (-0.3074884714739) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_44 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6289985353542:ℝ):ℂ) + (((-0.7774064847442):ℝ):ℂ) * I)‖ ≤ 0.00000015405 := by
  have hl := lg_44
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.138311553662538153 95.138311616515088435 (-0.890532) 0.00000005404 0.6289985353542 (-0.7774064847442) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_45 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1150191988798:ℝ):ℂ) + (((-0.9933632688443):ℝ):ℂ) * I)‖ ≤ 0.00000017178 := by
  have hl := lg_45
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.703301629174430717 95.70330167945650614 (-1.455522) 0.00000007177 0.1150191988798 (-0.9933632688443) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_46 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4234927063842):ℝ):ℂ) + (((-0.90589951299):ℝ):ℂ) * I)‖ ≤ 0.00000017163 := by
  have hl := lg_46
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.255873316455850606 96.255873379308426029 (-2.0080937) 0.00000007162 (-0.4234927063842) (-0.90589951299) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_47 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8293732139634):ℝ):ℂ) + (((-0.558694972143):ℝ):ℂ) * I)‖ ≤ 0.00000017709 := by
  have hl := lg_47
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.796560821916081389 96.796560884768681953 (-2.5487812) 0.00000007708 (-0.8293732139634) (-0.558694972143) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_48 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9979840664062):ℝ):ℂ) + (((-0.0634649718683):ℝ):ℂ) * I)‖ ≤ 0.00000013773 := by
  have hl := lg_48
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.325864582558851124 97.325864645411376265 (-3.078085) 0.00000003772 (-0.9979840664062) (-0.0634649718683) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_49 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8983129427706):ℝ):ℂ) + ((0.4393561843612:ℝ):ℂ) * I)‖ ≤ 0.00000012623 := by
  have hl := lg_49
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.844254088658089004 97.844254138940189568 2.6867108 0.00000002622 (-0.8983129427706) 0.4393561843612 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p141_50 : ‖exp (-((((((25141:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5712255200027):ℝ):ℂ) + ((0.8207931562139:ℝ):ℂ) * I)‖ ≤ 0.0000001681 := by
  have hl := lg_50
  refine (ecis_approx ((((25141:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.352170346792556938 98.35217040964510722 2.1787945 0.00000006809 (-0.5712255200027) 0.8207931562139 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_2 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1751643797581:ℝ):ℂ) + ((0.9845392018929:ℝ):ℂ) * I)‖ ≤ 0.00000012724 := by
  have hl := lg_2
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.4548322943146 17.4548323069056 1.3947236 0.00000002723 0.1751643797581 0.9845392018929 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_3 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8201751359775):ℝ):ℂ) + (((-0.5721125293738):ℝ):ℂ) * I)‖ ≤ 0.00000013058 := by
  have hl := lg_3
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.665254646694385848 27.66525465928541103 (-2.5325134) 0.00000003057 (-0.8201751359775) (-0.5721125293738) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_4 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9386348800679):ℝ):ℂ) + ((0.3449123972016:ℝ):ℂ) * I)‖ ≤ 0.00000015446 := by
  have hl := lg_4
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.9096645886292 34.9096646138112 2.7894472 0.00000005445 (-0.9386348800679) 0.3449123972016 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_5 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.951770971176):ℝ):ℂ) + (((-0.3068094167697):ℝ):ℂ) * I)‖ ≤ 0.00000014527 := by
  have hl := lg_5
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.528865497823611038 40.52886552300563622 (-2.8297537) 0.00000004526 (-0.951770971176) (-0.3068094167697) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_6 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4196017441056:ℝ):ℂ) + (((-0.9077083101655):ℝ):ℂ) * I)‖ ≤ 0.00000011595 := by
  have hl := lg_6
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.120086941008985848 45.12008696619101103 (-1.1377898) 0.00000001594 0.4196017441056 (-0.9077083101655) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_7 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3024130494306:ℝ):ℂ) + ((0.9531769759777:ℝ):ℂ) * I)‖ ≤ 0.00000012818 := by
  have hl := lg_7
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.001909360418996804 49.001909385601047168 1.2635731 0.00000002817 0.3024130494306 0.9531769759777 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_8 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5039950803801):ℝ):ℂ) + (((-0.8637065236214):ℝ):ℂ) * I)‖ ≤ 0.0000001633 := by
  have hl := lg_8
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.3644968829438 52.3644969207168 (-2.0990144) 0.00000006329 (-0.5039950803801) (-0.8637065236214) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_9 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3453745141311:ℝ):ℂ) + ((0.938464940735:ℝ):ℂ) * I)‖ ≤ 0.00000015397 := by
  have hl := lg_9
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.330509293388771696 55.33050931857082206 1.2181585 0.00000005396 0.3453745141311 0.938464940735 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_10 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1353496256547:ℝ):ℂ) + (((-0.9907979000962):ℝ):ℂ) * I)‖ ≤ 0.00000016531 := by
  have hl := lg_10
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.983697792138211038 57.98369782991123622 (-1.43503) 0.0000000653 0.1353496256547 (-0.9907979000962) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_11 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7689888980918):ℝ):ℂ) + ((0.63926213291:ℝ):ℂ) * I)‖ ≤ 0.00000013184 := by
  have hl := lg_11
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.383798739970698006 60.38379877774374837 2.4480543 0.00000003183 (-0.7689888980918) 0.63926213291 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_12 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9671736944936:ℝ):ℂ) + ((0.2541162031032:ℝ):ℂ) * I)‖ ≤ 0.00000013649 := by
  have hl := lg_12
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.574919235323585848 62.57491927309661103 0.2569338 0.00000003648 0.9671736944936 0.2541162031032 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_13 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.186801451552):ℝ):ℂ) + (((-0.9823976881575):ℝ):ℂ) * I)‖ ≤ 0.00000016595 := by
  have hl := lg_13
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.5905546999585694 64.590554737731619764 (-1.7587016) 0.00000006594 (-0.186801451552) (-0.9823976881575) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_14 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8854681049293):ℝ):ℂ) + ((0.4647001560702:ℝ):ℂ) * I)‖ ≤ 0.00000012426 := by
  have hl := lg_14
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.456741654733596804 66.456741692506647168 2.6582967 0.00000002425 (-0.8854681049293) 0.4647001560702 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_15 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6050893799578:ℝ):ℂ) + ((0.7961575486437:ℝ):ℂ) * I)‖ ≤ 0.00000013447 := by
  have hl := lg_15
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.194120144517996886 68.19412018229104725 0.9209182 0.00000003446 0.6050893799578 0.7961575486437 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_16 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7620709457836:ℝ):ℂ) + (((-0.6474935316993):ℝ):ℂ) * I)‖ ≤ 0.00000014866 := by
  have hl := lg_16
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.8193291772584 69.8193292276224 (-0.7042908) 0.00000004865 0.7620709457836 (-0.6474935316993) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_17 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6132304253503):ℝ):ℂ) + (((-0.7899040735504):ℝ):ℂ) * I)‖ ≤ 0.00000017515 := by
  have hl := lg_17
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.345978403839840988 71.34597845420386617 (-2.2309401) 0.00000007514 (-0.6132304253503) (-0.7899040735504) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_18 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8634582111823):ℝ):ℂ) + ((0.5044203777198:ℝ):ℂ) * I)‖ ≤ 0.00000013934 := by
  have hl := lg_18
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.785341587703371696 72.78534162547642206 2.6128821 0.00000003933 (-0.8634582111823) 0.5044203777198 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_19 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3140302178641:ℝ):ℂ) + ((0.9494129882555:ℝ):ℂ) * I)‖ ≤ 0.00000013244 := by
  have hl := lg_19
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.146862353731436746 74.146862391504512292 1.2513613 0.00000003243 0.3140302178641 0.9494129882555 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_20 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9991878070262:ℝ):ℂ) + (((-0.0402954872174):ℝ):ℂ) * I)‖ ≤ 0.00000015068 := by
  have hl := lg_20
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.438530086452811038 75.43853013681683622 (-0.0403064) 0.00000005067 0.9991878070262 (-0.0402954872174) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_21 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2972928267562:ℝ):ℂ) + (((-0.9547863505305):ℝ):ℂ) * I)‖ ≤ 0.00000015875 := by
  have hl := lg_21
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.667164007113382652 76.667164044886458198 (-1.2689403) 0.00000005874 0.2972928267562 (-0.9547863505305) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_22 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7640780888951):ℝ):ℂ) + (((-0.6451237664455):ℝ):ℂ) * I)‖ ≤ 0.00000015188 := by
  have hl := lg_22
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.838631034285298006 77.83863108464934837 (-2.4404074) 0.00000005187 (-0.7640780888951) (-0.6451237664455) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_23 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9138218138385):ℝ):ℂ) + ((0.406115368361:ℝ):ℂ) * I)‖ ≤ 0.00000017401 := by
  have hl := lg_23
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.958015319344014612 78.958015369708090158 2.7233936 0.000000074 (-0.9138218138385) 0.406115368361 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_24 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.080772983477):ℝ):ℂ) + ((0.9967325243714:ℝ):ℂ) * I)‖ ≤ 0.00000016371 := by
  have hl := lg_24
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.029751529638185848 80.02975158000221103 1.6516574 0.0000000637 (-0.080772983477) 0.9967325243714 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_25 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8117359092212:ℝ):ℂ) + ((0.5840246687263:ℝ):ℂ) * I)‖ ≤ 0.00000015269 := by
  have hl := lg_25
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.057730995647222076 81.05773104601127244 0.623678 0.00000005268 0.8117359092212 0.5840246687263 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_26 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9344880754415:ℝ):ℂ) + (((-0.3559944337453):ℝ):ℂ) * I)‖ ≤ 0.00000015132 := by
  have hl := lg_26
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.0453869942731694 82.045387044637219764 (-0.363978) 0.00000005131 0.9344880754415 (-0.3559944337453) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_27 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2536398651778:ℝ):ℂ) + (((-0.9672987226253):ℝ):ℂ) * I)‖ ≤ 0.00000015327 := by
  have hl := lg_27
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.995763940083157544 82.99576397785623309 (-1.314355) 0.00000005326 0.2536398651778 (-0.9672987226253) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_28 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6126179865559):ℝ):ℂ) + (((-0.7903791511263):ℝ):ℂ) * I)‖ ≤ 0.0000001443 := by
  have hl := lg_28
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.911573949048196804 83.911573999412247168 (-2.230165) 0.00000004429 (-0.6126179865559) (-0.7903791511263) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_29 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996147696635):ℝ):ℂ) + (((-0.0277544888059):ℝ):ℂ) * I)‖ ≤ 0.00000012881 := by
  have hl := lg_29
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.795243564535597944 84.79524361489967349 (-3.1138346) 0.0000000288 (-0.9996147696635) (-0.0277544888059) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_30 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6778582115817):ℝ):ℂ) + ((0.7351926584039:ℝ):ℂ) * I)‖ ≤ 0.0000001617 := by
  have hl := lg_30
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.648952438832596886 85.64895248919664725 2.3156418 0.00000006169 (-0.6778582115817) 0.7351926584039 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_31 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0807797149977:ℝ):ℂ) + ((0.9967319788412:ℝ):ℂ) * I)‖ ≤ 0.00000014337 := by
  have hl := lg_31
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.474665757161131066 86.474665807525206612 1.4899285 0.00000004336 0.0807797149977 0.9967319788412 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_32 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7709704494799:ℝ):ℂ) + ((0.6368709178701:ℝ):ℂ) * I)‖ ≤ 0.00000013403 := by
  have hl := lg_32
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.274161471573 87.274161534528 0.6904328 0.00000003402 0.7709704494799 0.6368709178701 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_33 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9964354498984:ℝ):ℂ) + (((-0.0843587232344):ℝ):ℂ) * I)‖ ≤ 0.00000013653 := by
  have hl := lg_33
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.049053386665083854 88.0490534370291594 (-0.0844591) 0.00000003652 0.9964354498984 (-0.0843587232344) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_34 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6702754732584:ℝ):ℂ) + (((-0.7421123836375):ℝ):ℂ) * I)‖ ≤ 0.00000016061 := by
  have hl := lg_34
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.800810698154440988 88.80081076110946617 (-0.8362164) 0.0000000606 0.6702754732584 (-0.7421123836375) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_35 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0046157104052:ℝ):ℂ) + (((-0.9999893475519):ℝ):ℂ) * I)‖ ≤ 0.00000014229 := by
  have hl := lg_35
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.530774858242607842 89.530774908606683388 (-1.5661806) 0.00000004228 0.0046157104052 (-0.9999893475519) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_36 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6478687526854):ℝ):ℂ) + (((-0.7617519801597):ℝ):ℂ) * I)‖ ≤ 0.00000013188 := by
  have hl := lg_36
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.240173882017971696 90.24017393238202206 (-2.2755796) 0.00000003187 (-0.6478687526854) (-0.7617519801597) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_37 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9845428227417):ℝ):ℂ) + (((-0.1751440259655):ℝ):ℂ) * I)‖ ≤ 0.00000015051 := by
  have hl := lg_37
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.930134850023058444 90.93013490038713399 (-2.9655406) 0.0000000505 (-0.9845428227417) (-0.1751440259655) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_38 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8797273973601):ℝ):ℂ) + ((0.4754783972359:ℝ):ℂ) * I)‖ ≤ 0.00000015966 := by
  have hl := lg_38
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.601694648046036746 91.601694698410112292 2.6460849 0.00000005965 (-0.8797273973601) 0.4754783972359 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_39 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4088320225119):ℝ):ℂ) + ((0.912609652242:ℝ):ℂ) * I)‖ ≤ 0.00000016106 := by
  have hl := lg_39
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.255809346652955248 92.255809397017030794 1.9919702 0.00000006105 (-0.4088320225119) 0.912609652242 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_40 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2146945993045:ℝ):ℂ) + ((0.9766812320453:ℝ):ℂ) * I)‖ ≤ 0.00000013604 := by
  have hl := lg_40
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.893362380767411038 92.89336244372243622 1.3544172 0.00000003603 0.2146945993045 0.9766812320453 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_41 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.743432807859:ℝ):ℂ) + ((0.6688106310451:ℝ):ℂ) * I)‖ ≤ 0.00000015669 := by
  have hl := lg_41
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.51517175101813356 93.515171813973183924 0.7326078 0.00000005668 0.743432807859 0.6688106310451 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_42 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9920997051348:ℝ):ℂ) + ((0.1254518834908:ℝ):ℂ) * I)‖ ≤ 0.00000014411 := by
  have hl := lg_42
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.121996301427982652 94.121996351792058198 0.1257833 0.0000000441 0.9920997051348 0.1254518834908 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_43 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.89303019254:ℝ):ℂ) + (((-0.4499967502239):ℝ):ℂ) * I)‖ ≤ 0.0000001299 := by
  have hl := lg_43
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.71454128721148796 94.714541337575588688 (-0.4667617) 0.00000002989 0.89303019254 (-0.4499967502239) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_44 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.50131037363:ℝ):ℂ) + (((-0.8652675362516):ℝ):ℂ) * I)‖ ≤ 0.00000017911 := by
  have hl := lg_44
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.293463328599898006 95.29346339155494837 (-1.0456838) 0.0000000791 0.50131037363 (-0.8652675362516) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_45 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.040787555533):ℝ):ℂ) + (((-0.9991678414127):ℝ):ℂ) * I)‖ ≤ 0.0000001339 := by
  have hl := lg_45
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.859374791212382734 95.85937484157645828 (-1.6115952) 0.00000003389 (-0.040787555533) (-0.9991678414127) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_46 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.559905443146):ℝ):ℂ) + (((-0.8285565126931):ℝ):ℂ) * I)‖ ≤ 0.00000016893 := by
  have hl := lg_46
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.412847613658614612 96.412847676613690158 (-2.165068) 0.00000006892 (-0.559905443146) (-0.8285565126931) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_47 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9068888558195):ℝ):ℂ) + (((-0.4213699123877):ℝ):ℂ) * I)‖ ≤ 0.00000013418 := by
  have hl := lg_47
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.954416873532904878 96.954416936488005606 (-2.7066373) 0.00000003417 (-0.9068888558195) (-0.4213699123877) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_48 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9954708028827):ℝ):ℂ) + ((0.0950677659549:ℝ):ℂ) * I)‖ ≤ 0.00000017205 := by
  have hl := lg_48
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.484583823952785848 97.48458388690781103 3.0463811 0.00000007204 (-0.9954708028827) 0.0950677659549 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_49 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8170926950558):ℝ):ℂ) + ((0.5765063118736:ℝ):ℂ) * I)‖ ≤ 0.00000015634 := by
  have hl := lg_49
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.003818720837993608 98.003818771202094336 2.5271462 0.00000005633 (-0.8170926950558) 0.5765063118736 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_50 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4328079641675):ℝ):ℂ) + ((0.9014861430711:ℝ):ℂ) * I)‖ ≤ 0.00000013806 := by
  have hl := lg_50
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.512563289961822076 98.51256335291687244 2.0184016 0.00000003805 (-0.4328079641675) 0.9014861430711 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_51 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0510423371648:ℝ):ℂ) + ((0.9986964903396:ℝ):ℂ) * I)‖ ≤ 0.00000016435 := by
  have hl := lg_51
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.011233050534226836 99.0112331134892772 1.5197318 0.00000006434 0.0510423371648 0.9986964903396 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_52 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.514179499804:ℝ):ℂ) + ((0.8576825997893:ℝ):ℂ) * I)‖ ≤ 0.00000013668 := by
  have hl := lg_52
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.5002192885877694 99.500219351542819764 1.0307456 0.00000003667 0.514179499804 0.8576825997893 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_53 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8519627167606:ℝ):ℂ) + ((0.5236024534415:ℝ):ℂ) * I)‖ ≤ 0.00000018055 := by
  have hl := lg_53
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.979890934339785708 99.979890997294861254 0.5510739 0.00000008054 0.8519627167606 0.5236024534415 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_54 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9967721740032:ℝ):ℂ) + ((0.0802822093182:ℝ):ℂ) * I)‖ ≤ 0.0000001699 := by
  have hl := lg_54
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.450596234397757544 100.45059628476183309 0.0803687 0.00000006989 0.9967721740032 0.0802822093182 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_55 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9280329526612:ℝ):ℂ) + (((-0.3724981057334):ℝ):ℂ) * I)‖ ≤ 0.00000017709 := by
  have hl := lg_55
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.912664237794309044 100.91266430074938459 (-0.3816994) 0.00000007708 0.9280329526612 (-0.3724981057334) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_56 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6708504090061:ℝ):ℂ) + (((-0.7415926973321):ℝ):ℂ) * I)‖ ≤ 0.00000017153 := by
  have hl := lg_56
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.366406243362796804 101.366406306317847168 (-0.8354414) 0.00000007152 0.6708504090061 (-0.7415926973321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_57 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.28561128952:ℝ):ℂ) + (((-0.9583455490055):ℝ):ℂ) * I)‖ ≤ 0.00000013593 := by
  have hl := lg_57
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.812117000425822594 101.812117050789923322 (-1.2811521) 0.00000003592 0.28561128952 (-0.9583455490055) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_58 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1477715186444):ℝ):ℂ) + (((-0.9890215256894):ℝ):ℂ) * I)‖ ≤ 0.00000015604 := by
  have hl := lg_58
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.250075858850197944 102.25007592180527349 (-1.719111) 0.00000005603 (-0.1477715186444) (-0.9890215256894) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_59 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5470086311045):ℝ):ℂ) + (((-0.8371269661698):ℝ):ℂ) * I)‖ ≤ 0.00000013518 := by
  have hl := lg_59
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.680547879704090544 102.680547942659191272 (-2.149583) 0.00000003517 (-0.5470086311045) (-0.8371269661698) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p182_60 : ‖exp (-((((((25182:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8425625486066):ℝ):ℂ) + (((-0.5385985068827):ℝ):ℂ) * I)‖ ≤ 0.00000018124 := by
  have hl := lg_60
  refine (ecis_approx ((((25182:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.103784733147196886 103.10378479610224725 (-2.5728198) 0.00000008123 (-0.8425625486066) (-0.5385985068827) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_2 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2125617011619:ℝ):ℂ) + ((0.9771476465709:ℝ):ℂ) * I)‖ ≤ 0.00000013232 := by
  have hl := lg_2
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.4929553892311 17.4929554018496 1.3566005 0.00000003231 0.2125617011619 0.9771476465709 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_3 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8532264763132):ℝ):ℂ) + (((-0.5215405833128):ℝ):ℂ) * I)‖ ≤ 0.00000010647 := by
  have hl := lg_3
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.725678322556834868 27.725678335175360105 (-2.5929371) 0.00000000646 (-0.8532264763132) (-0.5215405833128) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_4 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9096350879001):ℝ):ℂ) + ((0.4154082410507:ℝ):ℂ) * I)‖ ≤ 0.00000016064 := by
  have hl := lg_4
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.9859107784622 34.9859108036992 2.7132011 0.00000006063 (-0.9096350879001) 0.4154082410507 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_5 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9751675822588):ℝ):ℂ) + (((-0.2214682510319):ℝ):ℂ) * I)‖ ≤ 0.00000016011 := by
  have hl := lg_5
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.617384582978892533 40.61738460821591777 (-2.9182728) 0.0000000601 (-0.9751675822588) (-0.2214682510319) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_6 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3282588823307:ℝ):ℂ) + (((-0.9445877969628):ℝ):ℂ) * I)‖ ≤ 0.00000013848 := by
  have hl := lg_6
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.218633711787934868 45.218633737024960105 (-1.2363366) 0.00000003847 0.3282588823307 (-0.9445877969628) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_7 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.402501948129:ℝ):ℂ) + ((0.9154191290072:ℝ):ℂ) * I)‖ ≤ 0.00000013886 := by
  have hl := lg_7
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.108934418588445014 49.108934443825495488 1.156548 0.00000003885 0.402501948129 0.9154191290072 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_8 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5992687611565):ℝ):ℂ) + (((-0.8005479073047):ℝ):ℂ) * I)‖ ≤ 0.00000014813 := by
  have hl := lg_8
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.4788661676933 52.4788662055488 (-2.2133837) 0.00000004812 (-0.5992687611565) (-0.8005479073047) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_9 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4559908462178:ℝ):ℂ) + ((0.889984465126:ℝ):ℂ) * I)‖ ≤ 0.00000011952 := by
  have hl := lg_9
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.451356645113669736 55.45135667035072021 1.0973111 0.00000001951 0.4559908462178 0.889984465126 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_10 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0091240001986:ℝ):ℂ) + (((-0.9999583754438):ℝ):ℂ) * I)‖ ≤ 0.00000014546 := by
  have hl := lg_10
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.110339972209992533 58.11034001006551777 (-1.5616722) 0.00000004545 0.0091240001986 (-0.9999583754438) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_11 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6782465192496):ℝ):ℂ) + ((0.7348344433308:ℝ):ℂ) * I)‖ ≤ 0.00000014601 := by
  have hl := lg_11
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.515682979931717321 60.515683017787267795 2.3161701 0.000000046 (-0.6782465192496) 0.7348344433308 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_12 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9927769972341:ℝ):ℂ) + ((0.119974304594:ℝ):ℂ) * I)‖ ≤ 0.00000016709 := by
  have hl := lg_12
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.711589101019034868 62.711589138874560105 0.120264 0.00000006708 0.9927769972341 0.119974304594 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_13 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3230756001521):ℝ):ℂ) + (((-0.9463731592688):ℝ):ℂ) * I)‖ ≤ 0.00000015723 := by
  have hl := lg_13
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.7316269145760629 64.731626952431613374 (-1.8997739) 0.00000005722 (-0.3230756001521) (-0.9463731592688) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_14 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8089432074976):ℝ):ℂ) + ((0.5878867977686:ℝ):ℂ) * I)‖ ≤ 0.00000016671 := by
  have hl := lg_14
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.601889807819545014 66.601889845675095488 2.5131486 0.0000000667 (-0.8089432074976) 0.5878867977686 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_15 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7165340544828:ℝ):ℂ) + ((0.6975521118644:ℝ):ℂ) * I)‖ ≤ 0.00000016443 := by
  have hl := lg_15
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.343062905535727401 68.343062943391277875 0.7719755 0.00000006442 0.7165340544828 0.6975521118644 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_16 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.654871916272:ℝ):ℂ) + (((-0.7557398846682):ℝ):ℂ) * I)‖ ≤ 0.00000012844 := by
  have hl := lg_16
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.9718215569244 69.9718216073984 (-0.8567832) 0.00000002843 0.654871916272 (-0.7557398846682) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_17 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7283908726961):ℝ):ℂ) + (((-0.6851618323754):ℝ):ℂ) * I)‖ ≤ 0.00000014128 := by
  have hl := lg_17
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.501805137705744858 71.501805188179770095 (-2.3867668) 0.00000004127 (-0.7283908726961) (-0.6851618323754) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_18 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7727200355888):ℝ):ℂ) + ((0.634746994132:ℝ):ℂ) * I)‖ ≤ 0.00000015183 := by
  have hl := lg_18
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.944312034344769736 72.94431207220032021 2.4539116 0.00000005182 (-0.7727200355888) 0.634746994132 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_19 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4630020144689:ℝ):ℂ) + ((0.8863572274189:ℝ):ℂ) * I)‖ ≤ 0.00000014926 := by
  have hl := lg_19
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.308806497542699911 74.308806535398275622 1.0894172 0.00000004925 0.4630020144689 0.8863572274189 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_20 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9790463862375:ℝ):ℂ) + (((-0.203637358054):ℝ):ℂ) * I)‖ ≤ 0.00000012578 := by
  have hl := lg_20
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.603295361441092533 75.60329541191511777 (-0.2050717) 0.00000002577 0.9790463862375 (-0.203637358054) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_21 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1340029076375:ℝ):ℂ) + (((-0.9909809386384):ℝ):ℂ) * I)‖ ≤ 0.00000014502 := by
  have hl := lg_21
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.834612741145279882 76.834612779000855593 (-1.4363891) 0.00000004501 0.1340029076375 (-0.9909809386384) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_22 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8622109772128):ℝ):ℂ) + (((-0.5065493368781):ℝ):ℂ) * I)‖ ≤ 0.0000001335 := by
  have hl := lg_22
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.008638369162817321 78.008638419636867795 (-2.6104147) 0.00000003349 (-0.8622109772128) (-0.5065493368781) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_23 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8305782264742):ℝ):ℂ) + ((0.5569019748969:ℝ):ℂ) * I)‖ ≤ 0.00000015832 := by
  have hl := lg_23
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.130467501162929742 79.130467551637005453 2.5509415 0.00000005831 (-0.8305782264742) 0.5569019748969 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_24 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0937937580235:ℝ):ℂ) + ((0.9955916486973:ℝ):ℂ) * I)‖ ≤ 0.0000001474 := by
  have hl := lg_24
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.204544490250134868 80.204544540724160105 1.4768645 0.00000004739 0.0937937580235 0.9955916486973 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_25 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9019035873458:ℝ):ℂ) + ((0.4319374018683:ℝ):ℂ) * I)‖ ≤ 0.00000012739 := by
  have hl := lg_25
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.234769165957785066 81.23476921643183554 0.4466398 0.00000002738 0.9019035873458 0.4319374018683 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_26 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8560728578718:ℝ):ℂ) + (((-0.5168551654141):ℝ):ℂ) * I)‖ ≤ 0.00000016096 := by
  have hl := lg_26
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.2245823038071629 82.224582354281213374 (-0.5431733) 0.00000006095 0.8560728578718 (-0.5168551654141) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_27 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0750995541603:ℝ):ℂ) + (((-0.9971760411105):ℝ):ℂ) * I)‖ ≤ 0.00000012568 := by
  have hl := lg_27
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.177034967670504604 83.177035005526080315 (-1.495626) 0.00000002567 0.0750995541603 (-0.9971760411105) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_28 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7464025404666):ℝ):ℂ) + (((-0.6654947389364):ℝ):ℂ) * I)‖ ≤ 0.00000015421 := by
  have hl := lg_28
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.094845197050645014 84.094845247524695488 (-2.4134362) 0.0000000542 (-0.7464025404666) (-0.6654947389364) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_29 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9876313922933):ℝ):ℂ) + ((0.1567935986383:ℝ):ℂ) * I)‖ ≤ 0.0000001654 := by
  have hl := lg_29
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 84.980444835127666004 84.980444885601741715 2.9841494 0.00000006539 (-0.9876313922933) 0.1567935986383 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_30 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5293037069073):ℝ):ℂ) + ((0.8484324285685:ℝ):ℂ) * I)‖ ≤ 0.00000014474 := by
  have hl := lg_30
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.836018294766827401 85.836018345240877875 2.128576 0.00000004473 (-0.5293037069073) 0.8484324285685 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_31 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2664780779313:ℝ):ℂ) + ((0.9638409796133:ℝ):ℂ) * I)‖ ≤ 0.00000014718 := by
  have hl := lg_31
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.663535053350626031 86.663535103824701742 1.3010592 0.00000004717 0.2664780779313 0.9638409796133 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_32 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8776701382892:ℝ):ℂ) + ((0.4792651962696:ℝ):ℂ) * I)‖ ≤ 0.00000015437 := by
  have hl := lg_32
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.4647769461555 87.464777009248 0.4998173 0.00000005436 0.8776701382892 0.4792651962696 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_33 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9619438719559:ℝ):ℂ) + (((-0.2732471174715):ℝ):ℂ) * I)‖ ≤ 0.00000015246 := by
  have hl := lg_33
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.241361302488552189 88.2413613529626279 (-0.276767) 0.00000005245 0.9619438719559 (-0.2732471174715) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_34 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5146762690299:ℝ):ℂ) + (((-0.8573845917075):ℝ):ℂ) * I)‖ ≤ 0.00000017359 := by
  have hl := lg_34
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.994760526936844858 88.994760590029370095 (-1.0301663) 0.00000007358 0.5146762690299 (-0.8573845917075) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_35 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1897704798783):ℝ):ℂ) + (((-0.9818284804211):ℝ):ℂ) * I)‖ ≤ 0.00000015154 := by
  have hl := lg_35
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.726319001567337547 89.726319052041413258 (-1.7617247) 0.00000005153 (-0.1897704798783) (-0.9818284804211) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_36 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7844921503196):ℝ):ℂ) + (((-0.6201387474132):ℝ):ℂ) * I)‖ ≤ 0.00000017355 := by
  have hl := lg_36
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.437267423575869736 90.43726747404992021 (-2.4726731) 0.00000007354 (-0.7844921503196) (-0.6201387474132) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_37 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997457940807):ℝ):ℂ) + ((0.0225465426248:ℝ):ℂ) * I)‖ ≤ 0.00000017255 := by
  have hl := lg_37
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.128735335161302754 91.128735385635378465 3.1190442 0.00000007254 (-0.9997457940807) 0.0225465426248 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_38 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7676853829497):ℝ):ℂ) + ((0.6408269288715:ℝ):ℂ) * I)‖ ≤ 0.00000012957 := by
  have hl := lg_38
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.801761886773799911 91.801761937247875622 2.4460177 0.00000002956 (-0.7676853829497) 0.6408269288715 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_39 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2179153466433):ℝ):ℂ) + ((0.975967674514:ℝ):ℂ) * I)‖ ≤ 0.00000017058 := by
  have hl := lg_39
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.457305237132897768 92.457305287606973479 1.7904743 0.00000007057 (-0.2179153466433) 0.975967674514 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_40 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4070915305515:ℝ):ℂ) + ((0.9133873689477:ℝ):ℂ) * I)‖ ≤ 0.00000015704 := by
  have hl := lg_40
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.096250750672192533 93.09625081376471777 1.1515288 0.00000005703 0.4070915305515 0.9133873689477 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_41 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8636342787544:ℝ):ℂ) + ((0.5041188674909:ℝ):ℂ) * I)‖ ≤ 0.00000017003 := by
  have hl := lg_41
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.71941821461538546 93.719418277707935934 0.5283614 0.00000007002 0.8636342787544 0.5041188674909 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_42 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9968185859657:ℝ):ℂ) + (((-0.0797038686225):ℝ):ℂ) * I)‖ ≤ 0.00000017317 := by
  have hl := lg_42
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.327568130376379882 94.327568180850455593 (-0.0797885) 0.00000007316 0.9968185859657 (-0.0797038686225) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_43 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7815637623346:ℝ):ℂ) + (((-0.6238253645094):ℝ):ℂ) * I)‖ ≤ 0.00000013631 := by
  have hl := lg_43
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.92140729351744586 94.921407343991546808 (-0.6736277) 0.0000000363 0.7815637623346 (-0.6238253645094) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_44 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3117004603653:ℝ):ℂ) + (((-0.9501804160306):ℝ):ℂ) * I)‖ ≤ 0.00000014931 := by
  have hl := lg_44
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.501593758393917321 95.501593821486467795 (-1.2538142) 0.0000000493 0.3117004603653 (-0.9501804160306) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_45 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2475640911364):ℝ):ℂ) + (((-0.9688715192318):ℝ):ℂ) * I)‖ ≤ 0.00000017089 := by
  have hl := lg_45
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.068741228092562269 96.06874127856663798 (-1.8209616) 0.00000007088 (-0.2475640911364) (-0.9688715192318) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_46 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7207245699647):ℝ):ℂ) + (((-0.6932215332935):ℝ):ℂ) * I)‖ ≤ 0.00000014581 := by
  have hl := lg_46
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.623422890394029742 96.623422953486605453 (-2.3756433) 0.0000000458 (-0.7207245699647) (-0.6932215332935) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_47 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9751947269375):ℝ):ℂ) + (((-0.2213486938222):ℝ):ℂ) * I)‖ ≤ 0.00000014697 := by
  have hl := lg_47
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.166174991555472973 97.166175054648073921 (-2.9183954) 0.00000004696 (-0.9751947269375) (-0.2213486938222) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_48 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9529030756303):ℝ):ℂ) + ((0.3032750043162:ℝ):ℂ) * I)‖ ≤ 0.00000013541 := by
  have hl := lg_48
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.697499879481234868 97.697499942573760105 2.833465 0.0000000354 (-0.9529030756303) 0.3032750043162 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_49 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6759844371938):ℝ):ℂ) + ((0.7369158979501:ℝ):ℂ) * I)‖ ≤ 0.00000017279 := by
  have hl := lg_49
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.217868837176890028 98.217868887650990976 2.3130961 0.00000007278 (-0.6759844371938) 0.7369158979501 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_50 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2303564548914):ℝ):ℂ) + ((0.9731063167449:ℝ):ℂ) * I)‖ ≤ 0.0000001597 := by
  have hl := lg_50
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.727724555188885066 98.72772461828143554 1.8032403 0.00000005969 (-0.2303564548914) 0.9731063167449 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_51 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2641426828733:ℝ):ℂ) + ((0.9644836147309:ℝ):ℂ) * I)‖ ≤ 0.00000015463 := by
  have hl := lg_51
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.227483460262579726 99.2274835233551302 1.3034814 0.00000005462 0.2641426828733 0.9644836147309 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_52 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6870121114902:ℝ):ℂ) + ((0.7266459651479:ℝ):ℂ) * I)‖ ≤ 0.00000014127 := by
  have hl := lg_52
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.7175376930382629 99.717537756130813374 0.8134272 0.00000004126 0.6870121114902 0.7266459651479 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_53 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9451613999534:ℝ):ℂ) + ((0.326603625268:ℝ):ℂ) * I)‖ ≤ 0.00000013775 := by
  have hl := lg_53
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.198256989513667378 100.198257052606243089 0.3327079 0.00000003774 0.9451613999534 0.326603625268 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_54 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9903515107769:ℝ):ℂ) + (((-0.1385780830501):ℝ):ℂ) * I)‖ ≤ 0.00000015799 := by
  have hl := lg_54
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.669990356901604604 100.669990407375680315 (-0.1390255) 0.00000005798 0.9903515107769 (-0.1385780830501) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_55 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8241465175087:ℝ):ℂ) + (((-0.5663766570739):ℝ):ℂ) * I)‖ ≤ 0.00000015198 := by
  have hl := lg_55
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.133067562910609854 101.133067626003185565 (-0.6021027) 0.00000005197 0.8241465175087 (-0.5663766570739) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_56 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.491630024221:ℝ):ℂ) + (((-0.8708041796434):ℝ):ℂ) * I)‖ ≤ 0.00000013452 := by
  have hl := lg_56
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.587800586281745014 101.587800649374295488 (-1.0568357) 0.00000003451 0.491630024221 (-0.8708041796434) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_57 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0672256881088:ℝ):ℂ) + (((-0.9977377946425):ℝ):ℂ) * I)‖ ≤ 0.00000015572 := by
  have hl := lg_57
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.034484820099534779 102.034484870573635727 (-1.5035199) 0.00000005571 0.0672256881088 (-0.9977377946425) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_58 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3631430051272):ℝ):ℂ) + (((-0.9317334156424):ℝ):ℂ) * I)‖ ≤ 0.00000017259 := by
  have hl := lg_58
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.473400224358766004 102.473400287451341715 (-1.9424353) 0.00000007258 (-0.3631430051272) (-0.9317334156424) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_59 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7194785907247):ℝ):ℂ) + (((-0.6945146200489):ℝ):ℂ) * I)‖ ≤ 0.00000017584 := by
  have hl := lg_59
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.904812439047420104 102.904812502140021052 (-2.3738476) 0.00000007583 (-0.7194785907247) (-0.6945146200489) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p237_60 : ‖exp (-((((((25237:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9415534447445):ℝ):ℂ) + (((-0.336863637852):ℝ):ℂ) * I)‖ ≤ 0.00000013223 := by
  have hl := lg_60
  refine (ecis_approx ((((25237:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.328973683997927401 103.328973747090477875 (-2.7980088) 0.00000003222 (-0.9415534447445) (-0.336863637852) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_2 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.24965012902:ℝ):ℂ) + ((0.9683361054305:ℝ):ℂ) * I)‖ ≤ 0.00000013741 := by
  have hl := lg_2
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.5310784841476 17.5310784967936 1.3184774 0.0000000374 0.24965012902 0.9683361054305 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_3 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8831636143872):ℝ):ℂ) + (((-0.469065059585):ℝ):ℂ) * I)‖ ≤ 0.00000013031 := by
  have hl := lg_3
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.786101998419283888 27.78610201106530918 (-2.6533608) 0.0000000303 (-0.8831636143872) (-0.469065059585) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_4 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8753496744848):ℝ):ℂ) + ((0.4834903797256:ℝ):ℂ) * I)‖ ≤ 0.00000015052 := by
  have hl := lg_4
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.0621569682952 35.0621569935872 2.6369549 0.00000005051 (-0.8753496744848) 0.4834903797256 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_5 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.990928114549):ℝ):ℂ) + (((-0.1343929736968):ℝ):ℂ) * I)‖ ≤ 0.00000015036 := by
  have hl := lg_5
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.705903668134174028 40.70590369342619932 (-3.0067918) 0.00000005035 (-0.990928114549) (-0.1343929736968) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_6 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2337308199901:ℝ):ℂ) + (((-0.9723013441247):ℝ):ℂ) * I)‖ ≤ 0.00000015762 := by
  have hl := lg_6
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.317180482566883888 45.31718050785890918 (-1.3348833) 0.00000005761 0.2337308199901 (-0.9723013441247) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_7 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4979847521487:ℝ):ℂ) + ((0.8671857855312:ℝ):ℂ) * I)‖ ≤ 0.00000014463 := by
  have hl := lg_7
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.215959476757893224 49.215959502049943808 1.049523 0.00000004462 0.4979847521487 0.8671857855312 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_8 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6867123453226):ℝ):ℂ) + (((-0.7269292639314):ℝ):ℂ) * I)‖ ≤ 0.00000013296 := by
  have hl := lg_8
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.5932354524428 52.5932354903808 (-2.327753) 0.00000003295 (-0.6867123453226) (-0.7269292639314) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_9 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5599558627479:ℝ):ℂ) + ((0.8285224389081:ℝ):ℂ) * I)‖ ≤ 0.00000015753 := by
  have hl := lg_9
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.572203996838567776 55.57220402213061836 0.9764638 0.00000005752 0.5599558627479 0.8285224389081 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_10 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1172477627522):ℝ):ℂ) + (((-0.993102694654):ℝ):ℂ) * I)‖ ≤ 0.00000012562 := by
  have hl := lg_10
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.236982152281774028 58.23698219021979932 (-1.6883144) 0.00000002561 (-0.1172477627522) (-0.993102694654) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_11 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5757241063566):ℝ):ℂ) + ((0.8176440260588:ℝ):ℂ) * I)‖ ≤ 0.00000015192 := by
  have hl := lg_11
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.647567219892736636 60.64756725783078722 2.1842858 0.00000005191 (-0.5757241063566) 0.8176440260588 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_12 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9998654262411:ℝ):ℂ) + (((-0.0164051640589):ℝ):ℂ) * I)‖ ≤ 0.00000013287 := by
  have hl := lg_12
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.848258966714483888 62.84825900465250918 (-0.0164059) 0.00000003286 0.9998654262411 (-0.0164051640589) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_13 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4529306610293):ℝ):ℂ) + (((-0.8915457454864):ℝ):ℂ) * I)‖ ≤ 0.00000014262 := by
  have hl := lg_13
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.8726991291935564 64.872699167131606984 (-2.0408461) 0.00000004261 (-0.4529306610293) (-0.8915457454864) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_14 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7154053486182):ℝ):ℂ) + ((0.6987096586867:ℝ):ℂ) * I)‖ ≤ 0.00000011988 := by
  have hl := lg_14
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.747037960905493224 66.747037998843543808 2.3680004 0.00000001987 (-0.7154053486182) 0.6987096586867 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_15 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8121126113055:ℝ):ℂ) + ((0.5835007339829:ℝ):ℂ) * I)‖ ≤ 0.00000012553 := by
  have hl := lg_15
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.492005666553457916 68.4920057044915085 0.6230327 0.00000002552 0.8121126113055 0.5835007339829 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_16 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5324740267606:ℝ):ℂ) + (((-0.8464463425554):ℝ):ℂ) * I)‖ ≤ 0.0000001424 := by
  have hl := lg_16
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.1243139365904 70.1243139871744 (-1.0092756) 0.00000004239 0.5324740267606 (-0.8464463425554) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_17 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8259003218276):ℝ):ℂ) + (((-0.5638161565126):ℝ):ℂ) * I)‖ ≤ 0.0000001432 := by
  have hl := lg_17
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.657631871571648728 71.65763192215567402 (-2.5425935) 0.00000004319 (-0.8259003218276) (-0.5638161565126) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_18 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6624951383714):ℝ):ℂ) + ((0.7490662131053:ℝ):ℂ) * I)‖ ≤ 0.00000013278 := by
  have hl := lg_18
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.103282480986167776 73.10328251892421836 2.2949412 0.00000003277 (-0.6624951383714) 0.7490662131053 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_19 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5998577649201:ℝ):ℂ) + ((0.8001066565559:ℝ):ℂ) * I)‖ ≤ 0.00000014482 := by
  have hl := lg_19
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.470750641353963076 74.470750679292038952 0.927473 0.00000004481 0.5998577649201 0.8001066565559 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_20 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9323862765357:ℝ):ℂ) + (((-0.3614634578044):ℝ):ℂ) * I)‖ ≤ 0.00000014974 := by
  have hl := lg_20
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.768060636429374028 75.76806068701339932 (-0.369837) 0.00000004973 0.9323862765357 (-0.3614634578044) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_21 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0330354614228):ℝ):ℂ) + (((-0.9994541801845):ℝ):ℂ) * I)‖ ≤ 0.00000012698 := by
  have hl := lg_21
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.002061475177177112 77.002061513115252988 (-1.6038378) 0.00000002697 (-0.0330354614228) (-0.9994541801845) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_22 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9354837913289):ℝ):ℂ) + (((-0.3533696025282):ℝ):ℂ) * I)‖ ≤ 0.00000016848 := by
  have hl := lg_22
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.178645704040336636 78.17864575462438722 (-2.780422) 0.00000006847 (-0.9354837913289) (-0.3533696025282) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_23 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7226945569549):ℝ):ℂ) + ((0.6911675464892:ℝ):ℂ) * I)‖ ≤ 0.00000014025 := by
  have hl := lg_23
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.302919682981844872 79.302919733565920748 2.3784893 0.00000004024 (-0.7226945569549) 0.6911675464892 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_24 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2655022453375:ℝ):ℂ) + ((0.964110241477:ℝ):ℂ) * I)‖ ≤ 0.00000014249 := by
  have hl := lg_24
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.379337450862083888 80.37933750144610918 1.3020715 0.00000004248 0.2655022453375 0.964110241477 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_25 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9638770856814:ℝ):ℂ) + ((0.2663474492057:ℝ):ℂ) * I)‖ ≤ 0.00000015708 := by
  have hl := lg_25
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.411807336268348056 81.41180738685239864 0.2696016 0.00000005707 0.9638770856814 0.2663474492057 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_26 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7502418031532:ℝ):ℂ) + (((-0.6611635476956):ℝ):ℂ) * I)‖ ≤ 0.00000017061 := by
  have hl := lg_26
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.4037776133411564 82.403777663925206984 (-0.7223686) 0.0000000706 0.7502418031532 (-0.6611635476956) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_27 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1059017164385):ℝ):ℂ) + (((-0.9943766019245):ℝ):ℂ) * I)‖ ≤ 0.00000013988 := by
  have hl := lg_27
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.358305995257851664 83.35830603319592754 (-1.676897) 0.00000003987 (-0.1059017164385) (-0.9943766019245) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_28 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8551868235783):ℝ):ℂ) + (((-0.5183198787437):ℝ):ℂ) * I)‖ ≤ 0.0000001483 := by
  have hl := lg_28
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.278116445053093224 84.278116495637143808 (-2.5967075) 0.00000004829 (-0.8551868235783) (-0.5183198787437) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_29 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9418694789518):ℝ):ℂ) + ((0.3359789940392:ℝ):ℂ) * I)‖ ≤ 0.0000001558 := by
  have hl := lg_29
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.165646105719734064 85.16564615630380994 2.7989482 0.00000005579 (-0.9418694789518) 0.3359789940392 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_30 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3622808100697):ℝ):ℂ) + ((0.9320689967232:ℝ):ℂ) * I)‖ ≤ 0.00000014983 := by
  have hl := lg_30
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.023084150701057916 86.0230842012851085 1.9415101 0.00000004982 (-0.3622808100697) 0.9320689967232 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_31 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.442698961535:ℝ):ℂ) + ((0.896670301424:ℝ):ℂ) * I)‖ ≤ 0.00000015099 := by
  have hl := lg_31
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.852404349540120996 86.852404400124196872 1.1121899 0.00000005098 0.442698961535 0.896670301424 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_32 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9525767642866:ℝ):ℂ) + ((0.3042983866887:ℝ):ℂ) * I)‖ ≤ 0.00000017979 := by
  have hl := lg_32
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.655392420738 87.655392483968 0.3092018 0.00000007978 0.9525767642866 0.3042983866887 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_33 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8919868717317:ℝ):ℂ) + (((-0.452061301881):ℝ):ℂ) * I)‖ ≤ 0.0000001684 := by
  have hl := lg_33
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.433669218312020524 88.4336692688960964 (-0.4690749) 0.00000006839 0.8919868717317 (-0.452061301881) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_34 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3397774193034:ℝ):ℂ) + (((-0.9405058773509):ℝ):ℂ) * I)‖ ≤ 0.00000014481 := by
  have hl := lg_34
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.188710355719248728 89.18871041894927402 (-1.2241161) 0.0000000448 0.3397774193034 (-0.9405058773509) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_35 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3769235075982):ℝ):ℂ) + (((-0.9262443896818):ℝ):ℂ) * I)‖ ≤ 0.00000015564 := by
  have hl := lg_35
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.921863144892067252 89.921863195476143128 (-1.9572689) 0.00000005563 (-0.3769235075982) (-0.9262443896818) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_36 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8907398529946):ℝ):ℂ) + (((-0.4545134917477):ℝ):ℂ) * I)‖ ≤ 0.0000001354 := by
  have hl := lg_36
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.634360965133767776 90.63436101571781836 (-2.6697667) 0.00000003539 (-0.8907398529946) (-0.4545134917477) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_37 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9756460913541):ℝ):ℂ) + ((0.2193506419561:ℝ):ℂ) * I)‖ ≤ 0.0000001632 := by
  have hl := lg_37
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.327335820299547064 91.32733587088362294 2.9204438 0.00000006319 (-0.9756460913541) 0.2193506419561 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_38 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6250176733921):ℝ):ℂ) + ((0.7806105994241:ℝ):ℂ) * I)‖ ≤ 0.00000016841 := by
  have hl := lg_38
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.001829125501563076 92.001829176085638952 2.2459505 0.0000000684 (-0.6250176733921) 0.7806105994241 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_39 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.01818117141):ℝ):ℂ) + ((0.9998347088424:ℝ):ℂ) * I)‖ ≤ 0.00000017052 := by
  have hl := lg_39
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.658801127612840288 92.658801178196916164 1.5889785 0.00000007051 (-0.01818117141) 0.9998347088424 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_40 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.582788389957:ℝ):ℂ) + ((0.8126239551793:ℝ):ℂ) * I)‖ ≤ 0.00000017613 := by
  have hl := lg_40
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.299139120576974028 93.29913918380699932 0.9486405 0.00000007612 0.582788389957 0.8126239551793 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_41 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9479329753886:ℝ):ℂ) + ((0.318469895235:ℝ):ℂ) * I)‖ ≤ 0.00000013376 := by
  have hl := lg_41
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.92366467821263736 93.923664741442687944 0.3241149 0.00000003375 0.9479329753886 0.318469895235 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_42 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9595602611898:ℝ):ℂ) + (((-0.2815032950879):ℝ):ℂ) * I)‖ ≤ 0.00000014838 := by
  have hl := lg_42
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.533139959324777112 94.533140009908852988 (-0.2853604) 0.00000004837 0.9595602611898 (-0.2815032950879) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_43 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.63677055278:ℝ):ℂ) + (((-0.7710533464763):ℝ):ℂ) * I)‖ ≤ 0.00000014273 := by
  have hl := lg_43
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.12827329982340376 95.128273350407504928 (-0.8804937) 0.00000004272 0.63677055278 (-0.7710533464763) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_44 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1086368955606:ℝ):ℂ) + (((-0.9940814981292):ℝ):ℂ) * I)‖ ≤ 0.00000014374 := by
  have hl := lg_44
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.709724188187936636 95.70972425141798722 (-1.4619446) 0.00000004373 0.1086368955606 (-0.9940814981292) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_45 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4435285025271):ℝ):ℂ) + (((-0.8962602676911):ℝ):ℂ) * I)‖ ≤ 0.00000014274 := by
  have hl := lg_45
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.278107664972741804 96.27810771555681768 (-2.0303281) 0.00000004273 (-0.4435285025271) (-0.8962602676911) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_46 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8497032757659):ℝ):ℂ) + (((-0.5272611716019):ℝ):ℂ) * I)‖ ≤ 0.00000014058 := by
  have hl := lg_46
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.833998167129444872 96.833998230359520748 (-2.5862186) 0.00000004057 (-0.8497032757659) (-0.5272611716019) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_47 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999345732695):ℝ):ℂ) + (((-0.01143890382):ℝ):ℂ) * I)‖ ≤ 0.00000016513 := by
  have hl := lg_47
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.377933109578041068 97.377933172808142236 (-3.1301535) 0.00000006512 (-0.9999345732695) (-0.01143890382) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_48 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8673000866114):ℝ):ℂ) + ((0.4977856563603:ℝ):ℂ) * I)‖ ≤ 0.00000017988 := by
  have hl := lg_48
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.910415935009683888 97.91041599823970918 2.6205489 0.00000007987 (-0.8673000866114) 0.4977856563603 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_49 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5040222868855):ℝ):ℂ) + ((0.8636906473479:ℝ):ℂ) * I)‖ ≤ 0.00000016137 := by
  have hl := lg_49
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.431918953515786448 98.431919004099887616 2.0990459 0.00000006136 (-0.5040222868855) 0.8636906473479 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_50 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0172819128405):ℝ):ℂ) + ((0.9998506565924:ℝ):ℂ) * I)‖ ≤ 0.00000016879 := by
  have hl := lg_50
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.942885820415948056 98.94288588364599864 1.5880791 0.00000006878 (-0.0172819128405) 0.9998506565924 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_51 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4649386606441:ℝ):ℂ) + ((0.885342895063:ℝ):ℂ) * I)‖ ≤ 0.0000001449 := by
  have hl := lg_51
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.443733869990932616 99.4437339332209832 1.087231 0.00000004489 0.4649386606441 0.885342895063 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_52 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8275264977816:ℝ):ℂ) + ((0.5614266608109:ℝ):ℂ) * I)‖ ≤ 0.00000014586 := by
  have hl := lg_52
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.9348560974887564 99.934856160718806984 0.5961088 0.00000004585 0.8275264977816 0.5614266608109 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_53 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9934700953962:ℝ):ℂ) + ((0.1140928111381:ℝ):ℂ) * I)‖ ≤ 0.0000001702 := by
  have hl := lg_53
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.416623044687549048 100.416623107917624924 0.1143418 0.00000007019 0.9934700953962 0.1140928111381 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_54 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9364523888667:ℝ):ℂ) + (((-0.3507947026194):ℝ):ℂ) * I)‖ ≤ 0.00000013548 := by
  have hl := lg_54
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.889384479405451664 100.88938452998952754 (-0.3584196) 0.00000003547 0.9364523888667 (-0.3507947026194) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_55 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6803868155703:ℝ):ℂ) + (((-0.7328531784731):ℝ):ℂ) * I)‖ ≤ 0.0000001364 := by
  have hl := lg_55
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.353470888026910664 101.35347095125698654 (-0.822506) 0.00000003639 0.6803868155703 (-0.7328531784731) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_56 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2884104476943:ℝ):ℂ) + (((-0.9575068739496):ℝ):ℂ) * I)‖ ≤ 0.00000017757 := by
  have hl := lg_56
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.809194929200693224 101.809194992430743808 (-1.27823) 0.00000007756 0.2884104476943 (-0.9575068739496) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_57 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1544704752266):ℝ):ℂ) + (((-0.9879974049979):ℝ):ℂ) * I)‖ ≤ 0.00000017512 := by
  have hl := lg_57
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.256852639773246964 102.256852690357348132 (-1.7258878) 0.00000007511 (-0.1544704752266) (-0.9879974049979) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_58 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5604784216971):ℝ):ℂ) + (((-0.828169027918):ℝ):ℂ) * I)‖ ≤ 0.00000013824 := by
  have hl := lg_58
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.696724589867334064 102.69672465309740994 (-2.1657597) 0.00000003823 (-0.5604784216971) (-0.828169027918) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_59 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8559140118411):ℝ):ℂ) + (((-0.5171181724291):ℝ):ℂ) * I)‖ ≤ 0.00000014676 := by
  have hl := lg_59
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.129076998390749664 103.129077061620850832 (-2.5981121) 0.00000004675 (-0.8559140118411) (-0.5171181724291) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p292_60 : ‖exp (-((((((25292:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9929995122097):ℝ):ℂ) + (((-0.1181184503254):ℝ):ℂ) * I)‖ ≤ 0.00000018004 := by
  have hl := lg_60
  refine (ecis_approx ((((25292:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.554162634848657916 103.5541626980787085 (-3.0231978) 0.00000008003 (-0.9929995122097) (-0.1181184503254) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_2 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2863757666243:ℝ):ℂ) + ((0.9581173833567:ℝ):ℂ) * I)‖ ≤ 0.00000014249 := by
  have hl := lg_2
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.5692015790641 17.5692015917376 1.2803543 0.00000004248 0.2863757666243 0.9581173833567 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_3 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9098772822544):ℝ):ℂ) + (((-0.414877489277):ℝ):ℂ) * I)‖ ≤ 0.00000015445 := by
  have hl := lg_3
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.846525674281732908 27.846525686955258255 (-2.7137845) 0.00000005444 (-0.9098772822544) (-0.414877489277) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_4 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8359778954417):ℝ):ℂ) + ((0.5487631167155:ℝ):ℂ) * I)‖ ≤ 0.00000014041 := by
  have hl := lg_4
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.1384031581282 35.1384031834752 2.5607087 0.0000000404 (-0.8359778954417) 0.5487631167155 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_5 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9989291905238):ℝ):ℂ) + (((-0.0462652325027):ℝ):ℂ) * I)‖ ≤ 0.00000013557 := by
  have hl := lg_5
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.794422753289455523 40.79442277863648087 (-3.0953109) 0.00000003556 (-0.9989291905238) (-0.0462652325027) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_6 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.136934629313:ℝ):ℂ) + (((-0.99058008626):ℝ):ℂ) * I)‖ ≤ 0.00000012845 := by
  have hl := lg_6
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.415727253345832908 45.415727278692858255 (-1.4334301) 0.00000002844 0.136934629313 (-0.99058008626) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_7 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5877689877583:ℝ):ℂ) + ((0.8090288110009:ℝ):ℂ) * I)‖ ≤ 0.00000012252 := by
  have hl := lg_7
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.322984534927341434 49.322984560274392128 0.9424979 0.00000002251 0.5877689877583 0.8090288110009 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_8 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7651832875684):ℝ):ℂ) + (((-0.6438125009568):ℝ):ℂ) * I)‖ ≤ 0.00000012026 := by
  have hl := lg_8
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.7076047371923 52.7076047752128 (-2.4421223) 0.00000002025 (-0.7651832875684) (-0.6438125009568) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_9 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6557532675908:ℝ):ℂ) + ((0.7549752658492:ℝ):ℂ) * I)‖ ≤ 0.00000011607 := by
  have hl := lg_9
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.693051348563465816 55.69305137391051651 0.8556164 0.00000001606 0.6557532675908 0.7549752658492 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_10 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2417415890597):ℝ):ℂ) + (((-0.9703406639514):ℝ):ℂ) * I)‖ ≤ 0.00000013228 := by
  have hl := lg_10
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.363624332353555523 58.36362437037408087 (-1.8149566) 0.00000003227 (-0.2417415890597) (-0.9703406639514) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_11 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4632024491328):ℝ):ℂ) + ((0.8862524985084:ℝ):ℂ) * I)‖ ≤ 0.00000012609 := by
  have hl := lg_11
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.779451459853755951 60.779451497874306645 2.0524016 0.00000002608 (-0.4632024491328) 0.8862524985084 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_12 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9883067596997:ℝ):ℂ) + (((-0.1524786828772):ℝ):ℂ) * I)‖ ≤ 0.0000001394 := by
  have hl := lg_12
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.984928832409932908 62.984928870430458255 (-0.1530758) 0.00000003939 0.9883067596997 (-0.1524786828772) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_13 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.573786722451):ℝ):ℂ) + (((-0.8190047601381):ℝ):ℂ) * I)‖ ≤ 0.000000128 := by
  have hl := lg_13
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.0137713438110499 65.013771381831600594 (-2.1819183) 0.00000002799 (-0.573786722451) (-0.8190047601381) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_14 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6068217729882):ℝ):ℂ) + ((0.7948379305336:ℝ):ℂ) * I)‖ ≤ 0.000000165 := by
  have hl := lg_14
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.892186113991441434 66.892186152011992128 2.2228522 0.00000006499 (-0.6068217729882) 0.7948379305336 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_15 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8897085769939:ℝ):ℂ) + ((0.4565289125821:ℝ):ℂ) * I)‖ ≤ 0.00000015142 := by
  have hl := lg_15
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.640948427571188431 68.640948465591739125 0.4740899 0.00000005141 0.8897085769939 0.4565289125821 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_16 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.397717998222:ℝ):ℂ) + (((-0.9175077078097):ℝ):ℂ) * I)‖ ≤ 0.00000016273 := by
  have hl := lg_16
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.2768063162564 70.2768063669504 (-1.161768) 0.00000006272 0.397717998222 (-0.9175077078097) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_17 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9033958822311):ℝ):ℂ) + (((-0.4288075090848):ℝ):ℂ) * I)‖ ≤ 0.00000017355 := by
  have hl := lg_17
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.813458605437552598 71.813458656131577945 (-2.6984203) 0.00000007354 (-0.9033958822311) (-0.4288075090848) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_18 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5355630814914):ℝ):ℂ) + ((0.8444952254072:ℝ):ℂ) * I)‖ ≤ 0.00000015854 := by
  have hl := lg_18
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.262252927627565816 73.26225296564811651 2.1359707 0.00000005853 (-0.5355630814914) 0.8444952254072 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_19 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7210159737371:ℝ):ℂ) + ((0.692918440811:ℝ):ℂ) * I)‖ ≤ 0.00000013705 := by
  have hl := lg_19
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.632694785165226241 74.632694823185802282 0.7655289 0.00000003704 0.7210159737371 0.692918440811 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_20 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8604713250185:ℝ):ℂ) + (((-0.5094988702843):ℝ):ℂ) * I)‖ ≤ 0.00000017475 := by
  have hl := lg_20
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.932825911417655523 75.93282596211168087 (-0.5346023) 0.00000007474 0.8604713250185 (-0.5094988702843) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_21 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1991497092845):ℝ):ℂ) + (((-0.9799690777219):ℝ):ℂ) * I)‖ ≤ 0.00000016109 := by
  have hl := lg_21
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.169510209209074342 77.169510247229650383 (-1.7712865) 0.00000006108 (-0.1991497092845) (-0.9799690777219) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_22 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9817838798363):ℝ):ℂ) + (((-0.1900010867269):ℝ):ℂ) * I)‖ ≤ 0.00000014725 := by
  have hl := lg_22
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.348653038917855951 78.348653089611906645 (-2.9504294) 0.00000004724 (-0.9817838798363) (-0.1900010867269) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_23 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.593371336852):ℝ):ℂ) + ((0.8049288518813:ℝ):ℂ) * I)‖ ≤ 0.00000012855 := by
  have hl := lg_23
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.475371864800760002 79.475371915494836043 2.2060371 0.00000002854 (-0.593371336852) 0.8049288518813 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_24 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4291194923002:ℝ):ℂ) + ((0.9032477297663:ℝ):ℂ) * I)‖ ≤ 0.00000016885 := by
  have hl := lg_24
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.554130411474032908 80.554130462168058255 1.1272786 0.00000006884 0.4291194923002 0.9032477297663 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_25 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9957190571375:ℝ):ℂ) + ((0.092431375913:ℝ):ℂ) * I)‖ ≤ 0.00000016395 := by
  have hl := lg_25
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.588845506578911046 81.58884555727296174 0.0925635 0.00000006394 0.9957190571375 0.092431375913 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_26 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6203840852248:ℝ):ℂ) + (((-0.7842981491753):ℝ):ℂ) * I)‖ ≤ 0.00000017047 := by
  have hl := lg_26
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.5829729228751499 82.582972973569200594 (-0.901564) 0.00000007046 0.6203840852248 (-0.7842981491753) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_27 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2834326622577):ℝ):ℂ) + (((-0.9589921407207):ℝ):ℂ) * I)‖ ≤ 0.00000016755 := by
  have hl := lg_27
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.539577022845198724 83.539577060865774765 (-1.858168) 0.00000006754 (-0.2834326622577) (-0.9589921407207) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_28 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9353270506711):ℝ):ℂ) + (((-0.3537842677583):ℝ):ℂ) * I)‖ ≤ 0.00000015043 := by
  have hl := lg_28
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.461387693055541434 84.461387743749592128 (-2.7799787) 0.00000005042 (-0.9353270506711) (-0.3537842677583) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_29 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8638941109894):ℝ):ℂ) + ((0.5036734705289:ℝ):ℂ) * I)‖ ≤ 0.00000012651 := by
  have hl := lg_29
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.350847376311802124 85.350847427005878165 2.6137469 0.0000000265 (-0.8638941109894) 0.5036734705289 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_30 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1826174096595):ℝ):ℂ) + ((0.9831840528042:ℝ):ℂ) * I)‖ ≤ 0.00000015683 := by
  have hl := lg_30
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.210150006635288431 86.210150057329339125 1.7544443 0.00000005682 (-0.1826174096595) 0.9831840528042 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_31 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6031749467591:ℝ):ℂ) + ((0.797608916451:ℝ):ℂ) * I)‖ ≤ 0.0000001548 := by
  have hl := lg_31
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.041273645729615961 87.041273696423692002 0.9233206 0.00000005479 0.6031749467591 0.797608916451 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_32 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9929768690265:ℝ):ℂ) + ((0.1183086538603:ℝ):ℂ) * I)‖ ≤ 0.00000015819 := by
  have hl := lg_32
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.8460078953205 87.846007958688 0.1185864 0.00000005818 0.9929768690265 0.1183086538603 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_33 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7891435970777:ℝ):ℂ) + (((-0.6142087456161):ℝ):ℂ) * I)‖ ≤ 0.00000016639 := by
  have hl := lg_33
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.625977134135488859 88.6259771848295649 (-0.6613829) 0.00000006638 0.7891435970777 (-0.6142087456161) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_34 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1521373391167:ℝ):ℂ) + (((-0.9883593628061):ℝ):ℂ) * I)‖ ≤ 0.00000014737 := by
  have hl := lg_34
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.382660184501652598 89.382660247869177945 (-1.4180659) 0.00000004736 0.1521373391167 (-0.9883593628061) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_35 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5497096930629):ℝ):ℂ) + (((-0.8353557645363):ℝ):ℂ) * I)‖ ≤ 0.00000013841 := by
  have hl := lg_35
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.117407288216796957 90.117407338910872998 (-2.152813) 0.0000000384 (-0.5497096930629) (-0.8353557645363) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_36 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.962497814499):ℝ):ℂ) + (((-0.2712894337103):ℝ):ℂ) * I)‖ ≤ 0.00000015689 := by
  have hl := lg_36
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.831454506691665816 90.83145455738571651 (-2.8668602) 0.00000005688 (-0.962497814499) (-0.2712894337103) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_37 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9131911152822):ℝ):ℂ) + ((0.4075315777172:ℝ):ℂ) * I)‖ ≤ 0.00000014845 := by
  have hl := lg_37
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.525936305437791374 91.525936356131867415 2.7218433 0.00000004844 (-0.9131911152822) 0.4075315777172 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
