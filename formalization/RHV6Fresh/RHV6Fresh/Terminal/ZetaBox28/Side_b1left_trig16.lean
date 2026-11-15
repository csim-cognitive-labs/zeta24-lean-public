/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 16

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

lemma cs_b1left_v26p406_17 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8340476138249:ℝ):ℂ) + ((0.5516924667539:ℝ):ℂ) * I)‖ ≤ 0.00000015048 := by
  have hl := lg_17
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.813831535691956204 74.81383158850398261 0.5843921 0.00000005047 0.8340476138249 0.5516924667539 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_18 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6018880986224:ℝ):ℂ) + (((-0.7985804384887):ℝ):ℂ) * I)‖ ≤ 0.00000016776 := by
  have hl := lg_18
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.323156618413757168 76.32315665802280998 (-0.924933) 0.00000006775 0.6018880986224 (-0.7985804384887) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_19 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7045832384784):ℝ):ℂ) + (((-0.7096213497569):ℝ):ℂ) * I)‖ ≤ 0.00000012289 := by
  have hl := lg_19
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.750855663276638818 77.750855702885718036 (-2.352632) 0.00000002288 (-0.7045832384784) (-0.7096213497569) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_20 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8443261165592):ℝ):ℂ) + ((0.5358296453405:ℝ):ℂ) * I)‖ ≤ 0.0000001475 := by
  have hl := lg_20
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.105306388010202854 79.10530644082222926 2.5761026 0.00000004749 (-0.8443261165592) 0.5358296453405 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_2 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9276490488225:ℝ):ℂ) + ((0.3734531325598:ℝ):ℂ) * I)‖ ≤ 0.000000144 := by
  have hl := lg_2
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.4668271775526 18.4668271908736 0.3827287 0.00000004399 0.9276490488225 0.3734531325598 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_3 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5445911628508):ℝ):ℂ) + ((0.8387016545449:ℝ):ℂ) * I)‖ ≤ 0.00000014814 := by
  have hl := lg_3
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.269228587770305288 29.26922860109133193 2.1466979 0.00000004813 (-0.5445911628508) 0.8387016545449 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_4 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7210654462759:ℝ):ℂ) + ((0.6928669585043:ℝ):ℂ) * I)‖ ≤ 0.00000013868 := by
  have hl := lg_4
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.9336543551052 36.9336543817472 0.7654575 0.00000003867 0.7210654462759 0.6928669585043 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_5 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.450338146698:ℝ):ℂ) + ((0.8928580814601:ℝ):ℂ) * I)‖ ≤ 0.00000012562 := by
  have hl := lg_5
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.878644849218356178 42.87864487586038282 1.1036523 0.00000002561 0.450338146698 0.8928580814601 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_6 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8184052918423):ℝ):ℂ) + ((0.5746414344855:ℝ):ℂ) * I)‖ ≤ 0.00000013454 := by
  have hl := lg_6
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.736055765322905288 47.73605579196493193 2.5294267 0.00000003453 (-0.8184052918423) 0.5746414344855 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_7 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0066593239844):ℝ):ℂ) + (((-0.9999778264561):ℝ):ℂ) * I)‖ ≤ 0.0000001465 := by
  have hl := lg_7
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.842938177280712924 51.842938203922766208 (-1.5774557) 0.00000004649 (-0.0066593239844) (-0.9999778264561) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_8 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.410142339276:ℝ):ℂ) + ((0.9120215247094:ℝ):ℂ) * I)‖ ≤ 0.00000013197 := by
  have hl := lg_8
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.4004815326578 55.4004815726208 1.1481862 0.00000003196 0.410142339276 0.9120215247094 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_9 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4068408327804):ℝ):ℂ) + (((-0.913499062276):ℝ):ℂ) * I)‖ ≤ 0.00000013758 := by
  have hl := lg_9
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.538457175540610576 58.53845720218266386 (-1.9897894) 0.00000003757 (-0.4068408327804) (-0.913499062276) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_10 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0843151059802:ℝ):ℂ) + ((0.9964391415954:ℝ):ℂ) * I)‖ ≤ 0.00000014504 := by
  have hl := lg_10
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.345472026770956178 61.34547206673398282 1.486381 0.00000004503 0.0843151059802 0.9964391415954 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_11 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4950770646564:ℝ):ℂ) + (((-0.8688490663235):ℝ):ℂ) * I)‖ ≤ 0.00000013469 := by
  have hl := lg_11
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.884725837117756186 63.88472587708080947 (-1.0528728) 0.00000003468 0.4950770646564 (-0.8688490663235) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_12 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9737945342448):ℝ):ℂ) + ((0.2274295600522:ℝ):ℂ) * I)‖ ≤ 0.00000013611 := by
  have hl := lg_12
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.202882942875505288 66.20288298283853193 2.9121554 0.0000000361 (-0.9737945342448) 0.2274295600522 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_13 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7111542992078:ℝ):ℂ) + ((0.7030359611843:ℝ):ℂ) * I)‖ ≤ 0.00000012172 := by
  have hl := lg_13
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.3353807607138514 68.335380800676904684 0.7796576 0.00000002171 0.7111542992078 0.7030359611843 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_14 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3672673362204:ℝ):ℂ) + (((-0.9301154249584):ℝ):ℂ) * I)‖ ≤ 0.00000012416 := by
  have hl := lg_14
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.309765354833312924 70.309765394796366208 (-1.194727) 0.00000002415 0.3672673362204 (-0.9301154249584) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_15 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.994091724198):ℝ):ℂ) + (((-0.1085432790205):ℝ):ℂ) * I)‖ ≤ 0.000000142 := by
  have hl := lg_15
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.147873436988661466 72.14787347695171475 (-3.0328351) 0.00000004199 (-0.994091724198) (-0.1085432790205) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_16 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0398708555466:ℝ):ℂ) + ((0.9992048413002:ℝ):ℂ) * I)‖ ≤ 0.00000017596 := by
  have hl := lg_16
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.8673087102104 73.8673087634944 1.5309149 0.00000007595 0.0398708555466 0.9992048413002 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_17 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.996453387288:ℝ):ℂ) + (((-0.0841465802169):ℝ):ℂ) * I)‖ ≤ 0.00000015179 := by
  have hl := lg_17
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.482469884643834628 75.48246993792786127 (-0.0842462) 0.00000005178 0.996453387288 (-0.0841465802169) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_18 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0362564251528):ℝ):ℂ) + (((-0.9993425196772):ℝ):ℂ) * I)‖ ≤ 0.00000013308 := by
  have hl := lg_18
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.005284353093210576 77.00528439305626386 (-1.6070607) 0.00000003307 (-0.0362564251528) (-0.9993425196772) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_19 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9955783923542):ℝ):ℂ) + (((-0.093934361077):ℝ):ℂ) * I)‖ ≤ 0.00000012399 := by
  have hl := lg_19
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.445743262175877126 78.445743302138957052 (-3.0475196) 0.00000002398 (-0.9955783923542) (-0.093934361077) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p642_20 : ‖exp (-((((((26642:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2939085865535):ℝ):ℂ) + ((0.9558335329692:ℝ):ℂ) * I)‖ ≤ 0.00000016429 := by
  have hl := lg_20
  refine (ecis_approx ((((26642:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.812299204323556178 79.81229925760758282 1.8691098 0.00000006428 (-0.2939085865535) 0.9558335329692 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_2 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9663792570353:ℝ):ℂ) + ((0.2571208501307:ℝ):ℂ) * I)‖ ≤ 0.00000012035 := by
  have hl := lg_2
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.5895142284657 18.5895142418752 0.2600417 0.00000002034 0.9663792570353 0.2571208501307 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_3 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3722641119226):ℝ):ℂ) + ((0.9281268399156:ℝ):ℂ) * I)‖ ≤ 0.00000014035 := by
  have hl := lg_3
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.463682962818550316 29.463682976228077135 1.9522436 0.00000004034 (-0.3722641119226) 0.9281268399156 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_4 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8677777368561:ℝ):ℂ) + ((0.4969525122352:ℝ):ℂ) * I)‖ ≤ 0.00000014069 := by
  have hl := lg_4
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.1790284569314 37.1790284837504 0.5200834 0.00000004068 0.8677777368561 0.4969525122352 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_5 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6831113827052:ℝ):ℂ) + ((0.7303142055435:ℝ):ℂ) * I)‖ ≤ 0.0000001362 := by
  have hl := lg_5
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.163515359627171171 43.16351538644619799 0.8187818 0.00000003619 0.6831113827052 0.7303142055435 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_6 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5983890780083):ℝ):ℂ) + ((0.8012056610562:ℝ):ℂ) * I)‖ ≤ 0.00000016068 := by
  have hl := lg_6
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.053197191284250316 48.053197218103277135 2.2122853 0.00000006067 (-0.5983890780083) 0.8012056610562 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_7 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3439172691547):ℝ):ℂ) + (((-0.9389999531283):ℝ):ℂ) * I)‖ ≤ 0.00000014297 := by
  have hl := lg_7
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.187364273571482618 52.187364300390536256 (-1.9218818) 0.00000004296 (-0.3439172691547) (-0.9389999531283) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_8 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7108255521943:ℝ):ℂ) + ((0.7033683489806:ℝ):ℂ) * I)‖ ≤ 0.00000016102 := by
  have hl := lg_8
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.7685426853971 55.7685427256256 0.7801251 0.00000006101 0.7108255521943 0.7033683489806 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_9 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7228389260854):ℝ):ℂ) + (((-0.6910165605164):ℝ):ℂ) * I)‖ ≤ 0.00000013899 := by
  have hl := lg_9
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.927365925637100632 58.92736595245615427 (-2.3786982) 0.00000003898 (-0.7228389260854) (-0.6910165605164) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_10 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4723656610991:ℝ):ℂ) + ((0.8814026788105:ℝ):ℂ) * I)‖ ≤ 0.00000015654 := by
  have hl := lg_10
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.753029588092871171 61.75302962832139799 1.0788235 0.00000005653 0.4723656610991 0.8814026788105 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_11 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0933599698532:ℝ):ℂ) + (((-0.9956324201375):ℝ):ℂ) * I)‖ ≤ 0.00000016871 := by
  have hl := lg_11
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.309153300265036527 64.309153340493590165 (-1.4773002) 0.0000000687 0.0933599698532 (-0.9956324201375) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_12 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7842774112771):ℝ):ℂ) + ((0.620410301427:ℝ):ℂ) * I)‖ ≤ 0.00000015924 := by
  have hl := lg_12
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.642711419749950316 66.642711459978477135 2.4723269 0.00000005923 (-0.7842774112771) 0.620410301427 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_13 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9474392643373:ℝ):ℂ) + ((0.3199356816488:ℝ):ℂ) * I)‖ ≤ 0.00000015811 := by
  have hl := lg_13
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.7893767968465123 68.789376837075065938 0.3256616 0.0000000581 0.9474392643373 0.3199356816488 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_14 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0909180488259):ℝ):ℂ) + (((-0.9958583776809):ℝ):ℂ) * I)‖ ≤ 0.00000016331 := by
  have hl := lg_14
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.776878502037182618 70.776878542265736256 (-1.6618401) 0.0000000633 (-0.0909180488259) (-0.9958583776809) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_15 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9321220316959):ℝ):ℂ) + ((0.3621443329165:ℝ):ℂ) * I)‖ ≤ 0.00000016372 := by
  have hl := lg_15
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.627198322445721487 72.627198362674275125 2.7710253 0.00000006371 (-0.9321220316959) 0.3621443329165 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_16 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5060764874151:ℝ):ℂ) + ((0.8624886021772:ℝ):ℂ) * I)‖ ≤ 0.00000017231 := by
  have hl := lg_16
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.3580569138628 74.3580569675008 1.0401667 0.0000000723 0.5060764874151 0.8624886021772 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_17 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.83331152226:ℝ):ℂ) + (((-0.5528036784147):ℝ):ℂ) * I)‖ ≤ 0.00000013981 := by
  have hl := lg_17
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.983948646357743446 75.983948699995770265 (-0.585725) 0.0000000398 0.83331152226 (-0.5528036784147) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_18 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5208617788519):ℝ):ℂ) + (((-0.8536410295458):ℝ):ℂ) * I)‖ ≤ 0.00000013207 := by
  have hl := lg_18
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.516880154102800632 77.51688019433135427 (-2.1186565) 0.00000003206 (-0.5208617788519) (-0.8536410295458) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_19 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9101738941711):ℝ):ℂ) + ((0.4142263659407:ℝ):ℂ) * I)‖ ≤ 0.000000132 := by
  have hl := lg_19
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.966908961350305857 78.966909001578886314 2.7145 0.00000003199 (-0.9101738941711) 0.4142263659407 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p819_20 : ‖exp (-((((((26819:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2298574678611:ℝ):ℂ) + ((0.9732243032664:ℝ):ℂ) * I)‖ ≤ 0.00000017679 := by
  have hl := lg_20
  refine (ecis_approx ((((26819:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.342543816558571171 80.34254387019659799 1.3388651 0.00000007678 0.2298574678611 0.9732243032664 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_2 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9953514366542:ℝ):ℂ) + ((0.0963094883715:ℝ):ℂ) * I)‖ ≤ 0.00000015502 := by
  have hl := lg_2
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.7530969630165 18.753096976544 0.096459 0.00000005501 0.9953514366542 0.0963094883715 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_3 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1218710561084):ℝ):ℂ) + ((0.992545941346:ℝ):ℂ) * I)‖ ≤ 0.00000014053 := by
  have hl := lg_3
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.72295546288287702 29.722955476410404075 1.6929711 0.00000004052 (-0.1218710561084) 0.992545941346 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_4 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9814489840716:ℝ):ℂ) + ((0.1917234770831:ℝ):ℂ) * I)‖ ≤ 0.00000011706 := by
  have hl := lg_4
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.506193926033 37.506193953088 0.1929179 0.00000001705 0.9814489840716 0.1917234770831 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_5 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9051965308704:ℝ):ℂ) + ((0.4249932240639:ℝ):ℂ) * I)‖ ≤ 0.00000014343 := by
  have hl := lg_5
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.543342706838924495 43.54334273389395155 0.4389544 0.00000004342 0.9051965308704 0.4249932240639 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_6 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2168960249609):ℝ):ℂ) + ((0.9761947112924:ℝ):ℂ) * I)‖ ≤ 0.00000013155 := by
  have hl := lg_6
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.47605242589937702 48.476052452954404075 1.78943 0.00000003154 (-0.2168960249609) 0.9761947112924 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_7 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7245079650883):ℝ):ℂ) + (((-0.6892664278024):ℝ):ℂ) * I)‖ ≤ 0.00000013826 := by
  have hl := lg_7
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.64659906862584221 52.64659909568089632 (-2.3811166) 0.00000003825 (-0.7245079650883) (-0.6892664278024) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_8 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9584218663118:ℝ):ℂ) + ((0.2853550878737:ℝ):ℂ) * I)‖ ≤ 0.00000016503 := by
  have hl := lg_8
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.2592908890495 56.259290929632 0.2893769 0.00000006502 0.9584218663118 0.2853550878737 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_9 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9702949137154):ℝ):ℂ) + (((-0.2419251540151):ℝ):ℂ) * I)‖ ≤ 0.00000013887 := by
  have hl := lg_9
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.44591092576575404 59.44591095282080815 (-2.8972432) 0.00000003886 (-0.9702949137154) (-0.2419251540151) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_10 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8600577874853:ℝ):ℂ) + ((0.5101966309041:ℝ):ℂ) * I)‖ ≤ 0.00000013866 := by
  have hl := lg_10
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.296439669855424495 62.29643971043795155 0.5354134 0.00000003865 0.8600577874853 0.5101966309041 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_11 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.45503113048):ℝ):ℂ) + (((-0.8904755304271):ℝ):ℂ) * I)‖ ≤ 0.00000015326 := by
  have hl := lg_11
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.875056584461410315 64.875056625043964425 (-2.0432035) 0.00000005325 (-0.45503113048) (-0.8904755304271) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_12 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.309904583245):ℝ):ℂ) + ((0.9507676631448:ℝ):ℂ) * I)‖ ≤ 0.00000015054 := by
  have hl := lg_12
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.22914938891587702 67.229149429498404075 1.885889 0.00000005053 (-0.309904583245) 0.9507676631448 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_13 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9611475494725:ℝ):ℂ) + (((-0.2760351212129):ℝ):ℂ) * I)‖ ≤ 0.00000013397 := by
  have hl := lg_13
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.3947048450233935 69.39470488560594761 (-0.2796665) 0.00000003396 0.9611475494725 (-0.2760351212129) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_14 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6547572224895):ℝ):ℂ) + (((-0.75583925512):ℝ):ℂ) * I)‖ ≤ 0.00000014735 := by
  have hl := lg_14
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.39969603164234221 71.39969607222489632 (-2.2846577) 0.00000004734 (-0.6547572224895) (-0.75583925512) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_15 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5321425568468):ℝ):ℂ) + ((0.8466547697762:ℝ):ℂ) * I)‖ ≤ 0.00000012416 := by
  have hl := lg_15
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.266298169721801515 73.266298210304355625 2.1319255 0.00000002415 (-0.5321425568468) 0.8466547697762 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_16 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9264842166703:ℝ):ℂ) + ((0.3763336236117:ℝ):ℂ) * I)‖ ≤ 0.0000001341 := by
  have hl := lg_16
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.012387852066 75.012387906176 0.3858358 0.00000003409 0.9264842166703 0.3763336236117 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_17 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3111786693345:ℝ):ℂ) + (((-0.9503514274999):ℝ):ℂ) * I)‖ ≤ 0.00000016328 := by
  have hl := lg_17
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.65258699530962187 76.652587049419648925 (-1.2543633) 0.00000006327 0.3111786693345 (-0.9503514274999) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_18 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9424847485662):ℝ):ℂ) + (((-0.3342491563717):ℝ):ℂ) * I)‖ ≤ 0.00000014322 := by
  have hl := lg_18
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.19900788878225404 78.19900792936480815 (-2.8007842) 0.00000004321 (-0.9424847485662) (-0.3342491563717) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_19 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4338991660667):ℝ):ℂ) + ((0.9009614385103:ℝ):ℂ) * I)‖ ≤ 0.0000001331 := by
  have hl := lg_19
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.661796560249544165 79.66179660083212533 2.0196124 0.00000003309 (-0.4338991660667) 0.9009614385103 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p055_20 : ‖exp (-((((((27055:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8069230369536:ℝ):ℂ) + ((0.5906565943369:ℝ):ℂ) * I)‖ ≤ 0.00000016048 := by
  have hl := lg_20
  refine (ecis_approx ((((27055:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.049536632871924495 81.04953668698195155 0.6318723 0.00000006047 0.8069230369536 0.5906565943369 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_2 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9925815307546:ℝ):ℂ) + (((-0.1215808570655):ℝ):ℂ) * I)‖ ≤ 0.00000011697 := by
  have hl := lg_2
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.971438324811 18.971438338496 (-0.1218824) 0.00000001696 0.9925815307546 (-0.1215808570655) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_3 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.222022376998:ℝ):ℂ) + ((0.9750415704534:ℝ):ℂ) * I)‖ ≤ 0.00000011153 := by
  have hl := lg_3
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.06901833373144868 30.06901834741647605 1.3469082 0.00000001152 0.222022376998 0.9750415704534 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_4 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9704361903904:ℝ):ℂ) + (((-0.2413578264331):ℝ):ℂ) * I)‖ ≤ 0.00000013393 := by
  have hl := lg_4
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.942876649622 37.942876676992 (-0.2437648) 0.00000003392 0.9704361903904 (-0.2413578264331) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_5 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9976876335519:ℝ):ℂ) + (((-0.0679660640143):ℝ):ℂ) * I)‖ ≤ 0.00000012622 := by
  have hl := lg_5
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.05031564909190033 44.0503156764619277 (-0.0680185) 0.00000002621 0.9976876335519 (-0.0679660640143) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_6 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3389217006327:ℝ):ℂ) + ((0.9408145836669:ℝ):ℂ) * I)‖ ≤ 0.00000012849 := by
  have hl := lg_6
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.04045665854244868 49.04045668591247605 1.2250258 0.00000002848 0.3389217006327 0.9408145836669 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_7 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9891394732097):ℝ):ℂ) + (((-0.1469799378853):ℝ):ℂ) * I)‖ ≤ 0.00000013536 := by
  have hl := lg_7
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.25956076541450014 53.25956079278455488 (-2.9940783) 0.00000003535 (-0.9891394732097) (-0.1469799378853) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_8 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9338925479602:ℝ):ℂ) + (((-0.3575537845756):ℝ):ℂ) * I)‖ ≤ 0.00000015089 := by
  have hl := lg_8
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.914314974433 56.914315015488 (-0.3656472) 0.00000005088 0.9338925479602 (-0.3575537845756) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_9 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9014121281894):ℝ):ℂ) + ((0.4329620942241:ℝ):ℂ) * I)‖ ≤ 0.00000012305 := by
  have hl := lg_9
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.13803666746289736 60.1380366948329521 2.6938164 0.00000002304 (-0.9014121281894) 0.4329620942241 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_10 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9820229462117:ℝ):ℂ) + (((-0.1887615774296):ℝ):ℂ) * I)‖ ≤ 0.00000014318 := by
  have hl := lg_10
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.02175397390290033 63.0217540149579277 (-0.1899009) 0.00000004317 0.9820229462117 (-0.1887615774296) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_11 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9417324220413):ℝ):ℂ) + (((-0.3363629662922):ℝ):ℂ) * I)‖ ≤ 0.00000016442 := by
  have hl := lg_11
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.63039359514724821 65.63039363620230295 (-2.7985405) 0.00000006441 (-0.9417324220413) (-0.3363629662922) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_12 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4507924638419:ℝ):ℂ) + ((0.8926287887713:ℝ):ℂ) * I)‖ ≤ 0.00000014545 := by
  have hl := lg_12
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.01189498335344868 68.01189502440847605 1.1031434 0.00000004544 0.4507924638419 0.8926287887713 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_13 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4645893567018:ℝ):ℂ) + (((-0.8855262444668):ℝ):ℂ) * I)‖ ≤ 0.00000015447 := by
  have hl := lg_13
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.202663892378129 70.20266393343318374 (-1.0876255) 0.00000005446 0.4645893567018 (-0.8855262444668) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_14 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996715191563):ℝ):ℂ) + (((-0.0256291467135):ℝ):ℂ) * I)‖ ≤ 0.00000015232 := by
  have hl := lg_14
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.23099909022550014 72.23099913128055488 (-3.1159607) 0.00000005231 (-0.9996715191563) (-0.0256291467135) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p37_15 : ‖exp (-((((((27370:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2877787176967:ℝ):ℂ) + ((0.9576969299527:ℝ):ℂ) * I)‖ ≤ 0.00000013774 := by
  have hl := lg_15
  refine (ecis_approx ((((27370:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.11933398282334901 74.11933402387840375 1.2788897 0.00000003773 0.2877787176967 0.9576969299527 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_2 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9426800075081:ℝ):ℂ) + (((-0.3336980722816):ℝ):ℂ) * I)‖ ≤ 0.00000013495 := by
  have hl := lg_2
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.1897796866055 19.189779700448 (-0.3402238) 0.00000003494 0.9426800075081 (-0.3336980722816) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_3 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5395908174977:ℝ):ℂ) + ((0.8419274016637:ℝ):ℂ) * I)‖ ≤ 0.00000013133 := by
  have hl := lg_3
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.41508120458002034 30.415081218422548025 1.0008453 0.00000003132 0.5395908174977 0.8419274016637 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_4 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7772912560252:ℝ):ℂ) + (((-0.6291409248386):ℝ):ℂ) * I)‖ ≤ 0.00000015783 := by
  have hl := lg_4
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.379559373211 38.379559400896 (-0.6804475) 0.00000005782 0.7772912560252 (-0.6291409248386) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_5 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8391969249861:ℝ):ℂ) + (((-0.5438276575294):ℝ):ℂ) * I)‖ ≤ 0.00000015893 := by
  have hl := lg_5
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.557288591344876165 44.55728861902990385 (-0.5749915) 0.00000005892 0.8391969249861 (-0.5438276575294) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_6 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7896109654655:ℝ):ℂ) + ((0.6136077926629:ℝ):ℂ) * I)‖ ≤ 0.00000016145 := by
  have hl := lg_6
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.60486089118552034 49.604860918870548025 0.6606216 0.00000006144 0.7896109654655 0.6136077926629 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_7 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8936208725939):ℝ):ℂ) + ((0.4488226107887:ℝ):ℂ) * I)‖ ≤ 0.00000012529 := by
  have hl := lg_7
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.87252246220315807 53.87252248988821344 2.6761453 0.00000002528 (-0.8936208725939) 0.4488226107887 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_8 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5227938132537:ℝ):ℂ) + (((-0.8524591654875):ℝ):ℂ) * I)‖ ≤ 0.00000013674 := by
  have hl := lg_8
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.5693390598165 57.569339101344 (-1.0206713) 0.00000003673 0.5227938132537 (-0.8524591654875) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_9 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4176834993443):ℝ):ℂ) + ((0.9085925898728:ℝ):ℂ) * I)‖ ≤ 0.00000016265 := by
  have hl := lg_9
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.83016240916004068 60.83016243684509605 2.0016906 0.00000006264 (-0.4176834993443) 0.9085925898728 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_10 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6096200018451:ℝ):ℂ) + (((-0.7926937954535):ℝ):ℂ) * I)‖ ≤ 0.0000001477 := by
  have hl := lg_10
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.747068277950376165 63.74706831947790385 (-0.9152152) 0.00000004769 0.6096200018451 (-0.7926937954535) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_11 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.916207665673):ℝ):ℂ) + ((0.4007037724114:ℝ):ℂ) * I)‖ ≤ 0.0000001684 := by
  have hl := lg_11
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.385730605833086105 66.385730647360641475 2.7293078 0.00000006839 (-0.916207665673) 0.4007037724114 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_12 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9491102084021:ℝ):ℂ) + ((0.3149441415662:ℝ):ℂ) * I)‖ ≤ 0.00000014036 := by
  have hl := lg_12
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.79464057779102034 68.794640619318548025 0.3203978 0.00000004035 0.9491102084021 0.3149441415662 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_13 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3191081356506):ℝ):ℂ) + (((-0.9477183113983):ℝ):ℂ) * I)‖ ≤ 0.00000013926 := by
  have hl := lg_13
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.0106229397328645 71.01062298126041987 (-1.8955846) 0.00000003925 (-0.3191081356506) (-0.9477183113983) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_14 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6926272908766):ℝ):ℂ) + ((0.7212956646968:ℝ):ℂ) * I)‖ ≤ 0.00000013736 := by
  have hl := lg_14
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.06230214880865807 73.06230219033621344 2.3359215 0.00000003735 (-0.6926272908766) 0.7212956646968 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v27p685_15 : ‖exp (-((((((27685:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9106863201415:ℝ):ℂ) + ((0.4130985673021:ℝ):ℂ) * I)‖ ≤ 0.00000015131 := by
  have hl := lg_15
  refine (ecis_approx ((((27685:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.972369795924896505 74.972369837452451875 0.4258539 0.0000000513 0.9106863201415 0.4130985673021 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_2 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8480164376045:ℝ):ℂ) + (((-0.5299699251396):ℝ):ℂ) * I)‖ ≤ 0.00000014088 := by
  have hl := lg_2
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.4081210484 19.4081210624 (-0.5585651) 0.00000004087 0.8480164376045 (-0.5299699251396) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_3 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.793180401478:ℝ):ℂ) + ((0.6089867409979:ℝ):ℂ) * I)‖ ≤ 0.00000015355 := by
  have hl := lg_3
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.761144075428592 30.76114408942862 0.6547825 0.00000005354 0.793180401478 0.6089867409979 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_4 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4382636670103:ℝ):ℂ) + (((-0.8988464597353):ℝ):ℂ) * I)‖ ≤ 0.00000014629 := by
  have hl := lg_4
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.8162420968 38.8162421248 (-1.1171303) 0.00000004628 0.4382636670103 (-0.8988464597353) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_5 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4695949379756:ℝ):ℂ) + (((-0.8828819820495):ℝ):ℂ) * I)‖ ≤ 0.00000011667 := by
  have hl := lg_5
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.064261533597852 45.06426156159788 (-1.0819644) 0.00000001666 0.4695949379756 (-0.8828819820495) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_6 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9953746855837:ℝ):ℂ) + ((0.0960689091184:ℝ):ℂ) * I)‖ ≤ 0.00000013362 := by
  have hl := lg_6
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.169265123828592 50.16926515182862 0.0962173 0.00000003361 0.9953746855837 0.0960689091184 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_7 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4727309146966):ℝ):ℂ) + ((0.8812068328632:ℝ):ℂ) * I)‖ ≤ 0.00000012239 := by
  have hl := lg_7
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.485484158991816 54.485484186991872 2.0631836 0.00000002238 (-0.4727309146966) 0.8812068328632 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_8 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1047067973484):ℝ):ℂ) + (((-0.9945031355348):ℝ):ℂ) * I)‖ ≤ 0.0000001226 := by
  have hl := lg_8
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.2243631452 58.2243631872 (-1.6756954) 0.00000002259 (-0.1047067973484) (-0.9945031355348) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_9 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2582703951848:ℝ):ℂ) + ((0.9660726696119:ℝ):ℂ) * I)‖ ≤ 0.00000012095 := by
  have hl := lg_9
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.522288150857184 61.52228817885724 1.3095649 0.00000002094 0.2582703951848 0.9660726696119 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_10 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0696766715148):ℝ):ℂ) + (((-0.9975696273676):ℝ):ℂ) * I)‖ ≤ 0.00000015222 := by
  have hl := lg_10
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.472382581997852 64.47238262399788 (-1.6405295) 0.00000005221 (-0.0696766715148) (-0.9975696273676) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_11 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3923401667244):ℝ):ℂ) + ((0.9198201963273:ℝ):ℂ) * I)‖ ≤ 0.00000016247 := by
  have hl := lg_11
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.141067616518924 67.14106765851898 1.9739707 0.00000006246 (-0.3923401667244) 0.9198201963273 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_12 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8950077275241:ℝ):ℂ) + (((-0.4460506335295):ℝ):ℂ) * I)‖ ≤ 0.00000013527 := by
  have hl := lg_12
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.577386172228592 69.57738621422862 (-0.4623478) 0.00000003526 0.8950077275241 (-0.4460506335295) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_13 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9055809258975):ℝ):ℂ) + (((-0.4241735335066):ℝ):ℂ) * I)‖ ≤ 0.00000015013 := by
  have hl := lg_13
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.8185819870876 71.818582029087656 (-2.7035436) 0.00000005012 (-0.9055809258975) (-0.4241735335066) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_14 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.06612953302:ℝ):ℂ) + ((0.9978110466729:ℝ):ℂ) * I)‖ ≤ 0.00000016325 := by
  have hl := lg_14
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.893605207391816 73.893605249391872 1.5046185 0.00000006324 0.06612953302 0.9978110466729 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v28_15 : ‖exp (-((((((28000:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9101369223696:ℝ):ℂ) + (((-0.4143075941128):ℝ):ℂ) * I)‖ ≤ 0.00000016489 := by
  have hl := lg_15
  refine (ecis_approx ((((28000:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.825405609026444 75.8254056510265 (-0.4271819) 0.00000006488 0.9101369223696 (-0.4143075941128) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
