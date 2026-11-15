/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 1

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

lemma cs_b1left_v13p445_17 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9235951284024:ℝ):ℂ) + (((-0.38336932427):ℝ):ℂ) * I)‖ ≤ 0.00000014624 := by
  have hl := lg_17
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.09255339685595513 38.092553423745968575 (-0.3934416) 0.00000004623 0.9235951284024 (-0.38336932427) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_18 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3975634842854:ℝ):ℂ) + (((-0.9175746705107):ℝ):ℂ) * I)‖ ≤ 0.00000015153 := by
  have hl := lg_18
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.86104827442902996 38.86104829459655685 (-1.1619364) 0.00000005152 0.3975634842854 (-0.9175746705107) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_19 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3127376304581):ℝ):ℂ) + (((-0.9498395519737):ℝ):ℂ) * I)‖ ≤ 0.00000014151 := by
  have hl := lg_19
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.587982064407877335 39.58798208457541767 (-1.8888702) 0.0000000415 (-0.3127376304581) (-0.9498395519737) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_20 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8456128776103):ℝ):ℂ) + (((-0.5337966477493):ℝ):ℂ) * I)‖ ≤ 0.00000013914 := by
  have hl := lg_20
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.277620403953540005 40.27762043084355345 (-2.5785086) 0.00000003913 (-0.8456128776103) (-0.5337966477493) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_2 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993232300593):ℝ):ℂ) + (((-0.0367842529146):ℝ):ℂ) * I)‖ ≤ 0.00000010959 := by
  have hl := lg_2
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.3879854099832 9.3879854167552 (-3.1048001) 0.00000000958 (-0.9993232300593) (-0.0367842529146) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_3 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.676086198833):ℝ):ℂ) + (((-0.7368225374726):ℝ):ℂ) * I)‖ ≤ 0.00000012663 := by
  have hl := lg_3
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.879604834200173216 14.87960484097218676 (-2.3132342) 0.00000002662 (-0.676086198833) (-0.7368225374726) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_4 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9972938379627:ℝ):ℂ) + ((0.0735187102823:ℝ):ℂ) * I)‖ ≤ 0.00000011199 := by
  have hl := lg_4
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.7759708199664 18.7759708335104 0.0735851 0.00000001198 0.9972938379627 0.0735187102823 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_5 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9814483026209):ℝ):ℂ) + (((-0.1917269645844):ℝ):ℂ) * I)‖ ≤ 0.00000014259 := by
  have hl := lg_5
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.798227078966046696 21.79822709251006024 (-2.9486712) 0.00000004258 (-0.9814483026209) (-0.1917269645844) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_6 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6485251829074:ℝ):ℂ) + ((0.7611931996116:ℝ):ℂ) * I)‖ ≤ 0.00000012902 := by
  have hl := lg_6
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.267590244183373216 24.26759025772738676 0.865151 0.00000002901 0.6485251829074 0.7611931996116 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_7 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3411410771603:ℝ):ℂ) + (((-0.9400121092166):ℝ):ℂ) * I)‖ ≤ 0.0000001366 := by
  have hl := lg_7
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.355407051763755568 26.355407065307782656 (-1.2226658) 0.00000003659 0.3411410771603 (-0.9400121092166) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_8 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9939145687019):ℝ):ℂ) + (((-0.1101536638717):ℝ):ℂ) * I)‖ ≤ 0.00000012156 := by
  have hl := lg_8
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.1639562299496 28.1639562502656 (-3.031215) 0.00000002155 (-0.9939145687019) (-0.1101536638717) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_9 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0858148963356):ℝ):ℂ) + ((0.9963110977835:ℝ):ℂ) * I)‖ ≤ 0.00000014606 := by
  have hl := lg_9
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.759209668400346432 29.75920968194437352 1.6567169 0.00000004605 (-0.0858148963356) 0.9963110977835 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_10 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9737315567552:ℝ):ℂ) + ((0.2276990456262:ℝ):ℂ) * I)‖ ≤ 0.00000014696 := by
  have hl := lg_10
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.186212488949246696 31.18621250926526024 0.229714 0.00000004695 0.9737315567552 0.2276990456262 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_11 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.487853710349:ℝ):ℂ) + (((-0.8729254019094):ℝ):ℂ) * I)‖ ≤ 0.00000014865 := by
  have hl := lg_11
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.477093564219010952 32.47709358453503804 (-1.061167) 0.00000004864 0.487853710349 (-0.8729254019094) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_12 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6200863573662):ℝ):ℂ) + (((-0.7845335616751):ℝ):ℂ) * I)‖ ≤ 0.0000001386 := by
  have hl := lg_12
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.655575654166573216 33.65557567448258676 (-2.2396491) 0.00000003859 (-0.6200863573662) (-0.7845335616751) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_13 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9834556081212):ℝ):ℂ) + ((0.1811492934209:ℝ):ℂ) * I)‖ ≤ 0.0000001562 := by
  have hl := lg_13
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.7396740868969448 34.739674107212971888 2.9594377 0.00000005619 (-0.9834556081212) 0.1811492934209 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_14 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3754878400035):ℝ):ℂ) + ((0.92682732049:ℝ):ℂ) * I)‖ ≤ 0.000000139 := by
  have hl := lg_14
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.743392461746955568 35.743392482062982656 1.9557194 0.00000003899 (-0.3754878400035) 0.92682732049 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_15 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5222749098178:ℝ):ℂ) + ((0.8527771799098:ℝ):ℂ) * I)‖ ≤ 0.00000012993 := by
  have hl := lg_15
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.677831913166219912 36.677831933482247 1.0212799 0.00000002992 0.5222749098178 0.8527771799098 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_16 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9891899984769:ℝ):ℂ) + ((0.146639513479:ℝ):ℂ) * I)‖ ≤ 0.00000012396 := by
  have hl := lg_16
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.5519416399328 37.5519416670208 0.1471702 0.00000002395 0.9891899984769 0.146639513479 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_17 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7813753314366:ℝ):ℂ) + (((-0.6240613683144):ℝ):ℂ) * I)‖ ≤ 0.00000012528 := by
  have hl := lg_17
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.373041517814582096 38.37304154490259564 (-0.6739297) 0.00000002527 0.7813753314366 (-0.6240613683144) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_18 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1224053790925:ℝ):ℂ) + (((-0.9924801877968):ℝ):ℂ) * I)‖ ≤ 0.00000015564 := by
  have hl := lg_18
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.147195078383546432 39.14719509869957352 (-1.4480832) 0.00000005563 0.1224053790925 (-0.9924801877968) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_19 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5725177241698):ℝ):ℂ) + (((-0.8198923438485):ℝ):ℂ) * I)‖ ≤ 0.00000011982 := by
  have hl := lg_19
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.879481523268151032 39.879481543584191664 (-2.1803697) 0.00000001981 (-0.5725177241698) (-0.8198923438485) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p544_20 : ‖exp (-((((((13544:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9646968253509):ℝ):ℂ) + (((-0.2633629338159):ℝ):ℂ) * I)‖ ≤ 0.00000014416 := by
  have hl := lg_20
  refine (ecis_approx ((((13544:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.574197898932446696 40.57419792602046024 (-2.8750861) 0.00000004415 (-0.9646968253509) (-0.2633629338159) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_2 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998948713929):ℝ):ℂ) + ((0.014499845162:ℝ):ℂ) * I)‖ ≤ 0.00000011305 := by
  have hl := lg_2
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.4392783013254 9.4392783081344 3.1270923 0.00000001304 (-0.9998948713929) 0.014499845162 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_3 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7336889378788):ℝ):ℂ) + (((-0.679485498303):ℝ):ℂ) * I)‖ ≤ 0.00000013601 := by
  have hl := lg_3
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.960902143542377352 14.96090215035139097 (-2.3945315) 0.000000036 (-0.7336889378788) (-0.679485498303) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_4 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9995795091718:ℝ):ℂ) + (((-0.0289966350433):ℝ):ℂ) * I)‖ ≤ 0.0000001189 := by
  have hl := lg_4
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.8785566026508 18.8785566162688 (-0.0290007) 0.00000001889 0.9995795091718 (-0.0289966350433) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_5 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9972763154425):ℝ):ℂ) + (((-0.0737560176042):ℝ):ℂ) * I)‖ ≤ 0.00000013711 := by
  have hl := lg_5
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.917325484447698162 21.91732549806571178 (-3.0677696) 0.0000000371 (-0.9972763154425) (-0.0737560176042) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_6 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7434642411375:ℝ):ℂ) + ((0.6687756889644:ℝ):ℂ) * I)‖ ≤ 0.00000012978 := by
  have hl := lg_6
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.400180444867777352 24.40018045848579097 0.7325608 0.00000002977 0.7434642411375 0.6687756889644 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_7 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2027183617902:ℝ):ℂ) + (((-0.9792370835467):ℝ):ℂ) * I)‖ ≤ 0.00000012598 := by
  have hl := lg_7
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.499404402755376796 26.499404416373404032 (-1.3666632) 0.00000002597 0.2027183617902 (-0.9792370835467) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_8 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9990539780834):ℝ):ℂ) + ((0.0434873348112:ℝ):ℂ) * I)‖ ≤ 0.00000013194 := by
  have hl := lg_8
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.3178349039762 28.3178349244032 3.0980916 0.00000003193 (-0.9990539780834) 0.0434873348112 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_9 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0765990220101:ℝ):ℂ) + ((0.9970619789296:ℝ):ℂ) * I)‖ ≤ 0.00000014883 := by
  have hl := lg_9
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.921804287084754704 29.92180430070278194 1.4941222 0.00000004882 0.0765990220101 0.9970619789296 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_10 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9982409245988:ℝ):ℂ) + ((0.0592879115516:ℝ):ℂ) * I)‖ ≤ 0.00000015014 := by
  have hl := lg_10
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.356603785773098162 31.35660380620011178 0.0593227 0.00000005013 0.9982409245988 0.0592879115516 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_11 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3261093810739:ℝ):ℂ) + (((-0.9453320430281):ℝ):ℂ) * I)‖ ≤ 0.00000012156 := by
  have hl := lg_11
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.654537814348382394 32.65453783477540963 (-1.2386113) 0.00000002155 0.3261093810739 (-0.9453320430281) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_12 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7530832214205):ℝ):ℂ) + (((-0.6579252705135):ℝ):ℂ) * I)‖ ≤ 0.00000013074 := by
  have hl := lg_12
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.839458746193177352 33.83945876662019097 (-2.4235322) 0.00000003073 (-0.7530832214205) (-0.6579252705135) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_13 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9316163696819):ℝ):ℂ) + ((0.3634431724192:ℝ):ℂ) * I)‖ ≤ 0.00000011666 := by
  have hl := lg_13
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.9294803392913906 34.929480359718417836 2.7696315 0.00000001665 (-0.9316163696819) 0.3634431724192 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_14 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1884982639825):ℝ):ℂ) + ((0.9820735229476:ℝ):ℂ) * I)‖ ≤ 0.00000013901 := by
  have hl := lg_14
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.938682704080776796 35.938682724507804032 1.7604291 0.000000039 (-0.1884982639825) 0.9820735229476 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_15 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6815744615457:ℝ):ℂ) + ((0.7317487638314:ℝ):ℂ) * I)‖ ≤ 0.0000001151 := by
  have hl := lg_15
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.878227627990075514 36.87822764841710275 0.8208842 0.00000001509 0.6815744615457 0.7317487638314 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_16 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9983183903123:ℝ):ℂ) + (((-0.0579688844483):ℝ):ℂ) * I)‖ ≤ 0.00000013779 := by
  have hl := lg_16
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.7571132053016 37.7571132325376 (-0.0580014) 0.00000003778 0.9983183903123 (-0.0579688844483) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_17 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6343820242886:ℝ):ℂ) + (((-0.7730196939661):ℝ):ℂ) * I)‖ ≤ 0.00000013789 := by
  have hl := lg_17
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.582699305197798212 38.58269933243381183 (-0.8835875) 0.00000003788 0.6343820242886 (-0.7730196939661) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_18 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.091048206739):ℝ):ℂ) + (((-0.9958464861861):ℝ):ℂ) * I)‖ ≤ 0.00000015468 := by
  have hl := lg_18
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.361082588410154704 39.36108260883718194 (-1.6619708) 0.00000005467 (-0.091048206739) (-0.9958464861861) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_19 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7362160757864):ℝ):ℂ) + (((-0.6767465476256):ℝ):ℂ) * I)‖ ≤ 0.00000013542 := by
  have hl := lg_19
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.097370007668759654 40.097370028095800508 (-2.3982582) 0.00000003541 (-0.7362160757864) (-0.6767465476256) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_20 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.998995646195):ℝ):ℂ) + (((-0.044807346489):ℝ):ℂ) * I)‖ ≤ 0.00000015599 := by
  have hl := lg_20
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.795882087098498162 40.79588211433451178 (-3.0967703) 0.00000005598 (-0.998995646195) (-0.044807346489) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_21 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8141096130574):ℝ):ℂ) + ((0.5807112344982:ℝ):ℂ) * I)‖ ≤ 0.00000011648 := by
  have hl := lg_21
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.460306546297754148 41.460306566724795002 2.5219906 0.00000001647 (-0.8141096130574) 0.5807112344982 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_22 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3123679292276):ℝ):ℂ) + ((0.9499611975171:ℝ):ℂ) * I)‖ ≤ 0.0000001346 := by
  have hl := lg_22
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.093816115673782394 42.09381614290980963 1.888481 0.00000003459 (-0.3123679292276) 0.9499611975171 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_23 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2837086039504:ℝ):ℂ) + ((0.9589105422533:ℝ):ℂ) * I)‖ ≤ 0.00000013191 := by
  have hl := lg_23
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.699160218363386188 42.699160245599427042 1.2831369 0.0000000319 0.2837086039504 0.9589105422533 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_24 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7625438658217:ℝ):ℂ) + ((0.6469365136531:ℝ):ℂ) * I)‖ ≤ 0.00000012451 := by
  have hl := lg_24
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.278737047518577352 43.27873707475459097 0.7035601 0.0000000245 0.7625438658217 0.6469365136531 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_25 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9891200860077:ℝ):ℂ) + ((0.147110351288:ℝ):ℂ) * I)‖ ≤ 0.00000014589 := by
  have hl := lg_25
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.834650968895396324 43.83465099613142356 0.1476462 0.00000004588 0.9891200860077 0.147110351288 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_26 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9262485633779:ℝ):ℂ) + (((-0.3769132510809):ℝ):ℂ) * I)‖ ≤ 0.00000011761 := by
  have hl := lg_26
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.3687586406167906 44.368758667852817836 (-0.3864615) 0.0000000176 0.9262485633779 (-0.3769132510809) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_27 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6212893005074:ℝ):ℂ) + (((-0.7835812689664):ℝ):ℂ) * I)‖ ≤ 0.00000011964 := by
  have hl := lg_27
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.882706430627132056 44.88270645105417291 (-0.9004093) 0.00000001963 0.6212893005074 (-0.7835812689664) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_28 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1742385402459:ℝ):ℂ) + (((-0.9847034736878):ℝ):ℂ) * I)‖ ≤ 0.00000014487 := by
  have hl := lg_28
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.377961005406176796 45.377961032642204032 (-1.3956639) 0.00000004486 0.1742385402459 (-0.9847034736878) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_29 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2981378358945):ℝ):ℂ) + (((-0.9545228288556):ℝ):ℂ) * I)‖ ≤ 0.00000015168 := by
  have hl := lg_29
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.855834598596051656 45.85583462583209251 (-1.8735375) 0.00000005167 (-0.2981378358945) (-0.9545228288556) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p618_30 : ‖exp (-((((((13618:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6921130475929):ℝ):ℂ) + (((-0.7217891169374):ℝ):ℂ) * I)‖ ≤ 0.00000012096 := by
  have hl := lg_30
  refine (ecis_approx ((((13618:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.317505929315475514 46.31750595655150275 (-2.3352088) 0.00000002095 (-0.6921130475929) (-0.7217891169374) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_2 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.997836404278):ℝ):ℂ) + ((0.0657457964975:ℝ):ℂ) * I)‖ ≤ 0.00000012171 := by
  have hl := lg_2
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.4905711926676 9.4905711995136 3.0757994 0.0000000217 (-0.997836404278) 0.0657457964975 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_3 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7864452127599):ℝ):ℂ) + (((-0.6176600418375):ℝ):ℂ) * I)‖ ≤ 0.00000014539 := by
  have hl := lg_3
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.042199452884581488 15.04219945973059518 (-2.4758288) 0.00000004538 (-0.7864452127599) (-0.6176600418375) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_4 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9913549813622:ℝ):ℂ) + (((-0.1312070917608):ℝ):ℂ) * I)‖ ≤ 0.00000013622 := by
  have hl := lg_4
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.9811423853352 18.9811423990272 (-0.1315865) 0.00000003621 0.9913549813622 (-0.1312070917608) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_5 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9989752459668):ℝ):ℂ) + ((0.0452598869043:ℝ):ℂ) * I)‖ ≤ 0.0000001388 := by
  have hl := lg_5
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.036423889929349628 22.03642390362136332 3.0963173 0.00000003879 (-0.9989752459668) 0.0452598869043 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_6 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8253522150417:ℝ):ℂ) + ((0.5646182082839:ℝ):ℂ) * I)‖ ≤ 0.00000013054 := by
  have hl := lg_6
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.532770645552181488 24.53277065924419518 0.5999706 0.00000003053 0.8253522150417 0.5646182082839 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_7 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0600995883059:ℝ):ℂ) + (((-0.9981923860085):ℝ):ℂ) * I)‖ ≤ 0.00000013874 := by
  have hl := lg_7
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.643401753746998024 26.643401767439025408 (-1.5106605) 0.00000003873 0.0600995883059 (-0.9981923860085) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_8 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9805837752962):ℝ):ℂ) + ((0.1961006356384:ℝ):ℂ) * I)‖ ≤ 0.00000015791 := by
  have hl := lg_8
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.4717135780028 28.4717135985408 2.9442129 0.0000000579 (-0.9805837752962) 0.1961006356384 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_9 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2369922494993:ℝ):ℂ) + ((0.9715115406814:ℝ):ℂ) * I)‖ ≤ 0.00000013014 := by
  have hl := lg_9
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.084398905769162976 30.08439891946119036 1.3315276 0.00000003013 0.2369922494993 0.9715115406814 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_10 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9938382213846:ℝ):ℂ) + (((-0.1108403794431):ℝ):ℂ) * I)‖ ≤ 0.00000015332 := by
  have hl := lg_10
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.526995082596949628 31.52699510313496332 (-0.1110686) 0.00000005331 0.9938382213846 (-0.1108403794431) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_11 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.154124027994:ℝ):ℂ) + (((-0.9880515087762):ℝ):ℂ) * I)‖ ≤ 0.00000014913 := by
  have hl := lg_11
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.831982064477753836 32.83198208501578122 (-1.4160555) 0.00000004912 0.154124027994 (-0.9880515087762) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_12 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8606877570155):ℝ):ℂ) + (((-0.5091331700476):ℝ):ℂ) * I)‖ ≤ 0.00000012287 := by
  have hl := lg_12
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.023341838219781488 34.02334185875779518 (-2.6074153) 0.00000002286 (-0.8606877570155) (-0.5091331700476) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_13 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.846314941166):ℝ):ℂ) + ((0.5326828515051:ℝ):ℂ) * I)‖ ≤ 0.00000015141 := by
  have hl := lg_13
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.1192865916858364 35.119286612223863784 2.5798252 0.0000000514 (-0.846314941166) 0.5326828515051 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_14 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0056573966159:ℝ):ℂ) + ((0.9999839968036:ℝ):ℂ) * I)‖ ≤ 0.00000012389 := by
  have hl := lg_14
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.133972946414598024 36.133972966952625408 1.5651389 0.00000002388 0.0056573966159 0.9999839968036 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_15 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8135945238891:ℝ):ℂ) + ((0.5814326708207:ℝ):ℂ) * I)‖ ≤ 0.00000012029 := by
  have hl := lg_15
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.078623342813931116 37.0786233633519585 0.6204885 0.00000002028 0.8135945238891 0.5814326708207 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_16 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9655694241579:ℝ):ℂ) + (((-0.2601455114572):ℝ):ℂ) * I)‖ ≤ 0.00000015499 := by
  have hl := lg_16
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.9622847706704 37.9622847980544 (-0.2631729) 0.00000005498 0.9655694241579 (-0.2601455114572) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_17 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4596055661612:ℝ):ℂ) + (((-0.8881231466152):ℝ):ℂ) * I)‖ ≤ 0.00000015051 := by
  have hl := lg_17
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.792357092581014328 38.79235711996502802 (-1.0932453) 0.0000000505 0.4596055661612 (-0.8881231466152) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_18 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3003522875855):ℝ):ℂ) + (((-0.9538283406046):ℝ):ℂ) * I)‖ ≤ 0.00000014466 := by
  have hl := lg_18
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.574970098436762976 39.57497011897479036 (-1.8758583) 0.00000004465 (-0.3003522875855) (-0.9538283406046) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_19 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8651003378243):ℝ):ℂ) + (((-0.5015988490936):ℝ):ℂ) * I)‖ ≤ 0.00000015102 := by
  have hl := lg_19
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.315258492069368276 40.315258512607409352 (-2.6161467) 0.00000005101 (-0.8651003378243) (-0.5015988490936) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_20 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9844006858998):ℝ):ℂ) + ((0.1759411527891:ℝ):ℂ) * I)‖ ≤ 0.00000015241 := by
  have hl := lg_20
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.017566275264549628 41.01756630264856332 2.9647309 0.0000000524 (-0.9844006858998) 0.1759411527891 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_21 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6638085042793):ℝ):ℂ) + ((0.7479025803057:ℝ):ℂ) * I)‖ ≤ 0.00000014364 := by
  have hl := lg_21
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.685601206631579512 41.685601227169620588 2.2966959 0.00000004363 (-0.6638085042793) 0.7479025803057 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_22 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0888303322741):ℝ):ℂ) + ((0.9960467720281:ℝ):ℂ) * I)‖ ≤ 0.00000013429 := by
  have hl := lg_22
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.322553257145353836 42.32255328452938122 1.6597439 0.00000003428 (-0.0888303322741) 0.9960467720281 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_23 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4966076413879:ℝ):ℂ) + ((0.8679751439501:ℝ):ℂ) * I)‖ ≤ 0.00000016001 := by
  have hl := lg_23
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.931186790265199272 42.931186817649240348 1.0511103 0.00000006 0.4966076413879 0.8679751439501 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_24 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.892298942824:ℝ):ℂ) + ((0.4514450095362:ℝ):ℂ) * I)‖ ≤ 0.00000011938 := by
  have hl := lg_24
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.513913030887381488 43.51391305827139518 0.4683841 0.00000001937 0.892298942824 0.4514450095362 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_25 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9959030949186:ℝ):ℂ) + (((-0.0904269071213):ℝ):ℂ) * I)‖ ≤ 0.000000157 := by
  have hl := lg_25
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.072847779858699256 44.07284780724272664 (-0.0905506) 0.00000005699 0.9959030949186 (-0.0904269071213) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_26 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.809462262457:ℝ):ℂ) + (((-0.5871719046905):ℝ):ℂ) * I)‖ ≤ 0.0000001615 := by
  have hl := lg_26
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.6098577843534364 44.609857811737463784 (-0.6275606) 0.00000006149 0.809462262457 (-0.5871719046905) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_27 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4136824388051:ℝ):ℂ) + (((-0.9104212430651):ℝ):ℂ) * I)‖ ≤ 0.00000012895 := by
  have hl := lg_27
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.126598358653744464 45.12659837919178554 (-1.1443012) 0.00000002894 0.4136824388051 (-0.9104212430651) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_28 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0713898937411):ℝ):ℂ) + (((-0.9974484864249):ℝ):ℂ) * I)‖ ≤ 0.00000011622 := by
  have hl := lg_28
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.624544139082198024 45.624544166466225408 (-1.642247) 0.00000001621 (-0.0713898937411) (-0.9974484864249) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_29 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5243240254449):ℝ):ℂ) + (((-0.8515188291129):ℝ):ℂ) * I)‖ ≤ 0.00000016033 := by
  have hl := lg_29
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.105014489938106864 46.10501451732214794 (-2.1227174) 0.00000006032 (-0.5243240254449) (-0.8515188291129) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p692_30 : ‖exp (-((((((13692:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.850060984863):ℝ):ℂ) + (((-0.5266842715896):ℝ):ℂ) * I)‖ ≤ 0.00000011479 := by
  have hl := lg_30
  refine (ecis_approx ((((13692:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.569194535481531116 46.5691945628655585 (-2.5868974) 0.00000001478 (-0.850060984863) (-0.5266842715896) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_2 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9931532434277):ℝ):ℂ) + ((0.1168188110831:ℝ):ℂ) * I)‖ ≤ 0.00000013036 := by
  have hl := lg_2
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.5418640840098 9.5418640908928 3.0245065 0.00000003035 (-0.9931532434277) 0.1168188110831 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_3 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8340065911891):ℝ):ℂ) + (((-0.5517544796271):ℝ):ℂ) * I)‖ ≤ 0.00000015215 := by
  have hl := lg_3
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.123496762226785624 15.12349676910979939 (-2.5571262) 0.00000005214 (-0.8340065911891) (-0.5517544796271) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_4 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9727067323212:ℝ):ℂ) + (((-0.2320379557251):ℝ):ℂ) * I)‖ ≤ 0.00000015353 := by
  have hl := lg_4
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.0837281680196 19.0837281817856 (-0.2341723) 0.00000005352 0.9727067323212 (-0.2320379557251) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_5 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9865210241844):ℝ):ℂ) + ((0.1636345576869:ℝ):ℂ) * I)‖ ≤ 0.00000013332 := by
  have hl := lg_5
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.155522295411001094 22.15552230917701486 2.9772189 0.00000003331 (-0.9865210241844) 0.1636345576869 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_6 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.892751608647:ℝ):ℂ) + ((0.4505491818417:ℝ):ℂ) * I)‖ ≤ 0.0000001313 := by
  have hl := lg_6
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.665360846236585624 24.66536086000259939 0.4673804 0.00000003129 0.892751608647 0.4505491818417 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_7 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0837633113295):ℝ):ℂ) + (((-0.9964856786099):ℝ):ℂ) * I)‖ ≤ 0.00000012399 := by
  have hl := lg_7
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.787399104738619252 26.787399118504646784 (-1.6546579) 0.00000002398 (-0.0837633113295) (-0.9964856786099) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_8 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9389404824875):ℝ):ℂ) + ((0.3440795985946:ℝ):ℂ) * I)‖ ≤ 0.0000001368 := by
  have hl := lg_8
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.6255922520294 28.6255922726784 2.7903343 0.00000003679 (-0.9389404824875) 0.3440795985946 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_9 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3911339029179:ℝ):ℂ) + ((0.9203337818358:ℝ):ℂ) * I)‖ ≤ 0.00000011146 := by
  have hl := lg_9
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.246993524453571248 30.24699353821959878 1.168933 0.00000001145 0.3911339029179 0.9203337818358 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_10 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9606509626904:ℝ):ℂ) + (((-0.2777583984007):ℝ):ℂ) * I)‖ ≤ 0.00000015649 := by
  have hl := lg_10
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.697386379420801094 31.69738640006981486 (-0.2814599) 0.00000005648 0.9606509626904 (-0.2777583984007) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_11 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0227015228466):ℝ):ℂ) + (((-0.9997422872222):ℝ):ℂ) * I)‖ ≤ 0.00000012131 := by
  have hl := lg_11
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.009426314607125278 33.00942633525615281 (-1.5934998) 0.0000000213 (-0.0227015228466) (-0.9997422872222) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_12 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9392717732096):ℝ):ℂ) + (((-0.3431742063062):ℝ):ℂ) * I)‖ ≤ 0.00000011501 := by
  have hl := lg_12
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.207224930246385624 34.20722495089539939 (-2.7912984) 0.000000015 (-0.9392717732096) (-0.3431742063062) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_13 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7306153000586):ℝ):ℂ) + ((0.6827893403465:ℝ):ℂ) * I)‖ ≤ 0.00000012167 := by
  have hl := lg_13
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.3090928440802822 35.309092864729309732 2.390019 0.00000002166 (-0.7306153000586) 0.6827893403465 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_14 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1995980767916:ℝ):ℂ) + ((0.9798778534802:ℝ):ℂ) * I)‖ ≤ 0.00000015434 := by
  have hl := lg_14
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.329263188748419252 36.329263209397446784 1.3698486 0.00000005433 0.1995980767916 0.9798778534802 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_15 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9130510962106:ℝ):ℂ) + ((0.4078451859573:ℝ):ℂ) * I)‖ ≤ 0.00000013522 := by
  have hl := lg_15
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.279019057637786718 37.27901907828681425 0.4200928 0.00000003521 0.9130510962106 0.4078451859573 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_16 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8923168193468:ℝ):ℂ) + (((-0.4514096741441):ℝ):ℂ) * I)‖ ≤ 0.00000012051 := by
  have hl := lg_16
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.1674563360392 38.1674563635712 (-0.4683445) 0.0000000205 0.8923168193468 (-0.4514096741441) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_17 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2647003995479:ℝ):ℂ) + (((-0.9643306997494):ℝ):ℂ) * I)‖ ≤ 0.00000016313 := by
  have hl := lg_17
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.002014879964230444 39.00201490749624421 (-1.3029031) 0.00000006312 0.2647003995479 (-0.9643306997494) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_18 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4959681965299):ℝ):ℂ) + (((-0.8683406866114):ℝ):ℂ) * I)‖ ≤ 0.00000013463 := by
  have hl := lg_18
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.788857608463371248 39.78885762911239878 (-2.0897458) 0.00000003462 (-0.4959681965299) (-0.8683406866114) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_19 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9530758178473):ℝ):ℂ) + (((-0.3027317050176):ℝ):ℂ) * I)‖ ≤ 0.00000015406 := by
  have hl := lg_19
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.533146976469976898 40.533146997119018196 (-2.8340351) 0.00000005405 (-0.9530758178473) (-0.3027317050176) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_20 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9216262524229):ℝ):ℂ) + ((0.3880786656073:ℝ):ℂ) * I)‖ ≤ 0.00000014072 := by
  have hl := lg_20
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.239250463430601094 41.23925049096261486 2.7430467 0.00000004071 (-0.9216262524229) 0.3880786656073 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_21 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4799563647739):ℝ):ℂ) + ((0.8772923617059:ℝ):ℂ) * I)‖ ≤ 0.00000013737 := by
  have hl := lg_21
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.910895866965404876 41.910895887614446174 2.0714013 0.00000003736 (-0.4799563647739) 0.8772923617059 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_22 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.139334796645:ℝ):ℂ) + ((0.9902453304327:ℝ):ℂ) * I)‖ ≤ 0.00000015166 := by
  have hl := lg_22
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.551290398616925278 42.55129042614895281 1.4310067 0.00000005165 0.139334796645 0.9902453304327 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_23 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6828907966672:ℝ):ℂ) + ((0.7305204718741:ℝ):ℂ) * I)‖ ≤ 0.00000013946 := by
  have hl := lg_23
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.163213362167012356 43.163213389699053654 0.8190838 0.00000003945 0.6828907966672 0.7305204718741 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_24 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9729300111296:ℝ):ℂ) + ((0.2310999641784:ℝ):ℂ) * I)‖ ≤ 0.00000013602 := by
  have hl := lg_24
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.749089014256185624 43.74908904178819939 0.2332081 0.00000003601 0.9729300111296 0.2310999641784 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_25 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9464474652605:ℝ):ℂ) + (((-0.3228578564972):ℝ):ℂ) * I)‖ ≤ 0.00000015945 := by
  have hl := lg_25
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.311044590822002188 44.31104461835402972 (-0.3287475) 0.00000005944 0.9464474652605 (-0.3228578564972) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_26 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6458503214767:ℝ):ℂ) + (((-0.7634640543263):ℝ):ℂ) * I)‖ ≤ 0.00000012218 := by
  have hl := lg_26
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.8509569280900822 44.850956955622109732 (-0.8686598) 0.00000002217 0.6458503214767 (-0.7634640543263) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_27 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1815901321736:ℝ):ℂ) + (((-0.9833743050828):ℝ):ℂ) * I)‖ ≤ 0.00000015709 := by
  have hl := lg_27
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.370490286680356872 45.37049030732939817 (-1.3881931) 0.00000005708 0.1815901321736 (-0.9833743050828) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_28 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3126995416407):ℝ):ℂ) + (((-0.949852091989):ℝ):ℂ) * I)‖ ≤ 0.00000015005 := by
  have hl := lg_28
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.871127272758219252 45.871127300290246784 (-1.8888301) 0.00000005004 (-0.3126995416407) (-0.949852091989) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_29 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7181226417991):ℝ):ℂ) + (((-0.6959165692154):ℝ):ℂ) * I)‖ ≤ 0.00000015857 := by
  have hl := lg_29
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.354194381280162072 46.35419440881220337 (-2.3718972) 0.00000005856 (-0.7181226417991) (-0.6959165692154) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p766_30 : ‖exp (-((((((13766:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9544436453945):ℝ):ℂ) + (((-0.2983912323616):ℝ):ℂ) * I)‖ ≤ 0.00000011894 := by
  have hl := lg_30
  refine (ecis_approx ((((13766:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.820883141647586718 46.82088316917961425 (-2.838586) 0.00000001893 (-0.9544436453945) (-0.2983912323616) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_2 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9879792043873):ℝ):ℂ) + ((0.1545868406823:ℝ):ℂ) * I)‖ ≤ 0.00000013545 := by
  have hl := lg_2
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.5799871789263 9.5799871858368 2.9863834 0.00000003544 (-0.9879792043873) 0.1545868406823 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_3 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8658032793816):ℝ):ℂ) + (((-0.5003845334615):ℝ):ℂ) * I)‖ ≤ 0.00000013066 := by
  have hl := lg_3
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.183920438089234644 15.183920444999748465 (-2.6175498) 0.00000003065 (-0.8658032793816) (-0.5003845334615) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_4 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9522058499989:ℝ):ℂ) + (((-0.3054570660959):ℝ):ℂ) * I)‖ ≤ 0.00000015015 := by
  have hl := lg_4
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.1599743578526 19.1599743716736 (-0.3104184) 0.00000005014 0.9522058499989 (-0.3054570660959) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_5 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9681926649572):ℝ):ℂ) + ((0.2502058417771:ℝ):ℂ) * I)‖ ≤ 0.00000014817 := by
  have hl := lg_5
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.244041380566282589 22.24404139438729641 2.8886998 0.00000004816 (-0.9681926649572) 0.2502058417771 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_6 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9327484995398:ℝ):ℂ) + ((0.3605277196088:ℝ):ℂ) * I)‖ ≤ 0.00000011172 := by
  have hl := lg_6
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.763907617015534644 24.763907630836548465 0.3688336 0.00000001171 0.9327484995398 0.3605277196088 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_7 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.189729439282):ℝ):ℂ) + (((-0.9818364119694):ℝ):ℂ) * I)‖ ≤ 0.00000014803 := by
  have hl := lg_7
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.894424162908067462 26.894424176729095104 (-1.7616829) 0.00000004802 (-0.189729439282) (-0.9818364119694) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_8 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8935399353527):ℝ):ℂ) + ((0.448983723336:ℝ):ℂ) * I)‖ ≤ 0.00000012163 := by
  have hl := lg_8
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.7399615367789 28.7399615575104 2.675965 0.00000002162 (-0.8935399353527) 0.448983723336 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_9 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.499230643473:ℝ):ℂ) + ((0.8664691365638:ℝ):ℂ) * I)‖ ≤ 0.00000015412 := by
  have hl := lg_9
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.367840876178469288 30.36784088999949693 1.0480857 0.00000005411 0.499230643473 0.8664691365638 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_10 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9178757309475:ℝ):ℂ) + (((-0.3968679157321):ℝ):ℂ) * I)‖ ≤ 0.00000014434 := by
  have hl := lg_10
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.824028559492582589 31.82402858022409641 (-0.408102) 0.00000004433 0.9178757309475 (-0.3968679157321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_11 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1539727025516):ℝ):ℂ) + (((-0.988075101836):ℝ):ℂ) * I)‖ ≤ 0.00000013942 := by
  have hl := lg_11
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.141310554568144593 33.141310575299672235 (-1.725384) 0.00000003941 (-0.1539727025516) (-0.988075101836) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_12 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9772689601975):ℝ):ℂ) + (((-0.2120032526322):ℝ):ℂ) * I)‖ ≤ 0.00000013997 := by
  have hl := lg_12
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.343894795941834644 34.343894816673348465 (-2.9279683) 0.00000003996 (-0.9772689601975) (-0.2120032526322) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_13 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6273538077874):ℝ):ℂ) + ((0.7787343576857:ℝ):ℂ) * I)‖ ≤ 0.00000013637 := by
  have hl := lg_13
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.4501650586977757 35.450165079429303342 2.2489468 0.00000003636 (-0.6273538077874) 0.7787343576857 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_14 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.339227729679:ℝ):ℂ) + ((0.9407042826611:ℝ):ℂ) * I)‖ ≤ 0.0000001195 := by
  have hl := lg_14
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.474411341834367462 36.474411362565895104 1.2247005 0.00000001949 0.339227729679 0.9407042826611 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_15 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9634635179879:ℝ):ℂ) + ((0.2678395965992:ℝ):ℂ) * I)‖ ≤ 0.00000012444 := by
  have hl := lg_15
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.427961818655517233 37.427961839387044875 0.27115 0.00000002443 0.9634635179879 0.2678395965992 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_16 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8133919033726:ℝ):ℂ) + (((-0.5817160918592):ℝ):ℂ) * I)‖ ≤ 0.00000012739 := by
  have hl := lg_16
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.3199487157052 38.3199487433472 (-0.6208369) 0.00000002738 0.8133919033726 (-0.5817160918592) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_17 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1118321018787:ℝ):ℂ) + (((-0.9937271159575):ℝ):ℂ) * I)‖ ≤ 0.00000012926 := by
  have hl := lg_17
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.157841613830134314 39.157841641472148135 (-1.4587298) 0.00000002925 0.1118321018787 (-0.9937271159575) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_18 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6271742149659):ℝ):ℂ) + (((-0.7788790047674):ℝ):ℂ) * I)‖ ≤ 0.00000013277 := by
  have hl := lg_18
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.947828055104769288 39.94782807583629693 (-2.2487162) 0.00000003276 (-0.6271742149659) (-0.7788790047674) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_19 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9894170946261):ℝ):ℂ) + (((-0.1450993192997):ℝ):ℂ) * I)‖ ≤ 0.00000012281 := by
  have hl := lg_19
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.695091120281240063 40.695091141012781526 (-2.9959793) 0.0000000228 (-0.9894170946261) (-0.1450993192997) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_20 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8454915771878):ℝ):ℂ) + ((0.5339887572163:ℝ):ℂ) * I)‖ ≤ 0.00000011582 := by
  have hl := lg_20
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.404015738418882589 41.40401576606089641 2.5782814 0.00000001581 (-0.8454915771878) 0.5339887572163 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_21 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3270272829687):ℝ):ℂ) + ((0.9450148973387:ℝ):ℂ) * I)‖ ≤ 0.00000014927 := by
  have hl := lg_21
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.078344600997302106 42.078344621728843569 1.9039525 0.00000004926 (-0.3270272829687) 0.9450148973387 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_22 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3048652367243:ℝ):ℂ) + ((0.9523954994838:ℝ):ℂ) * I)‖ ≤ 0.00000011678 := by
  have hl := lg_22
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.721297733494444593 42.721297761136472235 1.2609994 0.00000001677 0.3048652367243 0.9523954994838 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_23 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.798117788357:ℝ):ℂ) + ((0.6025014488847:ℝ):ℂ) * I)‖ ≤ 0.00000012139 := by
  have hl := lg_23
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.335665543985927486 43.335665571627968949 0.6466316 0.00000002138 0.798117788357 0.6025014488847 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_24 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9982943173174:ℝ):ℂ) + ((0.0583819836234:ℝ):ℂ) * I)‖ ≤ 0.00000015227 := by
  have hl := lg_24
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.923881974868134644 43.923882002510148465 0.0584152 0.00000005226 0.9982943173174 0.0583819836234 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_25 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8747941252756:ℝ):ℂ) + (((-0.4844948280253):ℝ):ℂ) * I)‖ ≤ 0.00000013853 := by
  have hl := lg_25
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.488082761132565178 44.48808278877459282 (-0.5057856) 0.00000003852 0.8747941252756 (-0.4844948280253) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_26 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4994304379805:ℝ):ℂ) + (((-0.8663539909406):ℝ):ℂ) * I)‖ ≤ 0.00000011502 := by
  have hl := lg_26
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.0301522376240757 45.030152265266103342 (-1.0478551) 0.00000001501 0.4994304379805 (-0.8663539909406) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_27 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0013321264009:ℝ):ℂ) + (((-0.9999991127191):ℝ):ℂ) * I)‖ ≤ 0.000000136 := by
  have hl := lg_27
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.551761314267703932 45.551761334999245395 (-1.5694642) 0.00000003599 0.0013321264009 (-0.9999991127191) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_28 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4805704394832):ℝ):ℂ) + (((-0.8769561292843):ℝ):ℂ) * I)‖ ≤ 0.00000012951 := by
  have hl := lg_28
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.054398520760667462 46.054398548402695104 (-2.0721014) 0.0000000295 (-0.4805704394832) (-0.8769561292843) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_29 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.83399130727):ℝ):ℂ) + (((-0.551777581398):ℝ):ℂ) * I)‖ ≤ 0.00000012927 := by
  have hl := lg_29
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.539395651872230132 46.539395679514271595 (-2.5570985) 0.00000002926 (-0.83399130727) (-0.551777581398) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_30 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9932863961845):ℝ):ℂ) + (((-0.1156811769761):ℝ):ℂ) * I)‖ ≤ 0.00000015269 := by
  have hl := lg_30
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.007948997581817233 47.007949025223844875 (-3.0256519) 0.00000005268 (-0.9932863961845) (-0.1156811769761) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_31 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9436690646979):ℝ):ℂ) + ((0.3308907616488:ℝ):ℂ) * I)‖ ≤ 0.00000011863 := by
  have hl := lg_31
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.461137138818362023 47.461137166460403486 2.8043453 0.00000001862 (-0.9436690646979) 0.3308907616488 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_32 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7136886327571):ℝ):ℂ) + ((0.7004630864272:ℝ):ℂ) * I)‖ ≤ 0.00000016282 := by
  have hl := lg_32
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.8999358946315 47.899935929184 2.3655465 0.00000006281 (-0.7136886327571) 0.7004630864272 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_33 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3611074214004):ℝ):ℂ) + ((0.9325242249974:ℝ):ℂ) * I)‖ ≤ 0.00000016288 := by
  have hl := lg_33
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.325230992657379237 48.3252310202994207 1.9402515 0.00000006287 (-0.3611074214004) 0.9325242249974 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_34 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0431293444843:ℝ):ℂ) + ((0.9990694969041:ℝ):ℂ) * I)‖ ≤ 0.0000001647 := by
  have hl := lg_34
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.737828792756434314 48.737828827308948135 1.5276536 0.00000006469 0.0431293444843 0.9990694969041 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_35 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4293558575338:ℝ):ℂ) + ((0.9031353982662:ℝ):ℂ) * I)‖ ≤ 0.00000011398 := by
  have hl := lg_35
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.138465543474350051 49.138465571116391514 1.1270169 0.00000001397 0.4293558575338 0.9031353982662 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_36 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7400395267874:ℝ):ℂ) + ((0.6725633790151:ℝ):ℂ) * I)‖ ≤ 0.00000012342 := by
  have hl := lg_36
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.527815234031069288 49.52781526167309693 0.7376672 0.00000002341 0.7400395267874 0.6725633790151 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_37 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9362535485466:ℝ):ℂ) + ((0.351325052955:ℝ):ℂ) * I)‖ ≤ 0.00000012651 := by
  have hl := lg_37
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.906496456284992882 49.906496483927034345 0.358986 0.0000000265 0.9362535485466 0.351325052955 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_38 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999539597049:ℝ):ℂ) + (((-0.0095957527335):ℝ):ℂ) * I)‖ ≤ 0.00000015824 := by
  have hl := lg_38
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.275078299207540063 50.275078326849581526 (-0.0095959) 0.00000005823 0.9999539597049 (-0.0095957527335) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_39 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9328315763998:ℝ):ℂ) + (((-0.3603127115041):ℝ):ℂ) * I)‖ ≤ 0.00000016066 := by
  have hl := lg_39
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.634085496787010344 50.634085524429051807 (-0.3686031) 0.00000006065 0.9328315763998 (-0.3603127115041) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p821_40 : ‖exp (-((((((13821:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7527804655859:ℝ):ℂ) + (((-0.6582716541309):ℝ):ℂ) * I)‖ ≤ 0.00000014011 := by
  have hl := lg_40
  refine (ecis_approx ((((13821:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.984002917345182589 50.98400295189769641 (-0.7185205) 0.0000000401 0.7527804655859 (-0.6582716541309) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_2 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9813694391603):ℝ):ℂ) + ((0.1921302254954:ℝ):ℂ) * I)‖ ≤ 0.00000014053 := by
  have hl := lg_2
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.6181102738428 9.6181102807808 2.9482603 0.00000004052 (-0.9813694391603) 0.1921302254954 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_3 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8944399162527):ℝ):ℂ) + (((-0.4471881439659):ℝ):ℂ) * I)‖ ≤ 0.00000010655 := by
  have hl := lg_3
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.244344113951683664 15.24434412088969754 (-2.6779735) 0.00000000654 (-0.8944399162527) (-0.4471881439659) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_4 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9261719931934:ℝ):ℂ) + (((-0.3771013643891):ℝ):ℂ) * I)‖ ≤ 0.00000014004 := by
  have hl := lg_4
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.2362205476856 19.2362205615616 (-0.3866646) 0.00000004003 0.9261719931934 (-0.3771013643891) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_5 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9422828910623):ℝ):ℂ) + ((0.334817790786:ℝ):ℂ) * I)‖ ≤ 0.00000015089 := by
  have hl := lg_5
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.332560465721564084 22.33256047959757796 2.8001808 0.00000005088 (-0.9422828910623) 0.334817790786 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_6 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9636943581538:ℝ):ℂ) + ((0.2670078352082:ℝ):ℂ) * I)‖ ≤ 0.00000014094 := by
  have hl := lg_6
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.862454387794483664 24.86245440167049754 0.2702868 0.00000004093 0.9636943581538 0.2670078352082 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_7 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2935245089255):ℝ):ℂ) + (((-0.9559515482797):ℝ):ℂ) * I)‖ ≤ 0.00000010766 := by
  have hl := lg_7
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.001449221077515672 27.001449234953543424 (-1.868708) 0.00000000765 (-0.2935245089255) (-0.9559515482797) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_8 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8364643194016):ℝ):ℂ) + ((0.5480213885444:ℝ):ℂ) * I)‖ ≤ 0.00000011438 := by
  have hl := lg_8
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.8543308215284 28.8543308423424 2.5615957 0.00000001437 (-0.8364643194016) 0.5480213885444 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_9 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6000455334294:ℝ):ℂ) + ((0.7999658479032:ℝ):ℂ) * I)‖ ≤ 0.00000010801 := by
  have hl := lg_9
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.488688227903367328 30.48868824177939508 0.9272383 0.000000008 0.6000455334294 0.7999658479032 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_10 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.860399018466:ℝ):ℂ) + (((-0.5096209660353):ℝ):ℂ) * I)‖ ≤ 0.0000001245 := by
  have hl := lg_10
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.950670739564364084 31.95067076037837796 (-0.5347442) 0.00000002449 0.860399018466 (-0.5096209660353) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_11 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2825697424314):ℝ):ℂ) + (((-0.9592467569196):ℝ):ℂ) * I)‖ ≤ 0.00000014138 := by
  have hl := lg_11
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.273194794529163908 33.27319481534319166 (-1.8572683) 0.00000004137 (-0.2825697424314) (-0.9592467569196) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_12 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9970404590661):ℝ):ℂ) + (((-0.0768786216488):ℝ):ℂ) * I)‖ ≤ 0.00000014657 := by
  have hl := lg_12
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.480564661637283664 34.48056468245129754 (-3.0646381) 0.00000004656 (-0.9970404590661) (-0.0768786216488) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_13 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5116278103256):ℝ):ℂ) + ((0.8592071832187:ℝ):ℂ) * I)‖ ≤ 0.00000015107 := by
  have hl := lg_13
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.5912372733152692 35.591237294129296952 2.1078746 0.00000005106 (-0.5116278103256) 0.8592071832187 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_14 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4717231694353:ℝ):ℂ) + ((0.8817467047956:ℝ):ℂ) * I)‖ ≤ 0.00000014817 := by
  have hl := lg_14
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.619559494920315672 36.619559515734343424 1.0795523 0.00000004816 0.4717231694353 0.8817467047956 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_15 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9925419767464:ℝ):ℂ) + ((0.1219033403821:ℝ):ℂ) * I)‖ ≤ 0.00000015742 := by
  have hl := lg_15
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.576904579673247748 37.5769046004872755 0.1222073 0.00000005741 0.9925419767464 0.1219033403821 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_16 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7155890520997:ℝ):ℂ) + (((-0.6985215161433):ℝ):ℂ) * I)‖ ≤ 0.00000014772 := by
  have hl := lg_16
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.4724410953712 38.4724411231232 (-0.7733293) 0.00000004771 0.7155890520997 (-0.6985215161433) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_17 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0437462080983):ℝ):ℂ) + (((-0.9990426764041):ℝ):ℂ) * I)‖ ≤ 0.00000013239 := by
  have hl := lg_17
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.313668347696038184 39.31366837544805206 (-1.6145565) 0.00000003238 (-0.0437462080983) (-0.9990426764041) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_18 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7425639627586):ℝ):ℂ) + (((-0.6697751571835):ℝ):ℂ) * I)‖ ≤ 0.00000014135 := by
  have hl := lg_18
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.106798501746167328 40.10679852256019508 (-2.4076867) 0.00000004134 (-0.7425639627586) (-0.6697751571835) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_19 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998666558878):ℝ):ℂ) + ((0.016330027425:ℝ):ℂ) * I)‖ ≤ 0.00000013466 := by
  have hl := lg_19
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.857035264092503228 40.857035284906544856 3.1252619 0.00000003465 (-0.9998666558878) 0.016330027425 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_20 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7464557111136):ℝ):ℂ) + ((0.6654350992492:ℝ):ℂ) * I)‖ ≤ 0.00000013686 := by
  have hl := lg_20
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.568781013407164084 41.56878104115917796 2.4135161 0.00000003685 (-0.7464557111136) 0.6654350992492 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_21 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1649501543821):ℝ):ℂ) + ((0.9863019043724:ℝ):ℂ) * I)‖ ≤ 0.00000011524 := by
  have hl := lg_21
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.245793335029199336 42.245793355843240964 1.7365038 0.00000001523 (-0.1649501543821) 0.9863019043724 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_22 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4616055168543:ℝ):ℂ) + ((0.88708530977:ℝ):ℂ) * I)‖ ≤ 0.00000014588 := by
  have hl := lg_22
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.891305068371963908 42.89130509612399166 1.0909921 0.00000004587 0.4616055168543 0.88708530977 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_23 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8896677140929:ℝ):ℂ) + ((0.4566085396712:ℝ):ℂ) * I)‖ ≤ 0.00000012447 := by
  have hl := lg_23
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.508117725804842616 43.508117753556884244 0.4741794 0.00000002446 0.8896677140929 0.4566085396712 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_24 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9932357434801:ℝ):ℂ) + (((-0.1161152783808):ℝ):ℂ) * I)‖ ≤ 0.00000011479 := by
  have hl := lg_24
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.098674935480083664 44.09867496323209754 (-0.1163778) 0.00000001478 0.9932357434801 (-0.1161152783808) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_25 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7757940352487:ℝ):ℂ) + (((-0.6309862239958):ℝ):ℂ) * I)‖ ≤ 0.00000011883 := by
  have hl := lg_25
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.665120931443128168 44.66512095919515592 (-0.6828238) 0.00000001882 0.7757940352487 (-0.6309862239958) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_26 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3370162341072:ℝ):ℂ) + (((-0.9414988358719):ℝ):ℂ) * I)‖ ≤ 0.00000012467 := by
  have hl := lg_26
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.2093475471580692 45.209347574910096952 (-1.2270504) 0.00000002466 0.3370162341072 (-0.9414988358719) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_27 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1789694338799):ℝ):ℂ) + (((-0.9838546344537):ℝ):ℂ) * I)‖ ≤ 0.00000011243 := by
  have hl := lg_27
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.733032341855050992 45.73303236266909262 (-1.7507352) 0.00000001242 (-0.1789694338799) (-0.9838546344537) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_28 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6323448126276):ℝ):ℂ) + (((-0.7746870580615):ℝ):ℂ) * I)‖ ≤ 0.00000014627 := by
  have hl := lg_28
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.237669768763115672 46.237669796515143424 (-2.2553726) 0.00000004626 (-0.6323448126276) (-0.7746870580615) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_29 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9213361394256):ℝ):ℂ) + (((-0.3887669199448):ℝ):ℂ) * I)‖ ≤ 0.00000012781 := by
  have hl := lg_29
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.724596922464298192 46.72459695021633982 (-2.7422998) 0.0000000278 (-0.9213361394256) (-0.3887669199448) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_30 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9974716792474):ℝ):ℂ) + ((0.0710651009243:ℝ):ℂ) * I)‖ ≤ 0.00000012385 := by
  have hl := lg_30
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.195014853516047748 47.1950148812680755 3.0704676 0.00000002384 (-0.9974716792474) 0.0710651009243 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_31 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8647637209238):ℝ):ℂ) + ((0.5021789590276:ℝ):ℂ) * I)‖ ≤ 0.00000012244 := by
  have hl := lg_31
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.650006435007856988 47.650006462759898616 2.615476 0.00000002243 (-0.8647637209238) 0.5021789590276 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_32 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5680502126008):ℝ):ℂ) + ((0.8229938978841:ℝ):ℂ) * I)‖ ≤ 0.00000014648 := by
  have hl := lg_32
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.090551369214 48.090551403904 2.1749311 0.00000004647 (-0.5680502126008) 0.8229938978841 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_33 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1762221130579):ℝ):ℂ) + ((0.9843504288965:ℝ):ℂ) * I)‖ ≤ 0.00000014897 := by
  have hl := lg_33
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.517538908480847572 48.5175389362328892 1.7479435 0.00000004896 (-0.1762221130579) 0.9843504288965 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_34 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.234877486574:ℝ):ℂ) + ((0.9720249823439:ℝ):ℂ) * I)‖ ≤ 0.00000013591 := by
  have hl := lg_34
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.931778621538838184 48.93177865622885206 1.3337038 0.0000000359 0.234877486574 0.9720249823439 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_35 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5966527084726:ℝ):ℂ) + ((0.8024995610419:ℝ):ℂ) * I)‖ ≤ 0.00000015713 := by
  have hl := lg_35
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.334009686799079756 49.334009714551121384 0.9314728 0.00000005712 0.5966527084726 0.8024995610419 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_36 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.857413580412:ℝ):ℂ) + ((0.5146279744874:ℝ):ℂ) * I)‖ ≤ 0.00000014592 := by
  have hl := lg_36
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.724908775588967328 49.72490880334099508 0.5405737 0.00000004591 0.857413580412 0.5146279744874 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_37 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9871657928525:ℝ):ℂ) + ((0.1596987708844:ℝ):ℂ) * I)‖ ≤ 0.00000011603 := by
  have hl := lg_37
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.105096941423237192 50.10509696917527882 0.1603855 0.00000001602 0.9871657928525 0.1596987708844 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_38 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.978101089359:ℝ):ℂ) + (((-0.2081303894069):ℝ):ℂ) * I)‖ ≤ 0.00000011952 := by
  have hl := lg_38
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.475145537935303228 50.475145565687344856 (-0.2096631) 0.00000001951 0.978101089359 (-0.2081303894069) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_39 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8418476014353:ℝ):ℂ) + (((-0.5397153101011):ℝ):ℂ) * I)‖ ≤ 0.0000001576 := by
  have hl := lg_39
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.835581387266952864 50.835581415018994492 (-0.5700989) 0.00000005759 0.8418476014353 (-0.5397153101011) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p876_40 : ‖exp (-((((((13876:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6046987122611:ℝ):ℂ) + (((-0.7964543096687):ℝ):ℂ) * I)‖ ≤ 0.00000016452 := by
  have hl := lg_40
  refine (ecis_approx ((((13876:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.186891287249964084 51.18689132193997796 (-0.9214088) 0.00000006451 0.6046987122611 (-0.7964543096687) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_2 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9755137555177):ℝ):ℂ) + ((0.2199384288782:ℝ):ℂ) * I)‖ ≤ 0.00000010614 := by
  have hl := lg_2
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.6465293082351 9.6465293151936 2.9198413 0.00000000613 (-0.9755137555177) 0.2199384288782 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_3 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.913668643408):ℝ):ℂ) + (((-0.4064598503164):ℝ):ℂ) * I)‖ ≤ 0.00000011039 := by
  have hl := lg_3
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.289387217776418388 15.289387224734932305 (-2.7230166) 0.00000001038 (-0.913668643408) (-0.4064598503164) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_4 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.903254177955:ℝ):ℂ) + (((-0.4291059193334):ℝ):ℂ) * I)‖ ≤ 0.00000010886 := by
  have hl := lg_4
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.2930586164702 19.2930586303872 (-0.4435027) 0.00000000885 0.903254177955 (-0.4291059193334) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_5 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.918154560225):ℝ):ℂ) + ((0.3962224165766:ℝ):ℂ) * I)‖ ≤ 0.00000010862 := by
  have hl := lg_5
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.398547420110046653 22.39854743402706057 2.7341938 0.00000000861 (-0.918154560225) 0.3962224165766 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_6 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.980692470736:ℝ):ℂ) + ((0.195556329076:ℝ):ℂ) * I)‖ ≤ 0.00000011123 := by
  have hl := lg_6
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.935916526011518388 24.935916539928532305 0.1968247 0.00000001122 0.980692470736 0.195556329076 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_7 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3687779595455):ℝ):ℂ) + (((-0.9295175181516):ℝ):ℂ) * I)‖ ≤ 0.00000012238 := by
  have hl := lg_7
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.081231537167467974 27.081231551084495808 (-1.9484903) 0.00000002237 (-0.3687779595455) (-0.9295175181516) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_8 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7867599936386):ℝ):ℂ) + ((0.6172590318216:ℝ):ℂ) * I)‖ ≤ 0.00000011121 := by
  have hl := lg_8
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.9395879247053 28.9395879455808 2.4763386 0.0000000112 (-0.7867599936386) 0.6172590318216 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_9 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6695807853778:ℝ):ℂ) + ((0.7427392354339:ℝ):ℂ) * I)‖ ≤ 0.00000011359 := by
  have hl := lg_9
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.578774435552836776 30.57877444946986461 0.8371521 0.00000001358 0.6695807853778 0.7427392354339 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_10 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8085278717046:ℝ):ℂ) + (((-0.58845788352):ℝ):ℂ) * I)‖ ≤ 0.00000011334 := by
  have hl := lg_10
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.045076728345146653 32.04507674922066057 (-0.6291502) 0.00000001333 0.8085278717046 (-0.58845788352) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_11 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3753604903857):ℝ):ℂ) + (((-0.9268789037704):ℝ):ℂ) * I)‖ ≤ 0.00000013523 := by
  have hl := lg_11
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.371508500681923761 33.371508521557451595 (-1.955582) 0.00000003522 (-0.3753604903857) (-0.9268789037704) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_12 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996893467489):ℝ):ℂ) + ((0.0249240720741:ℝ):ℂ) * I)‖ ≤ 0.00000011206 := by
  have hl := lg_12
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.582445834246618388 34.582445855122132305 3.116666 0.00000001205 (-0.9996893467489) 0.0249240720741 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_13 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4186109545122):ℝ):ℂ) + ((0.908165661517:ℝ):ℂ) * I)‖ ≤ 0.00000014615 := by
  have hl := lg_13
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.6964001969392189 35.696400217814746734 2.0027116 0.00000004614 (-0.4186109545122) 0.908165661517 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_14 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5641845950081:ℝ):ℂ) + ((0.8256486799817:ℝ):ℂ) * I)‖ ≤ 0.00000012322 := by
  have hl := lg_14
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.727760845402567974 36.727760866278095808 0.971351 0.00000002321 0.5641845950081 0.8256486799817 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_15 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999375357504:ℝ):ℂ) + ((0.0111769672739:ℝ):ℂ) * I)‖ ≤ 0.0000001157 := by
  have hl := lg_15
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.687934637886465041 37.687934658761992875 0.0111772 0.00000001569 0.9999375357504 0.0111769672739 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_16 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6317362199862:ℝ):ℂ) + (((-0.7751834288461):ℝ):ℂ) * I)‖ ≤ 0.00000011771 := by
  have hl := lg_16
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.5861172329404 38.5861172607744 (-0.8870054) 0.0000000177 0.6317362199862 (-0.7751834288461) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_17 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1592411759487):ℝ):ℂ) + (((-0.9872397114591):ℝ):ℂ) * I)‖ ≤ 0.00000014833 := by
  have hl := lg_17
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.429830094759711978 39.429830122593725895 (-1.7307183) 0.00000004832 (-0.1592411759487) (-0.9872397114591) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_18 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8165421631075):ℝ):ℂ) + (((-0.5772858008055):ℝ):ℂ) * I)‖ ≤ 0.0000001216 := by
  have hl := lg_18
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.225303743787936776 40.22530376466346461 (-2.5261919) 0.00000002159 (-0.8165421631075) (-0.5772858008055) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_19 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9906229627451):ℝ):ℂ) + ((0.136624102077:ℝ):ℂ) * I)‖ ≤ 0.00000013284 := by
  have hl := lg_19
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.977757262206353951 40.977757283081895702 3.0045399 0.00000003283 (-0.9906229627451) 0.136624102077 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_20 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6593055582118):ℝ):ℂ) + ((0.751875109904:ℝ):ℂ) * I)‖ ≤ 0.00000011417 := by
  have hl := lg_20
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.691606036580246653 41.69160606441426057 2.2906911 0.00000001416 (-0.6593055582118) 0.751875109904 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_21 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0408706861561):ℝ):ℂ) + ((0.9991644444299:ℝ):ℂ) * I)‖ ≤ 0.00000012558 := by
  have hl := lg_21
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.370618754943886362 42.370618775819428113 1.6116784 0.00000002557 (-0.0408706861561) 0.9991644444299 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_22 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5700256116878:ℝ):ℂ) + ((0.821626923865:ℝ):ℂ) * I)‖ ≤ 0.00000014136 := by
  have hl := lg_22
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.018037808917023761 43.018037836751051595 0.9642593 0.00000004135 0.5700256116878 0.821626923865 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_23 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9408642007991:ℝ):ℂ) + ((0.3387839365357:ℝ):ℂ) * I)‖ ≤ 0.00000016166 := by
  have hl := lg_23
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.636672988615306622 43.636673016449348373 0.3456241 0.00000006165 0.9408642007991 0.3387839365357 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_24 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9697289498509:ℝ):ℂ) + (((-0.244183872975):ℝ):ℂ) * I)‖ ≤ 0.00000012007 := by
  have hl := lg_24
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.228975142481718388 44.228975170315732305 (-0.246678) 0.00000002006 0.9697289498509 (-0.244183872975) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_25 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6860155983096:ℝ):ℂ) + (((-0.7275868325333):ℝ):ℂ) * I)‖ ≤ 0.00000011781 := by
  have hl := lg_25
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.797094840220093306 44.79709486805412114 (-0.8147977) 0.0000000178 0.6860155983096 (-0.7275868325333) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_26 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2086202225177:ℝ):ℂ) + (((-0.9779967294202):ℝ):ℂ) * I)‖ ≤ 0.0000001451 := by
  have hl := lg_26
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.3429295051743189 45.342929533008346734 (-1.3606324) 0.00000004509 0.2086202225177 (-0.9779967294202) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_27 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3098812893443):ℝ):ℂ) + (((-0.9507752555218):ℝ):ℂ) * I)‖ ≤ 0.00000012396 := by
  have hl := lg_27
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.868161653329255164 45.868161674204796915 (-1.8858645) 0.00000002395 (-0.3098812893443) (-0.9507752555218) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_28 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.731961701856):ℝ):ℂ) + (((-0.6813457763767):ℝ):ℂ) * I)‖ ≤ 0.00000013123 := by
  have hl := lg_28
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.374290153637667974 46.374290181471695808 (-2.391993) 0.00000003122 (-0.731961701856) (-0.6813457763767) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_29 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9660720685696):ℝ):ℂ) + (((-0.2582726429075):ℝ):ℂ) * I)‖ ≤ 0.00000012904 := by
  have hl := lg_29
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.862656051451112564 46.862656079285154315 (-2.8803589) 0.00000002903 (-0.9660720685696) (-0.2582726429075) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_30 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9779110653996):ℝ):ℂ) + ((0.2090214052613:ℝ):ℂ) * I)‖ ≤ 0.00000011653 := by
  have hl := lg_30
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.334463946121565041 47.334463973955592875 2.9310185 0.00000001652 (-0.9779110653996) 0.2090214052613 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_31 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7857366725132):ℝ):ℂ) + ((0.6185611379838:ℝ):ℂ) * I)‖ ≤ 0.0000001471 := by
  have hl := lg_31
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.790799910349116871 47.790799938183158622 2.4746825 0.00000004709 (-0.7857366725132) 0.6185611379838 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_32 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4457747469824):ℝ):ℂ) + ((0.8951451697621:ℝ):ℂ) * I)‖ ≤ 0.00000011855 := by
  have hl := lg_32
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.2326465411755 48.232646575968 2.0328359 0.00000001854 (-0.4457747469824) 0.8951451697621 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_33 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0337839433244):ℝ):ℂ) + ((0.9994291596572:ℝ):ℂ) * I)‖ ≤ 0.00000013899 := by
  have hl := lg_33
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.660895718458342149 48.6608957462923839 1.6045867 0.00000003898 (-0.0337839433244) 0.9994291596572 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_34 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3724739088133:ℝ):ℂ) + ((0.9280426645652:ℝ):ℂ) * I)‖ ≤ 0.00000015446 := by
  have hl := lg_34
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.076359402994811978 49.076359437787325895 1.189123 0.00000005445 0.3724739088133 0.9280426645652 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_35 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7068908426458:ℝ):ℂ) + ((0.7073226538035:ℝ):ℂ) * I)‖ ≤ 0.00000012769 := by
  have hl := lg_35
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.479778957277514627 49.479778985111556378 0.7857035 0.00000002768 0.7068908426458 0.7073226538035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_36 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9235154443166:ℝ):ℂ) + ((0.3835612390592:ℝ):ℂ) * I)‖ ≤ 0.00000012244 := by
  have hl := lg_36
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.871833052023036776 49.87183307985706461 0.3936494 0.00000002243 0.9235154443166 0.3835612390592 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_37 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999238890773:ℝ):ℂ) + ((0.0123375869821:ℝ):ℂ) * I)‖ ≤ 0.00000014621 := by
  have hl := lg_37
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.253144575799019314 50.253144603633061065 0.0123379 0.0000000462 0.9999238890773 0.0123375869821 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_38 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9363174390842:ℝ):ℂ) + (((-0.3511547426232):ℝ):ℂ) * I)‖ ≤ 0.00000014085 := by
  have hl := lg_38
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.624286570441453951 50.624286598275495702 (-0.3588041) 0.00000004084 0.9363174390842 (-0.3511547426232) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_39 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7516045818507:ℝ):ℂ) + (((-0.6596139420457):ℝ):ℂ) * I)‖ ≤ 0.00000014274 := by
  have hl := lg_39
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.985787414715637288 50.985787442549679039 (-0.720305) 0.00000004273 0.7516045818507 (-0.6596139420457) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_40 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4777954170134:ℝ):ℂ) + (((-0.8784711375344):ℝ):ℂ) * I)‖ ≤ 0.00000012219 := by
  have hl := lg_40
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.338135344815346653 51.33813537960786057 (-1.0726529) 0.00000002218 0.4777954170134 (-0.8784711375344) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_41 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1538824447957:ℝ):ℂ) + (((-0.9880891625676):ℝ):ℂ) * I)‖ ≤ 0.00000012322 := by
  have hl := lg_41
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.68178243423553986 51.681782469028067694 (-1.4163) 0.00000002321 0.1538824447957 (-0.9880891625676) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_42 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1798847346378):ℝ):ℂ) + (((-0.9836876954824):ℝ):ℂ) * I)‖ ≤ 0.00000013359 := by
  have hl := lg_42
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.017148063178986362 52.017148091013028113 (-1.7516656) 0.00000003358 (-0.1798847346378) (-0.9836876954824) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_43 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4867306783728):ℝ):ℂ) + (((-0.8735520858684):ℝ):ℂ) * I)‖ ≤ 0.00000016182 := by
  have hl := lg_43
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.34462199563665626 52.344622023470711928 (-2.0791396) 0.00000006181 (-0.4867306783728) (-0.8735520858684) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_44 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7367751552889):ℝ):ℂ) + (((-0.6761378339646):ℝ):ℂ) * I)‖ ≤ 0.0000001403 := by
  have hl := lg_44
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.664567117152123761 52.664567151944651595 (-2.3990847) 0.00000004029 (-0.7367751552889) (-0.6761378339646) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_45 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9090685833385):ℝ):ℂ) + (((-0.416646505637):ℝ):ℂ) * I)‖ ≤ 0.00000012608 := by
  have hl := lg_45
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.977321855662883429 52.97732188349692518 (-2.7118394) 0.00000002607 (-0.9090685833385) (-0.416646505637) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_46 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9923375757669):ℝ):ℂ) + (((-0.1235562029451):ℝ):ℂ) * I)‖ ≤ 0.0000001606 := by
  have hl := lg_46
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.283202296850406622 53.283202331642948373 (-3.0177199) 0.00000006059 (-0.9923375757669) (-0.1235562029451) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_47 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9846517463977):ℝ):ℂ) + ((0.1745306218369:ℝ):ℂ) * I)‖ ≤ 0.0000001251 := by
  have hl := lg_47
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.582504154910548693 53.582504189703104361 2.9661636 0.00000002509 (-0.9846517463977) 0.1745306218369 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_48 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8922785123722):ℝ):ℂ) + ((0.4514853887457:ℝ):ℂ) * I)‖ ≤ 0.00000012091 := by
  have hl := lg_48
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.875504450716818388 53.875504485509332305 2.6731633 0.0000000209 (-0.8922785123722) 0.4514853887457 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_49 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7280056281805):ℝ):ℂ) + ((0.6855711526228:ℝ):ℂ) * I)‖ ≤ 0.00000013757 := by
  have hl := lg_49
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.162463074334935948 54.162463102168991616 2.3862047 0.00000003756 (-0.7280056281805) 0.6855711526228 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p917_50 : ‖exp (-((((((13917:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5091933478042):ℝ):ℂ) + ((0.8606521565332:ℝ):ℂ) * I)‖ ≤ 0.00000011865 := by
  have hl := lg_50
  refine (ecis_approx ((((13917:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.443624148455193306 54.44362418324772114 2.1050436 0.00000001864 (-0.5091933478042) 0.8606521565332 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_2 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.968870261396):ℝ):ℂ) + ((0.2475690132383:ℝ):ℂ) * I)‖ ≤ 0.00000013526 := by
  have hl := lg_2
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.6749483426274 9.6749483496064 2.8914223 0.00000003525 (-0.968870261396) 0.2475690132383 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_3 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9310439591344):ℝ):ℂ) + (((-0.3649070374736):ℝ):ℂ) * I)‖ ≤ 0.00000011424 := by
  have hl := lg_3
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.334430321601153112 15.33443032858016707 (-2.7680597) 0.00000001423 (-0.9310439591344) (-0.3649070374736) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_4 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8774191227067:ℝ):ℂ) + (((-0.4797245908942):ℝ):ℂ) * I)‖ ≤ 0.0000001363 := by
  have hl := lg_4
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.3498966852548 19.3498966992128 (-0.5003408) 0.00000003629 0.8774191227067 (-0.4797245908942) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_5 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8900297739735):ℝ):ℂ) + ((0.4559024033003:ℝ):ℂ) * I)‖ ≤ 0.00000015423 := by
  have hl := lg_5
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.464534374498529222 22.46453438845654318 2.6682068 0.00000005422 (-0.8900297739735) 0.4559024033003 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_6 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9924004794668:ℝ):ℂ) + ((0.1230499425195:ℝ):ℂ) * I)‖ ≤ 0.00000014948 := by
  have hl := lg_6
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.009378664228553112 25.00937867818656707 0.1233626 0.00000004947 0.9924004794668 0.1230499425195 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_7 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4416853038727):ℝ):ℂ) + (((-0.897170046501):ℝ):ℂ) * I)‖ ≤ 0.00000013851 := by
  have hl := lg_7
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.161013853257420276 27.161013867215448192 (-2.0282726) 0.0000000385 (-0.4416853038727) (-0.897170046501) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_8 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7313403511982):ℝ):ℂ) + ((0.6820126763336:ℝ):ℂ) * I)‖ ≤ 0.00000011294 := by
  have hl := lg_8
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.0248450278822 29.0248450488192 2.3910815 0.00000001293 (-0.7313403511982) 0.6820126763336 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_9 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7336857127584:ℝ):ℂ) + ((0.6794889807011:ℝ):ℂ) * I)‖ ≤ 0.00000012128 := by
  have hl := lg_9
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.668860643202306224 30.66886065716033414 0.7470659 0.00000002127 0.7336857127584 0.6794889807011 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_10 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7494560764404:ℝ):ℂ) + (((-0.6620540684012):ℝ):ℂ) * I)‖ ≤ 0.00000011879 := by
  have hl := lg_10
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.139482717125929222 32.13948273806294318 (-0.7235562) 0.00000001878 0.7494560764404 (-0.6620540684012) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_11 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4645260814868):ℝ):ℂ) + (((-0.8855594387807):ℝ):ℂ) * I)‖ ≤ 0.00000012908 := by
  have hl := lg_11
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.469822206834683614 33.46982222777171153 (-2.0538957) 0.00000002907 (-0.4645260814868) (-0.8855594387807) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_12 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9919706520806):ℝ):ℂ) + ((0.126468276578:ℝ):ℂ) * I)‖ ≤ 0.00000013624 := by
  have hl := lg_12
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.684327006855953112 34.68432702779296707 3.0147848 0.00000003623 (-0.9919706520806) 0.126468276578 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_13 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3209689324795):ℝ):ℂ) + ((0.9470897235115:ℝ):ℂ) * I)‖ ≤ 0.00000012253 := by
  have hl := lg_13
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.8015631205631686 35.801563141500196516 1.8975487 0.00000002252 (-0.3209689324795) 0.9470897235115 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_14 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6500473350936:ℝ):ℂ) + ((0.7598937176591:ℝ):ℂ) * I)‖ ≤ 0.00000014721 := by
  have hl := lg_14
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.835962195884820276 36.835962216821848192 0.8631496 0.0000000472 0.6500473350936 0.7598937176591 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_15 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9950188400084:ℝ):ℂ) + (((-0.0996870504545):ℝ):ℂ) * I)‖ ≤ 0.00000014699 := by
  have hl := lg_15
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.798964696099682334 37.79896471703671025 (-0.0998529) 0.00000004698 0.9950188400084 (-0.0996870504545) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_16 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5397287179668:ℝ):ℂ) + (((-0.8418390053935):ℝ):ℂ) * I)‖ ≤ 0.00000015536 := by
  have hl := lg_16
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.6997933705096 38.6997933984256 (-1.0006815) 0.00000005535 0.5397287179668 (-0.8418390053935) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_17 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2725897317055):ℝ):ℂ) + (((-0.9621303644347):ℝ):ℂ) * I)‖ ≤ 0.00000012668 := by
  have hl := lg_17
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.545991841823385772 39.54599186973939973 (-1.84688) 0.00000002667 (-0.2725897317055) (-0.9621303644347) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_18 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8790667291498):ℝ):ℂ) + (((-0.4766987367367):ℝ):ℂ) * I)‖ ≤ 0.00000015726 := by
  have hl := lg_18
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.343808985829706224 40.34380900676673414 (-2.6446972) 0.00000005725 (-0.8790667291498) (-0.4766987367367) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_19 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9669596524924):ℝ):ℂ) + ((0.2549294612106:ℝ):ℂ) * I)‖ ≤ 0.00000013102 := by
  have hl := lg_19
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.098479260320204674 41.098479281257246548 2.8838179 0.00000003101 (-0.9669596524924) 0.2549294612106 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_20 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5622216322487):ℝ):ℂ) + ((0.8269865997839:ℝ):ℂ) * I)‖ ≤ 0.00000013743 := by
  have hl := lg_20
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.814431059753329222 41.81443108766934318 2.1678661 0.00000003742 (-0.5622216322487) 0.8269865997839 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_21 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0838447773308:ℝ):ℂ) + ((0.9964788273286:ℝ):ℂ) * I)‖ ≤ 0.00000014555 := by
  have hl := lg_21
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.495444174858573388 42.495444195795615262 1.486853 0.00000004554 0.0838447773308 0.9964788273286 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_22 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6693025825862:ℝ):ℂ) + ((0.7429899413475:ℝ):ℂ) * I)‖ ≤ 0.00000012714 := by
  have hl := lg_22
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.144770549462083614 43.14477057737811153 0.8375266 0.00000002713 0.6693025825862 0.7429899413475 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_23 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.976532909129:ℝ):ℂ) + ((0.2153682367204:ℝ):ℂ) * I)‖ ≤ 0.0000001291 := by
  have hl := lg_23
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.765228251425770628 43.765228279341812502 0.2170689 0.00000002909 0.976532909129 0.2153682367204 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_24 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9297812414022:ℝ):ℂ) + (((-0.3681125414008):ℝ):ℂ) * I)‖ ≤ 0.00000012716 := by
  have hl := lg_24
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.359275349483353112 44.35927537739936707 (-0.3769782) 0.00000002715 0.9297812414022 (-0.3681125414008) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_25 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5843060842052:ℝ):ℂ) + (((-0.8115333634305):ℝ):ℂ) * I)‖ ≤ 0.00000012667 := by
  have hl := lg_25
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.929068748997058444 44.92906877691308636 (-0.9467716) 0.00000002666 0.5843060842052 (-0.8115333634305) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_26 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0765071922771:ℝ):ℂ) + (((-0.9970690294708):ℝ):ℂ) * I)‖ ≤ 0.00000014086 := by
  have hl := lg_26
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.4765114631905686 45.476511491106596516 (-1.4942143) 0.00000004085 0.0765071922771 (-0.9970690294708) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_27 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4351433398046):ℝ):ℂ) + (((-0.900361190756):ℝ):ℂ) * I)‖ ≤ 0.0000001355 := by
  have hl := lg_27
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.003290964803459336 46.00329098574050121 (-2.0209938) 0.00000003549 (-0.4351433398046) (-0.900361190756) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_28 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8179376653453):ℝ):ℂ) + (((-0.5753068533858):ℝ):ℂ) * I)‖ ≤ 0.00000011619 := by
  have hl := lg_28
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.510910538512220276 46.510910566428248192 (-2.5286134) 0.00000001618 (-0.8179376653453) (-0.5753068533858) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_29 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.99242358854):ℝ):ℂ) + (((-0.1228634220319):ℝ):ℂ) * I)‖ ≤ 0.00000015811 := by
  have hl := lg_29
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.000715180437926936 47.00071520835396881 (-3.018418) 0.0000000581 (-0.99242358854) (-0.1228634220319) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_30 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9393647389278):ℝ):ℂ) + ((0.3429196510571:ℝ):ℂ) * I)‖ ≤ 0.00000011872 := by
  have hl := lg_30
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.473913038727082334 47.47391306664311025 2.7915694 0.00000001871 (-0.9393647389278) 0.3429196510571 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_31 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.691159900077):ℝ):ℂ) + ((0.7227018697245:ℝ):ℂ) * I)‖ ≤ 0.00000015618 := by
  have hl := lg_31
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.931593385690376754 47.931593413606418628 2.3338891 0.00000005617 (-0.691159900077) 0.7227018697245 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_32 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3145137572057):ℝ):ℂ) + ((0.9492529149423:ℝ):ℂ) * I)‖ ≤ 0.00000014431 := by
  have hl := lg_32
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.374741713137 48.374741748032 1.8907407 0.0000000443 (-0.3145137572057) 0.9492529149423 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_33 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1093473378012:ℝ):ℂ) + ((0.9940036014601:ℝ):ℂ) * I)‖ ≤ 0.00000012902 := by
  have hl := lg_33
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.804252528435836726 48.8042525563518786 1.4612299 0.00000002901 0.1093473378012 0.9940036014601 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_34 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5022977496989:ℝ):ℂ) + ((0.864694726853:ℝ):ℂ) * I)‖ ≤ 0.00000016192 := by
  have hl := lg_34
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.220940184450785772 49.22094021934579973 1.0445423 0.00000006191 0.5022977496989 0.864694726853 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_35 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8021350516079:ℝ):ℂ) + ((0.5971426621687:ℝ):ℂ) * I)‖ ≤ 0.0000001297 := by
  have hl := lg_35
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.625548227755949498 49.625548255671991372 0.6399342 0.00000002969 0.8021350516079 0.5971426621687 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_36 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9697174477148:ℝ):ℂ) + ((0.2442295469377:ℝ):ℂ) * I)‖ ≤ 0.00000012899 := by
  have hl := lg_36
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.018757328457106224 50.01875735637313414 0.2467251 0.00000002898 0.9697174477148 0.2442295469377 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_37 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9908055493938:ℝ):ℂ) + (((-0.1352936188088):ℝ):ℂ) * I)‖ ≤ 0.00000014728 := by
  have hl := lg_37
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.401192210174801436 50.40119223809084331 (-0.1357098) 0.00000004727 0.9908055493938 (-0.1352936188088) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_38 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8737457710952:ℝ):ℂ) + (((-0.4863829021392):ℝ):ℂ) * I)‖ ≤ 0.0000001545 := by
  have hl := lg_38
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.773427602947604674 50.773427630863646548 (-0.5079452) 0.00000005449 0.8737457710952 (-0.4863829021392) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_39 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6444358909813:ℝ):ℂ) + (((-0.7646583435856):ℝ):ℂ) * I)‖ ≤ 0.00000011529 := by
  have hl := lg_39
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.135993442164321712 51.135993470080363586 (-0.870511) 0.00000001528 0.6444358909813 (-0.7646583435856) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_40 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.339983475984:ℝ):ℂ) + (((-0.9404314095445):ℝ):ℂ) * I)‖ ≤ 0.00000015507 := by
  have hl := lg_40
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.489379402380729222 51.48937943727574318 (-1.223897) 0.00000005506 0.339983475984 (-0.9404314095445) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_41 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0022399249218:ℝ):ℂ) + (((-0.9999974913649):ℝ):ℂ) * I)‖ ≤ 0.00000016639 := by
  have hl := lg_41
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.83403888891712764 51.834038923812155556 (-1.5685564) 0.00000006638 0.0022399249218 (-0.9999974913649) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_42 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3279320791545):ℝ):ℂ) + (((-0.9447013027721):ℝ):ℂ) * I)‖ ≤ 0.00000013997 := by
  have hl := lg_42
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.170392517485973388 52.170392545402015262 (-1.9049101) 0.00000003996 (-0.3279320791545) (-0.9447013027721) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_43 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6151312865222):ℝ):ℂ) + (((-0.7884246954074):ℝ):ℂ) * I)‖ ≤ 0.00000015711 := by
  have hl := lg_43
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.49883120033746124 52.498831228253517072 (-2.2333488) 0.0000000571 (-0.6151312865222) (-0.7884246954074) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_44 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8324087063607):ℝ):ℂ) + (((-0.5541622014457):ℝ):ℂ) * I)‖ ≤ 0.00000016536 := by
  have hl := lg_44
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.819718892089483614 52.81971892698451153 (-2.5542365) 0.00000006535 (-0.8324087063607) (-0.5541622014457) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_45 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9627827864408):ℝ):ℂ) + (((-0.270276350964):ℝ):ℂ) * I)‖ ≤ 0.00000013975 := by
  have hl := lg_45
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.133395017700835446 53.13339504561687732 (-2.8679126) 0.00000003974 (-0.9627827864408) (-0.270276350964) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_46 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9994521966113):ℝ):ℂ) + ((0.0330954087336:ℝ):ℂ) * I)‖ ≤ 0.00000016435 := by
  have hl := lg_46
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.440176594053170628 53.440176628948212502 3.1084912 0.00000006434 (-0.9994521966113) 0.0330954087336 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_47 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9449727093081):ℝ):ℂ) + ((0.3271491685336:ℝ):ℂ) * I)‖ ≤ 0.0000001581 := by
  have hl := lg_47
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.740360206527372182 53.740360241422428014 2.8083075 0.00000005809 (-0.9449727093081) 0.3271491685336 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_48 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8097041357983):ℝ):ℂ) + ((0.5868383188052:ℝ):ℂ) * I)‖ ≤ 0.0000001624 := by
  have hl := lg_48
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.034223692110753112 54.03422372700576707 2.5144441 0.00000006239 (-0.8097041357983) 0.5868383188052 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_49 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6098280997413):ℝ):ℂ) + ((0.7925337145845:ℝ):ℂ) * I)‖ ≤ 0.00000015812 := by
  have hl := lg_49
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.322027706514840552 54.322027734430896384 2.22664 0.00000005811 (-0.6098280997413) 0.7925337145845 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p958_50 : ‖exp (-((((((13958:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3652062744957):ℝ):ℂ) + ((0.9309266228153:ℝ):ℂ) * I)‖ ≤ 0.00000016192 := by
  have hl := lg_50
  refine (ecis_approx ((((13958:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.604017091624458444 54.60401712651948636 1.9446507 0.00000006191 (-0.3652062744957) 0.9309266228153 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_2 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9635131176875):ℝ):ℂ) + ((0.2676611137214:ℝ):ℂ) * I)‖ ≤ 0.00000015069 := by
  have hl := lg_2
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.6957427580364 9.6957427650304 2.8706279 0.00000005068 (-0.9635131176875) 0.2676611137214 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_3 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9425629036618):ℝ):ℂ) + (((-0.3340287000476):ℝ):ℂ) * I)‖ ≤ 0.00000012412 := by
  have hl := lg_3
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.367388690253398032 15.36738869724741202 (-2.8010181) 0.00000002411 (-0.9425629036618) (-0.3340287000476) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_4 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.856715008393:ℝ):ℂ) + (((-0.5157900681422):ℝ):ℂ) * I)‖ ≤ 0.00000010854 := by
  have hl := lg_4
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.3914855160728 19.3914855300608 (-0.5419296) 0.00000000853 0.856715008393 (-0.5157900681422) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_5 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8669887015364):ℝ):ℂ) + ((0.4983277950533:ℝ):ℂ) * I)‖ ≤ 0.00000011688 := by
  have hl := lg_5
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.512817511855955492 22.51281752584396948 2.6199237 0.00000001687 (-0.8669887015364) 0.4983277950533 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_6 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.99757821601:ℝ):ℂ) + ((0.0695535976225:ℝ):ℂ) * I)‖ ≤ 0.00000013357 := by
  have hl := lg_6
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.063131448289798032 25.06313146227781202 0.0696098 0.00000003356 0.99757821601 0.0695535976225 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_7 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4932775280668):ℝ):ℂ) + (((-0.869871990754):ℝ):ℂ) * I)‖ ≤ 0.000000143 := by
  have hl := lg_7
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.219391157713482936 27.219391171701510912 (-2.0866499) 0.00000004299 (-0.4932775280668) (-0.869871990754) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_8 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6873992046331):ℝ):ℂ) + ((0.7262797900589:ℝ):ℂ) * I)‖ ≤ 0.00000015921 := by
  have hl := lg_8
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.0872282741092 29.0872282950912 2.3286983 0.0000000592 (-0.6873992046331) 0.7262797900589 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_9 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7768496594806:ℝ):ℂ) + ((0.6296861174942:ℝ):ℂ) * I)‖ ≤ 0.00000015541 := by
  have hl := lg_9
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.734777380506796064 30.73477739449482404 0.6811491 0.0000000554 0.7768496594806 0.6296861174942 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_10 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7019720193351:ℝ):ℂ) + (((-0.7122045240453):ℝ):ℂ) * I)‖ ≤ 0.00000015499 := by
  have hl := lg_10
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.208560269892355492 32.20856029087436948 (-0.7926337) 0.00000005498 0.7019720193351 (-0.7122045240453) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_11 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5269740434812):ℝ):ℂ) + (((-0.8498813784815):ℝ):ℂ) * I)‖ ≤ 0.00000015009 := by
  have hl := lg_11
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.541759064995239604 33.54175908597726758 (-2.1258325) 0.00000005008 (-0.5269740434812) (-0.8498813784815) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_12 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9797964704171):ℝ):ℂ) + ((0.1999971905679:ℝ):ℂ) * I)‖ ≤ 0.00000013677 := by
  have hl := lg_12
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.758874206326198032 34.75887422730821202 2.9402376 0.00000003676 (-0.9797964704171) 0.1999971905679 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_13 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2472139248098):ℝ):ℂ) + ((0.9689609256203:ℝ):ℂ) * I)‖ ≤ 0.00000014183 := by
  have hl := lg_13
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.8785116012636196 35.878511622245647576 1.8206002 0.00000004182 (-0.2472139248098) 0.9689609256203 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_14 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7081103455589:ℝ):ℂ) + ((0.7061017904753:ℝ):ℂ) * I)‖ ≤ 0.00000012734 := by
  have hl := lg_14
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.915133915749882936 36.915133936731910912 0.7839779 0.00000002733 0.7081103455589 0.7061017904753 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_15 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9836471736818:ℝ):ℂ) + (((-0.1801061845354):ℝ):ℂ) * I)‖ ≤ 0.00000014098 := by
  have hl := lg_15
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.880206202109353524 37.8802062230913815 (-0.1810944) 0.00000004097 0.9836471736818 (-0.1801061845354) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
