/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Base
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
namespace H22

open Complex Set

lemma cs_b1left_v13p515_2 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9983819809659):ℝ):ℂ) + (((-0.0568631649144):ℝ):ℂ) * I)‖ ≤ 0.00000014135 := by
  have hl := lg_2
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.3678841417545 9.367884148512 (-3.0846988) 0.00000004134 (-0.9983819809659) (-0.0568631649144) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_3 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6522721265629):ℝ):ℂ) + (((-0.757984876427):ℝ):ℂ) * I)‖ ≤ 0.00000013654 := by
  have hl := lg_3
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.84774507783633646 14.847745084593849975 (-2.2813745) 0.00000003653 (-0.6522721265629) (-0.757984876427) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_4 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9935331730629:ℝ):ℂ) + ((0.1135422125184:ℝ):ℂ) * I)‖ ≤ 0.00000013804 := by
  have hl := lg_4
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.735768283509 18.735768297024 0.1137876 0.00000003803 0.9935331730629 0.1135422125184 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_5 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.971434128194):ℝ):ℂ) + (((-0.2373093641259):ℝ):ℂ) * I)‖ ≤ 0.00000014203 := by
  have hl := lg_5
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.751553379520534635 21.75155339303554815 (-2.9019975) 0.00000004202 (-0.971434128194) (-0.2373093641259) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_6 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.608115324495:ℝ):ℂ) + ((0.7938486959832:ℝ):ℂ) * I)‖ ≤ 0.00000010914 := by
  have hl := lg_6
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.21562921959083646 24.215629233105849975 0.917112 0.00000000913 0.608115324495 0.7938486959832 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_7 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.393616088443:ℝ):ℂ) + (((-0.9192749180299):ℝ):ℂ) * I)‖ ≤ 0.00000014227 := by
  have hl := lg_7
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.29897565745622833 26.29897567097125536 (-1.1662344) 0.00000004226 0.393616088443 (-0.9192749180299) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_8 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.985469248003):ℝ):ℂ) + (((-0.1698539398326):ℝ):ℂ) * I)‖ ≤ 0.00000011683 := by
  have hl := lg_8
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.1036524252635 28.103652445536 (-2.9709112) 0.00000001682 (-0.985469248003) (-0.1698539398326) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_9 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1490822375967):ℝ):ℂ) + ((0.9888248006763:ℝ):ℂ) * I)‖ ≤ 0.0000001333 := by
  have hl := lg_9
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.69549015567267292 29.69549016918769995 1.7204364 0.00000003329 (-0.1490822375967) 0.9888248006763 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_10 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9563681701713:ℝ):ℂ) + ((0.2921642056845:ℝ):ℂ) * I)‖ ≤ 0.00000011464 := by
  have hl := lg_10
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.119437521275034635 31.11943754154754815 0.296489 0.00000001463 0.9563681701713 0.2921642056845 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_11 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5473280000786:ℝ):ℂ) + (((-0.8369181921371):ℝ):ℂ) * I)‖ ≤ 0.00000013458 := by
  have hl := lg_11
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.407554601330473495 32.407554621603000525 (-0.9916281) 0.00000003457 0.5473280000786 (-0.8369181921371) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_12 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5619906329654):ℝ):ℂ) + (((-0.8271435960278):ℝ):ℂ) * I)‖ ≤ 0.00000014573 := by
  have hl := lg_12
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.58351336134533646 33.583513381617849975 (-2.1675868) 0.00000004572 (-0.5619906329654) (-0.8271435960278) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_13 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9941982861397):ℝ):ℂ) + ((0.107562853136:ℝ):ℂ) * I)‖ ≤ 0.00000013276 := by
  have hl := lg_13
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.6652905555531755 34.66529057582570253 3.0338213 0.00000003275 (-0.9941982861397) 0.107562853136 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_14 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4452519957564):ℝ):ℂ) + ((0.895405305027:ℝ):ℂ) * I)‖ ≤ 0.00000014388 := by
  have hl := lg_14
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.66685979921072833 35.66685981948325536 2.032252 0.00000004387 (-0.4452519957564) 0.895405305027 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_15 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.453762412821:ℝ):ℂ) + ((0.8911227035099:ℝ):ℂ) * I)‖ ≤ 0.00000013457 := by
  have hl := lg_15
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.599298457356871095 36.599298477629398125 1.0998134 0.00000003456 0.453762412821 0.8911227035099 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_16 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9742163093913:ℝ):ℂ) + ((0.2256160067815:ℝ):ℂ) * I)‖ ≤ 0.00000015099 := by
  have hl := lg_16
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.471536567018 37.471536594048 0.2275753 0.00000005098 0.9742163093913 0.2256160067815 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_17 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8299565713802:ℝ):ℂ) + (((-0.5578280107908):ℝ):ℂ) * I)‖ ≤ 0.00000011483 := by
  have hl := lg_17
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.29087833086710551 38.290878357897119025 (-0.5917665) 0.00000001482 0.8299565713802 (-0.5578280107908) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_18 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2050686298293:ℝ):ℂ) + (((-0.9787475961962):ℝ):ℂ) * I)‖ ≤ 0.00000014567 := by
  have hl := lg_18
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.06337429742717292 39.06337431769969995 (-1.3642625) 0.00000004566 0.2050686298293 (-0.9787475961962) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_19 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5005073163633):ℝ):ℂ) + (((-0.8657323063514):ℝ):ℂ) * I)‖ ≤ 0.0000001502 := by
  have hl := lg_19
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.794092792894939545 39.79409281316748009 (-2.094981) 0.00000005019 (-0.5005073163633) (-0.8657323063514) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_20 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9382073669774):ℝ):ℂ) + (((-0.3460735996485):ℝ):ℂ) * I)‖ ≤ 0.000000147 := by
  have hl := lg_20
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.487321663029534635 40.48732169005954815 (-2.7882098) 0.00000004699 (-0.9382073669774) (-0.3460735996485) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_21 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9535412859731):ℝ):ℂ) + ((0.3012623702549:ℝ):ℂ) * I)‖ ≤ 0.00000011498 := by
  have hl := lg_21
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.14672073529256479 41.146720755565105335 2.8355764 0.00000001497 (-0.9535412859731) 0.3012623702549 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_22 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5940322247193):ℝ):ℂ) + ((0.8044412445813:ℝ):ℂ) * I)‖ ≤ 0.00000011987 := by
  have hl := lg_22
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.775438743084973495 41.775438770115000525 2.2068584 0.00000001986 (-0.5940322247193) 0.8044412445813 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_23 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.035289144696):ℝ):ℂ) + ((0.9993771441585:ℝ):ℂ) * I)‖ ≤ 0.00000013604 := by
  have hl := lg_23
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.37620431422978149 42.376204341259822035 1.6060928 0.00000003603 (-0.035289144696) 0.9993771441585 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_24 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.514047410587:ℝ):ℂ) + ((0.8577617732616:ℝ):ℂ) * I)‖ ≤ 0.00000014717 := by
  have hl := lg_24
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.95139750309983646 42.951397530129849975 1.0308996 0.00000004716 0.514047410587 0.8577617732616 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_25 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8873684884676:ℝ):ℂ) + ((0.4610609131934:ℝ):ℂ) * I)‖ ≤ 0.00000013583 := by
  have hl := lg_25
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.50310675904106927 43.5031067860710963 0.4791904 0.00000003582 0.8873684884676 0.4610609131934 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_26 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9987060140721:ℝ):ℂ) + (((-0.0508556531402):ℝ):ℂ) * I)‖ ≤ 0.00000015296 := by
  have hl := lg_26
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.0331746973076755 44.03317472433770253 (-0.0508776) 0.00000005295 0.9987060140721 (-0.0508556531402) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_27 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8467564325086:ℝ):ℂ) + (((-0.5319807740936):ℝ):ℂ) * I)‖ ≤ 0.00000011676 := by
  have hl := lg_27
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.54323523350900938 44.543235253781549925 (-0.5609381) 0.00000001675 0.8467564325086 (-0.5319807740936) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_28 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4954471494251:ℝ):ℂ) + (((-0.8686380846627):ℝ):ℂ) * I)‖ ≤ 0.00000011775 := by
  have hl := lg_28
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.03474394096522833 45.03474396799525536 (-1.0524468) 0.00000001774 0.4954471494251 (-0.8686380846627) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_29 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.044076043234:ℝ):ℂ) + (((-0.9990281789883):ℝ):ℂ) * I)‖ ≤ 0.00000012206 := by
  have hl := lg_29
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.50900312821454238 45.509003155244582925 (-1.526706) 0.00000002205 0.044076043234 (-0.9990281789883) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p515_30 : ‖exp (-((((((13515:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4023562507915):ℝ):ℂ) + (((-0.9154831770413):ℝ):ℂ) * I)‖ ≤ 0.00000015116 := by
  have hl := lg_30
  refine (ecis_approx ((((13515:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.967182599111371095 45.967182626141398125 (-1.9848855) 0.00000005115 (-0.4023562507915) (-0.9154831770413) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_2 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.99993123036):ℝ):ℂ) + ((0.0117274844578:ℝ):ℂ) * I)‖ ≤ 0.00000010507 := by
  have hl := lg_2
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.4365057126042 9.4365057194112 3.1298649 0.00000000506 (-0.99993123036) 0.0117274844578 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_3 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7306959323843):ℝ):ℂ) + (((-0.6827030499181):ℝ):ℂ) * I)‖ ≤ 0.00000011999 := by
  have hl := lg_3
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.956507694388744696 14.95650770119575831 (-2.3901371) 0.00000001998 (-0.7306959323843) (-0.6827030499181) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_4 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997249323712:ℝ):ℂ) + (((-0.0234533493443):ℝ):ℂ) * I)‖ ≤ 0.0000001173 := by
  have hl := lg_4
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.8730114252084 18.8730114388224 (-0.0234555) 0.00000001729 0.9997249323712 (-0.0234533493443) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_5 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9967808261168):ℝ):ℂ) + (((-0.0801747103123):ℝ):ℂ) * I)‖ ≤ 0.00000012489 := by
  have hl := lg_5
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.910887732800041326 21.91088774641405494 (-3.0613318) 0.00000002488 (-0.9967808261168) (-0.0801747103123) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_6 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7386520725393:ℝ):ℂ) + ((0.674086875509:ℝ):ℂ) * I)‖ ≤ 0.00000012174 := by
  have hl := lg_6
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.393013406992944696 24.39301342060695831 0.7397278 0.00000002173 0.7386520725393 0.674086875509 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_7 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2103342315975:ℝ):ℂ) + (((-0.9776295366949):ℝ):ℂ) * I)‖ ≤ 0.00000014707 := by
  have hl := lg_7
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.491620762161235108 26.491620775775262336 (-1.3588795) 0.00000004706 0.2103342315975 (-0.9776295366949) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_8 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993811328836):ℝ):ℂ) + ((0.0351759951:ℝ):ℂ) * I)‖ ≤ 0.00000012235 := by
  have hl := lg_8
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.3095171378126 28.3095171582336 3.1064094 0.00000002234 (-0.9993811328836) 0.0351759951 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_9 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0678330983824:ℝ):ℂ) + ((0.9976966827467:ℝ):ℂ) * I)‖ ≤ 0.00000014714 := by
  have hl := lg_9
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.913015388777489392 29.91301540239151662 1.5029111 0.00000004713 0.0678330983824 0.9976966827467 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_10 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9976525261165:ℝ):ℂ) + ((0.0684794650487:ℝ):ℂ) * I)‖ ≤ 0.00000012994 := by
  have hl := lg_10
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.347393445404241326 31.34739346582525494 0.0685331 0.00000002993 0.9976525261165 0.0684794650487 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_11 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3351614881498:ℝ):ℂ) + (((-0.9421606958801):ℝ):ℂ) * I)‖ ≤ 0.0000001178 := by
  have hl := lg_11
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.644946233260308262 32.64494625368133549 (-1.2290197) 0.00000001779 0.3351614881498 (-0.9421606958801) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_12 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7465066147145):ℝ):ℂ) + (((-0.6653779934402):ℝ):ℂ) * I)‖ ≤ 0.00000011632 := by
  have hl := lg_12
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.829519119597144696 33.82951914001815831 (-2.4135926) 0.00000001631 (-0.7465066147145) (-0.6653779934402) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_13 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9352961263538):ℝ):ℂ) + ((0.3538660139912:ℝ):ℂ) * I)‖ ≤ 0.00000011922 := by
  have hl := lg_13
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.9192205418646638 34.919220562285691028 2.7798913 0.00000001921 (-0.9352961263538) 0.3538660139912 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_14 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1988546315721):ℝ):ℂ) + ((0.9800289972758:ℝ):ℂ) * I)‖ ≤ 0.00000015212 := by
  have hl := lg_14
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.928126474765435108 35.928126495186462336 1.7709854 0.00000005211 (-0.1988546315721) 0.9800289972758 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_15 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6736081811863:ℝ):ℂ) + ((0.7390886403125:ℝ):ℂ) * I)‖ ≤ 0.0000001159 := by
  have hl := lg_15
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.867395427188786022 36.86739544760981325 0.8317164 0.00000001589 0.6736081811863 0.7390886403125 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_16 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9988998808091:ℝ):ℂ) + (((-0.0468937961742):ℝ):ℂ) * I)‖ ≤ 0.00000013458 := by
  have hl := lg_16
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.7460228504168 37.7460228776448 (-0.046911) 0.00000003457 0.9988998808091 (-0.0468937961742) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_17 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6431016537813:ℝ):ℂ) + (((-0.7657808191015):ℝ):ℂ) * I)‖ ≤ 0.00000013599 := by
  have hl := lg_17
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.571366451825732476 38.57136647905374609 (-0.8722546) 0.00000003598 0.6431016537813 (-0.7657808191015) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_18 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0795288990241):ℝ):ℂ) + (((-0.9968325607742):ℝ):ℂ) * I)‖ ≤ 0.00000014171 := by
  have hl := lg_18
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.349521101381689392 39.34952112180271662 (-1.6504093) 0.0000000417 (-0.0795288990241) (-0.9968325607742) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_19 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7281946124769):ℝ):ℂ) + (((-0.6853704154184):ℝ):ℂ) * I)‖ ≤ 0.00000012911 := by
  have hl := lg_19
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.085592251755213242 40.085592272176254084 (-2.3864804) 0.0000000291 (-0.7281946124769) (-0.6853704154184) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_20 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9983870094461):ℝ):ℂ) + (((-0.0567748078865):ℝ):ℂ) * I)‖ ≤ 0.00000014217 := by
  have hl := lg_20
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.783899158008441326 40.78389918523645494 (-3.0847873) 0.00000004216 (-0.9983870094461) (-0.0567748078865) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_21 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8211210297677):ℝ):ℂ) + ((0.5707541102918:ℝ):ℂ) * I)‖ ≤ 0.00000012673 := by
  have hl := lg_21
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.448128456549979804 41.448128476971020646 2.5341687 0.00000002672 (-0.8211210297677) 0.5707541102918 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_22 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3240892641295):ℝ):ℂ) + ((0.9460265053761:ℝ):ℂ) * I)‖ ≤ 0.00000012285 := by
  have hl := lg_22
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.081451945864508262 42.08145197309253549 1.9008452 0.00000002284 (-0.3240892641295) 0.9460265053761 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_23 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2716599495899:ℝ):ℂ) + ((0.9623933041064:ℝ):ℂ) * I)‖ ≤ 0.00000011849 := by
  have hl := lg_23
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.686618241503828724 42.686618268731869566 1.2956789 0.00000001848 0.2716599495899 0.9623933041064 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_24 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7542584882448:ℝ):ℂ) + ((0.6565775909294:ℝ):ℂ) * I)‖ ≤ 0.00000011807 := by
  have hl := lg_24
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.266024832201344696 43.26602485942935831 0.7162723 0.00000001806 0.7542584882448 0.6565775909294 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_25 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9871440327237:ℝ):ℂ) + ((0.1598332213837:ℝ):ℂ) * I)‖ ≤ 0.00000014259 := by
  have hl := lg_25
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.821775465600082652 43.82177549282810988 0.1605217 0.00000004258 0.9871440327237 0.1598332213837 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_26 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9310818510725:ℝ):ℂ) + (((-0.3648103433338):ℝ):ℂ) * I)‖ ≤ 0.00000013145 := by
  have hl := lg_26
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.3557262544688638 44.355726281696891028 (-0.3734291) 0.00000003144 0.9310818510725 (-0.3648103433338) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_27 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6315652766839:ℝ):ℂ) + (((-0.7753227078367):ℝ):ℂ) * I)‖ ≤ 0.00000015335 := by
  have hl := lg_27
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.869523083166234088 44.86952310358727493 (-0.8872259) 0.00000005334 0.6315652766839 (-0.7753227078367) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_28 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1873475901763:ℝ):ℂ) + (((-0.9822936834038):ℝ):ℂ) * I)‖ ≤ 0.0000001629 := by
  have hl := lg_28
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.364632187369635108 45.364632214597662336 (-1.3823351) 0.00000006289 0.1873475901763 (-0.9822936834038) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_29 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2852545221685):ℝ):ℂ) + (((-0.9584518024298):ℝ):ℂ) * I)‖ ≤ 0.00000013499 := by
  have hl := lg_29
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.842365415280264888 45.84236544250830573 (-1.8600683) 0.00000003498 (-0.2852545221685) (-0.9584518024298) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p614_30 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6822295031216):ℝ):ℂ) + (((-0.7311380889063):ℝ):ℂ) * I)‖ ≤ 0.00000011678 := by
  have hl := lg_30
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.303901139792986022 46.30390116702101325 (-2.321604) 0.00000001677 (-0.6822295031216) (-0.7311380889063) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_2 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9980148555004):ℝ):ℂ) + ((0.0629789461207:ℝ):ℂ) * I)‖ ≤ 0.00000011043 := by
  have hl := lg_2
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.4877986039464 9.4877986107904 3.078572 0.00000001042 (-0.9980148555004) 0.0629789461207 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_3 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7837233827961):ℝ):ℂ) + (((-0.621110021828):ℝ):ℂ) * I)‖ ≤ 0.00000011064 := by
  have hl := lg_3
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.037805003730948832 15.03780501057496252 (-2.4714344) 0.00000001063 (-0.7837233827961) (-0.621110021828) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_4 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9920673055302:ℝ):ℂ) + (((-0.1257078410366):ℝ):ℂ) * I)‖ ≤ 0.00000011366 := by
  have hl := lg_4
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.9755972078928 18.9755972215808 (-0.1260413) 0.00000001365 0.9920673055302 (-0.1257078410366) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_5 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.99924591672):ℝ):ℂ) + ((0.0388277905816:ℝ):ℂ) * I)‖ ≤ 0.00000012327 := by
  have hl := lg_5
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.029986138281692792 22.02998615196970648 3.1027551 0.00000002326 (-0.99924591672) 0.0388277905816 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_6 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8212844336015:ℝ):ℂ) + ((0.5705189559725:ℝ):ℂ) * I)‖ ≤ 0.00000012106 := by
  have hl := lg_6
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.525603607677348832 24.52560362136536252 0.6071376 0.00000002105 0.8212844336015 0.5705189559725 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_7 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0678672195693:ℝ):ℂ) + (((-0.9976943622712):ℝ):ℂ) * I)‖ ≤ 0.00000011558 := by
  have hl := lg_7
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.635618113152856336 26.635618126840883712 (-1.5028769) 0.00000001557 0.0678672195693 (-0.9976943622712) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_8 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9821809613112):ℝ):ℂ) + ((0.1879376463058:ℝ):ℂ) * I)‖ ≤ 0.00000012407 := by
  have hl := lg_8
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.4633958118392 28.4633958323712 2.9525307 0.00000002406 (-0.9821809613112) 0.1879376463058 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_9 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2284446884988:ℝ):ℂ) + ((0.9735568931997:ℝ):ℂ) * I)‖ ≤ 0.00000012845 := by
  have hl := lg_9
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.075610007461897664 30.07561002114992504 1.3403165 0.00000002844 0.2284446884988 0.9735568931997 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_10 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9948169371019:ℝ):ℂ) + (((-0.101682159965):ℝ):ℂ) * I)‖ ≤ 0.00000012688 := by
  have hl := lg_10
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.517784742228092792 31.51778476276010648 (-0.1018582) 0.00000002687 0.9948169371019 (-0.101682159965) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_11 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1635936893237:ℝ):ℂ) + (((-0.986527802352):ℝ):ℂ) * I)‖ ≤ 0.00000015252 := by
  have hl := lg_11
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.822390483389679704 32.82239050392170708 (-1.406464) 0.00000005251 0.1635936893237 (-0.986527802352) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_12 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8555847445337):ℝ):ℂ) + (((-0.5176627713519):ℝ):ℂ) * I)‖ ≤ 0.00000012429 := by
  have hl := lg_12
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.013402211623748832 34.01340223215576252 (-2.5974757) 0.00000002428 (-0.8555847445337) (-0.5176627713519) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_13 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8517355221603):ℝ):ℂ) + ((0.5239719460195:ℝ):ℂ) * I)‖ ≤ 0.00000014883 := by
  have hl := lg_13
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.1090267942591096 35.109026814791136976 2.590085 0.00000004882 (-0.8517355221603) 0.5239719460195 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_14 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0048987536117):ℝ):ℂ) + ((0.9999880010344:ℝ):ℂ) * I)‖ ≤ 0.00000012599 := by
  have hl := lg_14
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.123416717099256336 36.123416737631283712 1.5756951 0.00000002598 (-0.0048987536117) 0.9999880010344 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_15 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8072487203563:ℝ):ℂ) + ((0.5902114057549:ℝ):ℂ) * I)‖ ≤ 0.00000011948 := by
  have hl := lg_15
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.067791142012641624 37.067791162544669 0.6313207 0.00000001947 0.8072487203563 0.5902114057549 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_16 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9683950774038:ℝ):ℂ) + (((-0.2494212782825):ℝ):ℂ) * I)‖ ≤ 0.00000012731 := by
  have hl := lg_16
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.9511944157856 37.9511944431616 (-0.2520826) 0.0000000273 0.9683950774038 (-0.2494212782825) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_17 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4696408472038:ℝ):ℂ) + (((-0.8828575619191):ℝ):ℂ) * I)‖ ≤ 0.00000012352 := by
  have hl := lg_17
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.781024239208948592 38.78102426658496228 (-1.0819124) 0.00000002351 0.4696408472038 (-0.8828575619191) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_18 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2893047733357):ℝ):ℂ) + (((-0.9572370386292):ℝ):ℂ) * I)‖ ≤ 0.00000013168 := by
  have hl := lg_18
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.563408611408297664 39.56340863194032504 (-1.8642968) 0.00000003167 (-0.2893047733357) (-0.9572370386292) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_19 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8591327422995):ℝ):ℂ) + (((-0.5117528026587):ℝ):ℂ) * I)‖ ≤ 0.00000011363 := by
  have hl := lg_19
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.303480736155821864 40.303480756687862928 (-2.6043689) 0.00000001362 (-0.8591327422995) (-0.5117528026587) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_20 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9864382465296):ℝ):ℂ) + ((0.1641328285617:ℝ):ℂ) * I)‖ ≤ 0.00000012331 := by
  have hl := lg_20
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.005583346174492792 41.00558337355050648 2.9767138 0.0000000233 (-0.9864382465296) 0.1641328285617 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_21 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6728670887412):ℝ):ℂ) + ((0.7397633951942:ℝ):ℂ) * I)‖ ≤ 0.00000013339 := by
  have hl := lg_21
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.673423116883805168 41.673423137415846232 2.308874 0.00000003338 (-0.6728670887412) 0.7397633951942 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_22 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1011384506942):ℝ):ℂ) + ((0.9948723605522:ℝ):ℂ) * I)‖ ≤ 0.00000016294 := by
  have hl := lg_22
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.310189087336079704 42.31018911471210708 1.672108 0.00000006293 (-0.1011384506942) 0.9948723605522 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_23 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4856827244148:ℝ):ℂ) + ((0.8741351675828:ℝ):ℂ) * I)‖ ≤ 0.00000013687 := by
  have hl := lg_23
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.918644813405641808 42.918644840781682872 1.0636523 0.00000003686 0.4856827244148 0.8741351675828 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_24 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8864881413427:ℝ):ℂ) + ((0.4627513103804:ℝ):ℂ) * I)‖ ≤ 0.0000001347 := by
  have hl := lg_24
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.501200815570148832 43.50120084294616252 0.4810963 0.00000003469 0.8864881413427 0.4627513103804 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_25 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9969848058721:ℝ):ℂ) + (((-0.0775970157941):ℝ):ℂ) * I)‖ ≤ 0.0000001537 := by
  have hl := lg_25
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.059972276563385584 44.05997230393941296 (-0.0776751) 0.00000005369 0.9969848058721 (-0.0775970157941) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_26 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8170455073593:ℝ):ℂ) + (((-0.5765731860779):ℝ):ℂ) * I)‖ ≤ 0.00000015207 := by
  have hl := lg_26
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.5968253982055096 44.596825425581536976 (-0.6145283) 0.00000005206 0.8170455073593 (-0.5765731860779) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_27 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4256484991558:ℝ):ℂ) + (((-0.9048885871567):ℝ):ℂ) * I)‖ ≤ 0.00000013908 := by
  have hl := lg_27
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.113415011192846496 45.11341503172488756 (-1.1311179) 0.00000003907 0.4256484991558 (-0.9048885871567) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_28 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0580891546436):ℝ):ℂ) + (((-0.9983113993702):ℝ):ℂ) * I)‖ ≤ 0.00000012923 := by
  have hl := lg_28
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.611215321045656336 45.611215348421683712 (-1.6289182) 0.00000002922 (-0.0580891546436) (-0.9983113993702) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_29 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5128075342776):ℝ):ℂ) + (((-0.8585036009134):ℝ):ℂ) * I)‖ ≤ 0.00000014365 := by
  have hl := lg_29
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.091545306622320096 46.09154533399836116 (-2.1092482) 0.00000004364 (-0.5128075342776) (-0.8585036009134) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p688_30 : ‖exp (-((((((13688:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8428171037979):ℝ):ℂ) + (((-0.5382000831254):ℝ):ℂ) * I)‖ ≤ 0.00000012309 := by
  have hl := lg_30
  refine (ecis_approx ((((13688:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.555589745959041624 46.555589773335069 (-2.5732926) 0.00000002308 (-0.8428171037979) (-0.5382000831254) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_2 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9934733175099):ℝ):ℂ) + ((0.1140647489149:ℝ):ℂ) * I)‖ ≤ 0.00000011909 := by
  have hl := lg_2
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.5390914952886 9.5390915021696 3.0272791 0.00000001908 (-0.9934733175099) 0.1140647489149 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_3 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8315738609322):ℝ):ℂ) + (((-0.5554141821659):ℝ):ℂ) * I)‖ ≤ 0.00000010561 := by
  have hl := lg_3
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.119102313073152968 15.11910231995416673 (-2.5527317) 0.0000000056 (-0.8315738609322) (-0.5554141821659) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_4 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9739784676396:ℝ):ℂ) + (((-0.2266405625092):ℝ):ℂ) * I)‖ ≤ 0.00000013098 := by
  have hl := lg_4
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.0781829905772 19.0781830043392 (-0.2286271) 0.00000003097 0.9739784676396 (-0.2266405625092) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_5 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9875540202153):ℝ):ℂ) + ((0.1572801855749:ℝ):ℂ) * I)‖ ≤ 0.00000012882 := by
  have hl := lg_5
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.149084543763344258 22.14908455752535802 2.9836567 0.00000002881 (-0.9875540202153) 0.1572801855749 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_6 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8894996219129:ℝ):ℂ) + ((0.4569359064647:ℝ):ℂ) * I)‖ ≤ 0.00000012037 := by
  have hl := lg_6
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.658193808361752968 24.65819382212376673 0.4745474 0.00000002036 0.8894996219129 0.4569359064647 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_7 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0760045066451):ℝ):ℂ) + (((-0.9971074741317):ℝ):ℂ) * I)‖ ≤ 0.0000001492 := by
  have hl := lg_7
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.779615464144477564 26.779615477906505088 (-1.6468742) 0.00000004919 (-0.0760045066451) (-0.9971074741317) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_8 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9417699206581):ℝ):ℂ) + ((0.3362579610365:ℝ):ℂ) * I)‖ ≤ 0.00000015005 := by
  have hl := lg_8
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.6172744858658 28.6172745065088 2.798652 0.00000005004 (-0.9417699206581) 0.3362579610365 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_9 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.383030179052:ℝ):ℂ) + ((0.923735829085:ℝ):ℂ) * I)‖ ≤ 0.00000010977 := by
  have hl := lg_9
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.238204626146305936 30.23820463990833346 1.1777219 0.00000000976 0.383030179052 0.923735829085 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_10 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9631684460452:ℝ):ℂ) + (((-0.2688987626281):ℝ):ℂ) * I)‖ ≤ 0.00000012381 := by
  have hl := lg_10
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.688176039051944258 31.68817605969495802 (-0.2722495) 0.0000000238 0.9631684460452 (-0.2688987626281) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_11 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0131114975068):ℝ):ℂ) + (((-0.9999140406219):ℝ):ℂ) * I)‖ ≤ 0.00000011828 := by
  have hl := lg_11
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.999834733519051146 32.99983475416207867 (-1.5839082) 0.00000001827 (-0.0131114975068) (-0.9999140406219) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_12 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9358144174363):ℝ):ℂ) + (((-0.3524930863827):ℝ):ℂ) * I)‖ ≤ 0.00000013226 := by
  have hl := lg_12
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.197285303650352968 34.19728532429336673 (-2.7813588) 0.00000003225 (-0.9358144174363) (-0.3524930863827) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_13 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.73758200601):ℝ):ℂ) + ((0.6752575689167:ℝ):ℂ) * I)‖ ≤ 0.00000012423 := by
  have hl := lg_13
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.2988330466535554 35.298833067296582924 2.4002788 0.00000002422 (-0.73758200601) 0.6752575689167 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_14 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.189243263269:ℝ):ℂ) + ((0.9819302354583:ℝ):ℂ) * I)‖ ≤ 0.00000013701 := by
  have hl := lg_14
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.318706959433077564 36.318706980076105088 1.3804049 0.000000037 0.189243263269 0.9819302354583 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_15 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9085797553707:ℝ):ℂ) + ((0.4177114172852:ℝ):ℂ) * I)‖ ≤ 0.00000013442 := by
  have hl := lg_15
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.268186856836497226 37.26818687747952475 0.430925 0.00000003441 0.9085797553707 0.4177114172852 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_16 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.897268110851:ℝ):ℂ) + (((-0.4414860555554):ℝ):ℂ) * I)‖ ≤ 0.00000016194 := by
  have hl := lg_16
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.1563659811544 38.1563660086784 (-0.4572542) 0.00000006193 0.897268110851 (-0.4414860555554) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_17 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2756118308341:ℝ):ℂ) + (((-0.9612690147426):ℝ):ℂ) * I)‖ ≤ 0.0000001165 := by
  have hl := lg_17
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.990682026592164708 38.99068205411617847 (-1.2915702) 0.00000001649 0.2756118308341 (-0.9612690147426) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_18 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4858959520974):ℝ):ℂ) + (((-0.8740166610138):ℝ):ℂ) * I)‖ ≤ 0.00000012166 := by
  have hl := lg_18
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.777296121434905936 39.77729614207793346 (-2.0781843) 0.00000002165 (-0.4858959520974) (-0.8740166610138) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_19 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9494443152595):ℝ):ℂ) + (((-0.3139354902197):ℝ):ℂ) * I)‖ ≤ 0.00000012254 := by
  have hl := lg_19
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.521369220556430486 40.521369241199471772 (-2.8222574) 0.00000002253 (-0.9494443152595) (-0.3139354902197) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_20 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9262102816585):ℝ):ℂ) + ((0.3770073129227:ℝ):ℂ) * I)‖ ≤ 0.00000011593 := by
  have hl := lg_20
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.227267534340544258 41.22726756186455802 2.7550296 0.00000001592 (-0.9262102816585) 0.3770073129227 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_21 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4906042650151):ℝ):ℂ) + ((0.8713824964636:ℝ):ℂ) * I)‖ ≤ 0.00000014762 := by
  have hl := lg_21
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.898717777217630532 41.898717797860671818 2.0835794 0.00000004761 (-0.4906042650151) 0.8713824964636 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_22 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1270808671221:ℝ):ℂ) + ((0.99189235969:ℝ):ℂ) * I)‖ ≤ 0.00000012146 := by
  have hl := lg_22
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.538926228807651146 42.53892625633167867 1.4433709 0.00000002145 0.1270808671221 0.99189235969 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_23 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6736751398524:ℝ):ℂ) + ((0.739027608378:ℝ):ℂ) * I)‖ ≤ 0.00000016259 := by
  have hl := lg_23
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.150671385307454892 43.150671412831496178 0.8316258 0.00000006258 0.6736751398524 0.739027608378 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_24 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9699136895886:ℝ):ℂ) + ((0.2434490393259:ℝ):ℂ) * I)‖ ≤ 0.00000015133 := by
  have hl := lg_24
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.736376798938952968 43.73637682646296673 0.2459203 0.00000005132 0.9699136895886 0.2434490393259 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_25 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9505258575002:ℝ):ℂ) + (((-0.3106454477752):ℝ):ℂ) * I)‖ ≤ 0.00000016275 := by
  have hl := lg_25
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.298169087526688516 44.29816911505071604 (-0.315872) 0.00000006274 0.9505258575002 (-0.3106454477752) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_26 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6557449628232:ℝ):ℂ) + (((-0.7549824790894):ℝ):ℂ) * I)‖ ≤ 0.00000011922 := by
  have hl := lg_26
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.8379245419421554 44.837924569466182924 (-0.8556274) 0.00000001921 0.6557449628232 (-0.7549824790894) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_27 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1945380952277:ℝ):ℂ) + (((-0.9808949635436):ℝ):ℂ) * I)‖ ≤ 0.00000011105 := by
  have hl := lg_27
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.357306939219458904 45.35730695986250019 (-1.3750098) 0.00000001104 0.1945380952277 (-0.9808949635436) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_28 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3000117517353):ℝ):ℂ) + (((-0.9539355055867):ℝ):ℂ) * I)‖ ≤ 0.000000132 := by
  have hl := lg_28
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.857798454721677564 45.857798482245705088 (-1.8755013) 0.00000003199 (-0.3000117517353) (-0.9539355055867) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_29 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7086844166296):ℝ):ℂ) + (((-0.7055256179624):ℝ):ℂ) * I)‖ ≤ 0.00000015231 := by
  have hl := lg_29
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.340725197964375304 46.34072522548841659 (-2.3584281) 0.0000000523 (-0.7086844166296) (-0.7055256179624) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p762_30 : ‖exp (-((((((13762:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9502958896871):ℝ):ℂ) + (((-0.3113482324337):ℝ):ℂ) * I)‖ ≤ 0.00000012941 := by
  have hl := lg_30
  refine (ecis_approx ((((13762:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.807278352125097226 46.80727837964912475 (-2.8249812) 0.0000000294 (-0.9502958896871) (-0.3113482324337) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_2 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9884040138618):ℝ):ℂ) + ((0.1518469788695:ℝ):ℂ) * I)‖ ≤ 0.00000012417 := by
  have hl := lg_2
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.5772145902051 9.5772145971136 2.989156 0.00000002416 (-0.9884040138618) 0.1518469788695 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_3 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8635960370227):ℝ):ℂ) + (((-0.5041843757552):ℝ):ℂ) * I)‖ ≤ 0.00000012544 := by
  have hl := lg_3
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.179525988935601988 15.179525995844115805 (-2.6131554) 0.00000002543 (-0.8635960370227) (-0.5041843757552) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_4 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9538849920569:ℝ):ℂ) + (((-0.3001723203904):ℝ):ℂ) * I)‖ ≤ 0.00000014114 := by
  have hl := lg_4
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.1544291804102 19.1544291942272 (-0.3048733) 0.00000004113 0.9538849920569 (-0.3001723203904) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_5 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9697833655629):ℝ):ℂ) + ((0.2439676691834:ℝ):ℂ) * I)‖ ≤ 0.00000011403 := by
  have hl := lg_5
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.237603628918625753 22.23760364273563957 2.8951376 0.00000001402 (-0.9697833655629) 0.2439676691834 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_6 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9301406638686:ℝ):ℂ) + ((0.3672034115011:ℝ):ℂ) * I)‖ ≤ 0.00000014959 := by
  have hl := lg_6
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.756740579140701988 24.756740592957715805 0.3760006 0.00000004958 0.9301406638686 0.3672034115011 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_7 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1820815472563):ℝ):ℂ) + (((-0.9832834332724):ℝ):ℂ) * I)‖ ≤ 0.00000010743 := by
  have hl := lg_7
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.886640522313925774 26.886640536130953408 (-1.7538993) 0.00000000742 (-0.1820815472563) (-0.9832834332724) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_8 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8972435391446):ℝ):ℂ) + ((0.4415359910018:ℝ):ℂ) * I)‖ ≤ 0.00000015546 := by
  have hl := lg_8
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.7316437706153 28.7316437913408 2.6842828 0.00000005545 (-0.8972435391446) 0.4415359910018 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_9 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4915961495664:ℝ):ℂ) + ((0.8708233033925:ℝ):ℂ) * I)‖ ≤ 0.00000015581 := by
  have hl := lg_9
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.359051977871203976 30.35905199168823161 1.0568746 0.0000000558 0.4915961495664 0.8708233033925 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_10 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9214920205805:ℝ):ℂ) + (((-0.3883972914511):ℝ):ℂ) * I)‖ ≤ 0.00000011679 := by
  have hl := lg_10
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.814818219123725753 31.81481823984923957 (-0.3988917) 0.00000001678 0.9214920205805 (-0.3883972914511) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_11 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1444885441228):ℝ):ℂ) + (((-0.9895064732566):ℝ):ℂ) * I)‖ ≤ 0.00000015832 := by
  have hl := lg_11
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.131718973480070461 33.131718994205598095 (-1.7157924) 0.00000005831 (-0.1444885441228) (-0.9895064732566) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_12 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9751134706361):ℝ):ℂ) + (((-0.2217063803498):ℝ):ℂ) * I)‖ ≤ 0.00000015419 := by
  have hl := lg_12
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.333955169345801988 34.333955190071315805 (-2.9180286) 0.00000005418 (-0.9751134706361) (-0.2217063803498) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_13 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6353103079433):ℝ):ℂ) + ((0.7722569602184:ℝ):ℂ) * I)‖ ≤ 0.00000013893 := by
  have hl := lg_13
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.4399052612710489 35.439905281996576534 2.2592066 0.00000003892 (-0.6353103079433) 0.7722569602184 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_14 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3292787510893:ℝ):ℂ) + ((0.9442327594831:ℝ):ℂ) * I)‖ ≤ 0.00000013057 := by
  have hl := lg_14
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.463855112519025774 36.463855133244553408 1.2352567 0.00000003056 0.3292787510893 0.9442327594831 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_15 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.960505758454:ℝ):ℂ) + ((0.2782601084898:ℝ):ℂ) * I)‖ ≤ 0.00000012524 := by
  have hl := lg_15
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.417129617854227741 37.417129638579755375 0.2819822 0.00000002523 0.960505758454 0.2782601084898 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_16 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8197932134088:ℝ):ℂ) + (((-0.5726596609233):ℝ):ℂ) * I)‖ ≤ 0.00000014539 := by
  have hl := lg_16
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.3088583608204 38.3088583884544 (-0.6097465) 0.00000004538 0.8197932134088 (-0.5726596609233) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_17 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.123086489365:ℝ):ℂ) + (((-0.9923959472588):ℝ):ℂ) * I)‖ ≤ 0.00000014503 := by
  have hl := lg_17
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.146508760458068578 39.146508788092082395 (-1.4473969) 0.00000004502 0.123086489365 (-0.9923959472588) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_18 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6181274897819):ℝ):ℂ) + (((-0.786077862786):ℝ):ℂ) * I)‖ ≤ 0.00000014574 := by
  have hl := lg_18
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.936266568076303976 39.93626658880183161 (-2.2371547) 0.00000004573 (-0.6181274897819) (-0.786077862786) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_19 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9876395598994):ℝ):ℂ) + (((-0.15674214283):ℝ):ℂ) * I)‖ ≤ 0.00000014203 := by
  have hl := lg_19
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.683313364367693651 40.683313385093235102 (-2.9842015) 0.00000004202 (-0.9876395598994) (-0.15674214283) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_20 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8518294566387):ℝ):ℂ) + ((0.5238192214187:ℝ):ℂ) * I)‖ ≤ 0.00000014094 := by
  have hl := lg_20
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.392032809328825753 41.39203283696283957 2.5902643 0.00000004093 (-0.8518294566387) 0.5238192214187 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_21 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.338511234655):ℝ):ℂ) + ((0.9409623499429:ℝ):ℂ) * I)‖ ≤ 0.00000013902 := by
  have hl := lg_21
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.066166511249527762 42.066166531975069213 1.9161306 0.00000003901 (-0.338511234655) 0.9409623499429 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_22 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2930666257148:ℝ):ℂ) + ((0.9560920211424:ℝ):ℂ) * I)‖ ≤ 0.00000014108 := by
  have hl := lg_22
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.708933563685170461 42.708933591319198095 1.2733636 0.00000004107 0.2930666257148 0.9560920211424 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_23 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7904986414487:ℝ):ℂ) + ((0.6124637931076:ℝ):ℂ) * I)‖ ≤ 0.00000014452 := by
  have hl := lg_23
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.323123567126370022 43.323123594760411473 0.6591736 0.00000004451 0.7904986414487 0.6124637931076 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_24 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.997471512745:ℝ):ℂ) + ((0.0710674416472:ℝ):ℂ) * I)‖ ≤ 0.00000013694 := by
  have hl := lg_24
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.911169759550901988 43.911169787184915805 0.0711274 0.00000003693 0.997471512745 0.0710674416472 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_25 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8809595560505:ℝ):ℂ) + (((-0.4731915686098):ℝ):ℂ) * I)‖ ≤ 0.00000013523 := by
  have hl := lg_25
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.475207257837251506 44.47520728547127914 (-0.4929101) 0.00000003522 0.8809595560505 (-0.4731915686098) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_26 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.510678378233:ℝ):ℂ) + (((-0.8597718267106):ℝ):ℂ) * I)‖ ≤ 0.00000012887 := by
  have hl := lg_26
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.0171198514761489 45.017119879110176534 (-1.0348227) 0.00000002886 0.510678378233 (-0.8597718267106) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_27 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0145150170621:ℝ):ℂ) + (((-0.9998946515906):ℝ):ℂ) * I)‖ ≤ 0.00000013729 := by
  have hl := lg_27
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.538577966806805964 45.538577987532347415 (-1.5562808) 0.00000003728 0.0145150170621 (-0.9998946515906) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_28 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4688393250251):ℝ):ℂ) + (((-0.8832834693941):ℝ):ℂ) * I)‖ ≤ 0.00000014755 := by
  have hl := lg_28
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.041069702724125774 46.041069730358153408 (-2.0587726) 0.00000004754 (-0.4688393250251) (-0.8832834693941) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_29 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8264838794514):ℝ):ℂ) + (((-0.562960386658):ℝ):ℂ) * I)‖ ≤ 0.00000014595 := by
  have hl := lg_29
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.525926468556443364 46.525926496190484815 (-2.5436293) 0.00000004594 (-0.8264838794514) (-0.562960386658) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_30 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9916207029059):ℝ):ℂ) + (((-0.1291835173025):ℝ):ℂ) * I)‖ ≤ 0.00000014221 := by
  have hl := lg_30
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.994344208059327741 46.994344235693355375 (-3.0120471) 0.0000000422 (-0.9916207029059) (-0.1291835173025) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_31 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9481250140179):ℝ):ℂ) + ((0.3178977156179:ℝ):ℂ) * I)‖ ≤ 0.00000016022 := by
  have hl := lg_31
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.447401190004580571 47.447401217638622022 2.8180813 0.00000006021 (-0.9481250140179) 0.3178977156179 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_32 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7233302632641):ℝ):ℂ) + ((0.6905022304224:ℝ):ℂ) * I)‖ ≤ 0.00000012815 := by
  have hl := lg_32
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.8860729510255 47.886072985568 2.3794095 0.00000002814 (-0.7233302632641) 0.6905022304224 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_33 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3741139628092):ℝ):ℂ) + ((0.9273827380475:ℝ):ℂ) * I)‖ ≤ 0.00000013263 := by
  have hl := lg_33
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.311244962415672449 48.3112449900497139 1.9542375 0.00000003262 (-0.3741139628092) 0.9273827380475 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_34 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0290331464596:ℝ):ℂ) + ((0.9995784493508:ℝ):ℂ) * I)‖ ≤ 0.00000012778 := by
  have hl := lg_34
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.723723350663168578 48.723723385205682395 1.5417591 0.00000002777 0.0290331464596 0.9995784493508 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_35 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4164690232207:ℝ):ℂ) + ((0.9091499066147:ℝ):ℂ) * I)‖ ≤ 0.00000012144 := by
  have hl := lg_35
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.124244151232551527 49.124244178866592978 1.1412383 0.00000002143 0.4164690232207 0.9091499066147 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_36 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7303232408538:ℝ):ℂ) + ((0.6831017229292:ℝ):ℂ) * I)‖ ≤ 0.00000012849 := by
  have hl := lg_36
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.513481158281403976 49.51348118591543161 0.7520013 0.00000002848 0.7303232408538 0.6831017229292 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_37 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9310816321862:ℝ):ℂ) + ((0.3648109019828:ℝ):ℂ) * I)‖ ≤ 0.00000015485 := by
  have hl := lg_37
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.892052784638575114 49.892052812272616565 0.3734297 0.00000005484 0.9310816321862 0.3648109019828 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_38 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.99998772649:ℝ):ℂ) + ((0.0049544797303:ℝ):ℂ) * I)‖ ≤ 0.00000012479 := by
  have hl := lg_38
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.260527954572793651 50.260527982206835102 0.0049545 0.00000002478 0.99998772649 0.0049544797303 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_39 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9380113576843:ℝ):ℂ) + (((-0.3466045193809):ℝ):ℂ) * I)‖ ≤ 0.00000012042 := by
  have hl := lg_39
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.619431250206650888 50.619431277840692339 (-0.3539488) 0.00000002041 0.9380113576843 (-0.3466045193809) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p817_40 : ‖exp (-((((((13817:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7624112925237:ℝ):ℂ) + (((-0.6470927453096):ℝ):ℂ) * I)‖ ≤ 0.00000015792 := by
  have hl := lg_40
  refine (ecis_approx ((((13817:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.969247399533925753 50.96924743407643957 (-0.703765) 0.00000005791 0.7624112925237 (-0.6470927453096) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_2 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.981898366696):ℝ):ℂ) + ((0.1894085455906:ℝ):ℂ) * I)‖ ≤ 0.00000012925 := by
  have hl := lg_2
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.6153376851216 9.6153376920576 2.9510329 0.00000002924 (-0.981898366696) 0.1894085455906 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_3 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8924661628585):ℝ):ℂ) + (((-0.4511143403222):ℝ):ℂ) * I)‖ ≤ 0.00000014958 := by
  have hl := lg_3
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.239949664798051008 15.23994967173406488 (-2.6735791) 0.00000004957 (-0.8924661628585) (-0.4511143403222) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_4 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9282488082593:ℝ):ℂ) + (((-0.3719598768217):ℝ):ℂ) * I)‖ ≤ 0.00000015131 := by
  have hl := lg_4
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.2306753702432 19.2306753841152 (-0.3811195) 0.0000000513 0.9282488082593 (-0.3719598768217) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_5 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9444188067541):ℝ):ℂ) + ((0.328744760049:ℝ):ℂ) * I)‖ ≤ 0.00000011466 := by
  have hl := lg_5
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.326122714073907248 22.32612272794592112 2.8066185 0.00000001465 (-0.9444188067541) 0.328744760049 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_6 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9617559515879:ℝ):ℂ) + ((0.2739078122018:ℝ):ℂ) * I)‖ ≤ 0.00000013509 := by
  have hl := lg_6
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.855287349919651008 24.85528736379166488 0.2774539 0.00000003508 0.9617559515879 0.2739078122018 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_7 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2860749481238):ℝ):ℂ) + (((-0.9582072448351):ℝ):ℂ) * I)‖ ≤ 0.00000014825 := by
  have hl := lg_7
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.993665580483373984 26.993665594355401728 (-1.8609244) 0.00000004824 (-0.2860749481238) (-0.9582072448351) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_8 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8409936635865):ℝ):ℂ) + ((0.541044968315:ℝ):ℂ) * I)‖ ≤ 0.00000014029 := by
  have hl := lg_8
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.8460130553648 28.8460130761728 2.5699135 0.00000004028 (-0.8409936635865) 0.541044968315 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_9 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5929916290657:ℝ):ℂ) + ((0.80520862381:ℝ):ℂ) * I)‖ ≤ 0.00000010759 := by
  have hl := lg_9
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.479899329596102016 30.47989934346812976 0.9360272 0.00000000758 0.5929916290657 0.80520862381 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_10 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8650562206825:ℝ):ℂ) + (((-0.5016749296691):ℝ):ℂ) * I)‖ ≤ 0.00000013672 := by
  have hl := lg_10
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.941460399195507248 31.94146042000352112 (-0.5255339) 0.00000003671 0.8650562206825 (-0.5016749296691) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_11 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2733561743751):ℝ):ℂ) + (((-0.9619128868715):ℝ):ℂ) * I)‖ ≤ 0.00000012247 := by
  have hl := lg_11
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.263603213441089776 33.26360323424911752 (-1.8476767) 0.00000002246 (-0.2733561743751) (-0.9619128868715) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_12 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9962270776855):ℝ):ℂ) + (((-0.0867848442205):ℝ):ℂ) * I)‖ ≤ 0.00000011997 := by
  have hl := lg_12
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.470625035041251008 34.47062505584926488 (-3.0546985) 0.00000001996 (-0.9962270776855) (-0.0867848442205) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_13 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5204160219002):ℝ):ℂ) + ((0.8539128551219:ℝ):ℂ) * I)‖ ≤ 0.00000015363 := by
  have hl := lg_13
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.5809774758885424 35.580977496696570144 2.1181344 0.00000005362 (-0.5204160219002) 0.8539128551219 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_14 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4623890764653:ℝ):ℂ) + ((0.8866771351318:ℝ):ℂ) * I)‖ ≤ 0.00000014335 := by
  have hl := lg_14
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.609003265604973984 36.609003286413001728 1.0901086 0.00000004334 0.4623890764653 0.8866771351318 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_15 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9911632910464:ℝ):ℂ) + ((0.1326473915391:ℝ):ℂ) * I)‖ ≤ 0.00000015662 := by
  have hl := lg_15
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.566072378871958256 37.566072399679986 0.1330395 0.00000005661 0.9911632910464 0.1326473915391 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_16 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7232917691238:ℝ):ℂ) + (((-0.6905425524309):ℝ):ℂ) * I)‖ ≤ 0.00000012517 := by
  have hl := lg_16
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.4613507404864 38.4613507682304 (-0.7622389) 0.00000002516 0.7232917691238 (-0.6905425524309) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_17 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0324216904202):ℝ):ℂ) + (((-0.9994742788036):ℝ):ℂ) * I)‖ ≤ 0.00000014877 := by
  have hl := lg_17
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.302335494323972448 39.30233552206798632 (-1.6032237) 0.00000004876 (-0.0324216904202) (-0.9994742788036) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_18 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7347709017184):ℝ):ℂ) + (((-0.678315355832):ℝ):ℂ) * I)‖ ≤ 0.00000012837 := by
  have hl := lg_18
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.095237014717702016 40.09523703552572976 (-2.3961252) 0.00000002836 (-0.7347709017184) (-0.678315355832) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_19 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999896345326):ℝ):ℂ) + ((0.0045530375583:ℝ):ℂ) * I)‖ ≤ 0.00000014209 := by
  have hl := lg_19
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.845257508178956816 40.845257528986998432 3.1370396 0.00000004208 (-0.9999896345326) 0.0045530375583 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_20 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7543758370762):ℝ):ℂ) + ((0.6564427594243:ℝ):ℂ) * I)‖ ≤ 0.00000016182 := by
  have hl := lg_20
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.556798084317107248 41.55679811206112112 2.4254991 0.00000006181 (-0.7543758370762) 0.6564427594243 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_21 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1769489093073):ℝ):ℂ) + ((0.9842200381491:ℝ):ℂ) * I)‖ ≤ 0.00000011585 := by
  have hl := lg_21
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.233615245281424992 42.233615266089466608 1.7486819 0.00000001584 (-0.1769489093073) 0.9842200381491 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_22 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4506025022303:ℝ):ℂ) + ((0.8927246971961:ℝ):ℂ) * I)‖ ≤ 0.00000015171 := by
  have hl := lg_22
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.878940898562689776 42.87894092630671752 1.1033562 0.0000000517 0.4506025022303 0.8927246971961 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_23 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8838711076929:ℝ):ℂ) + ((0.4677305474156:ℝ):ℂ) * I)‖ ≤ 0.00000012645 := by
  have hl := lg_23
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.495575748945285152 43.495575776689326768 0.4867214 0.00000002644 0.8838711076929 0.4677305474156 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_24 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9946315319849:ℝ):ℂ) + (((-0.1034800250359):ℝ):ℂ) * I)‖ ≤ 0.00000013011 := by
  have hl := lg_24
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.085962720162851008 44.08596274790686488 (-0.1036656) 0.0000000301 0.9946315319849 (-0.1034800250359) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_25 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7838537698088:ℝ):ℂ) + (((-0.6209454626265):ℝ):ℂ) * I)‖ ≤ 0.00000012212 := by
  have hl := lg_25
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.652245428147814496 44.65224545589184224 (-0.6699483) 0.00000002211 0.7838537698088 (-0.6209454626265) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_26 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3492572566144:ℝ):ℂ) + (((-0.9370268772571):ℝ):ℂ) * I)‖ ≤ 0.00000013851 := by
  have hl := lg_26
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.1963151610101424 45.196315188754170144 (-1.214018) 0.0000000385 0.3492572566144 (-0.9370268772571) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_27 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1659838066189):ℝ):ℂ) + (((-0.9861284784143):ℝ):ℂ) * I)‖ ≤ 0.00000015588 := by
  have hl := lg_27
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.719848994394153024 45.71984901520219464 (-1.7375519) 0.00000005587 (-0.1659838066189) (-0.9861284784143) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_28 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6219633001216):ℝ):ℂ) + (((-0.7830463928069):ℝ):ℂ) * I)‖ ≤ 0.00000012823 := by
  have hl := lg_28
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.224340950726573984 46.224340978470601728 (-2.2420438) 0.00000002822 (-0.6219633001216) (-0.7830463928069) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_29 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9160163455208):ℝ):ℂ) + (((-0.4011409410689):ℝ):ℂ) * I)‖ ≤ 0.00000011665 := by
  have hl := lg_29
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.711127739148511424 46.71112776689255304 (-2.7288306) 0.00000001664 (-0.9160163455208) (-0.4011409410689) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_30 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9983461660113):ℝ):ℂ) + ((0.0574885401912:ℝ):ℂ) * I)‖ ≤ 0.00000013432 := by
  have hl := lg_30
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.181410063993558256 47.181410091737586 3.0840724 0.00000003431 (-0.9983461660113) 0.0574885401912 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_31 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.871579854661):ℝ):ℂ) + ((0.4902535638422:ℝ):ℂ) * I)‖ ≤ 0.00000015652 := by
  have hl := lg_31
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.636270486194075536 47.636270513938117152 2.629212 0.00000005651 (-0.871579854661) 0.4902535638422 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_32 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5794043462086):ℝ):ℂ) + ((0.8150402466038:ℝ):ℂ) * I)‖ ≤ 0.00000013184 := by
  have hl := lg_32
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.076688425608 48.076688460288 2.188794 0.00000003183 (-0.5794043462086) 0.8150402466038 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_33 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1899716525488):ℝ):ℂ) + ((0.9817895758395:ℝ):ℂ) * I)‖ ≤ 0.00000014856 := by
  have hl := lg_33
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.503552878239140784 48.5035529059831824 1.7619296 0.00000004855 (-0.1899716525488) 0.9817895758395 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_34 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2211436770187:ℝ):ℂ) + ((0.9752412389325:ℝ):ℂ) * I)‖ ≤ 0.0000001567 := by
  have hl := lg_34
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.917673179445572448 48.91767321412558632 1.3478093 0.00000005669 0.2211436770187 0.9752412389325 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_35 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5851801720436:ℝ):ℂ) + ((0.810903302649:ℝ):ℂ) * I)‖ ≤ 0.00000016289 := by
  have hl := lg_35
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.319788294557281232 49.319788322301322848 0.9456941 0.00000006288 0.5851801720436 0.810903302649 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_36 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8499490735161:ℝ):ℂ) + ((0.5268648521482:ℝ):ℂ) * I)‖ ≤ 0.00000015761 := by
  have hl := lg_36
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.710574699839302016 49.71057472758332976 0.5549077 0.0000000576 0.8499490735161 0.5268648521482 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_37 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9847562622112:ℝ):ℂ) + ((0.173939943762:ℝ):ℂ) * I)‖ ≤ 0.0000001401 := by
  have hl := lg_37
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.090653269776819424 50.09065329752086104 0.1748292 0.00000004009 0.9847562622112 0.173939943762 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_38 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9810258258308:ℝ):ℂ) + (((-0.193877097804):ℝ):ℂ) * I)‖ ≤ 0.00000016362 := by
  have hl := lg_38
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.460595193300556816 50.460595221044598432 (-0.1951127) 0.00000006361 0.9810258258308 (-0.193877097804) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_39 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8496660245546:ℝ):ℂ) + (((-0.527321198813):ℝ):ℂ) * I)‖ ≤ 0.00000011677 := by
  have hl := lg_39
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.820927140686593408 50.820927168430635024 (-0.5554447) 0.00000001676 0.8496660245546 (-0.527321198813) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p872_40 : ‖exp (-((((((13872:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6163845396261:ℝ):ℂ) + (((-0.7874452992494):ℝ):ℂ) * I)‖ ≤ 0.0000001467 := by
  have hl := lg_40
  refine (ecis_approx ((((13872:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.172135769438707248 51.17213580411872112 (-0.9066533) 0.00000004669 0.6163845396261 (-0.7874452992494) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_2 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9761198064868):ℝ):ℂ) + ((0.2172328775362:ℝ):ℂ) * I)‖ ≤ 0.00000011213 := by
  have hl := lg_2
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.6437567195139 9.6437567264704 2.9226139 0.00000001212 (-0.9761198064868) 0.2172328775362 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_3 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9118736801914):ℝ):ℂ) + (((-0.410470938366):ℝ):ℂ) * I)‖ ≤ 0.00000014575 := by
  have hl := lg_3
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.284992768622785732 15.284992775579299645 (-2.7186222) 0.00000004574 (-0.9118736801914) (-0.410470938366) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_4 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9056197567488:ℝ):ℂ) + (((-0.4240906226106):ℝ):ℂ) * I)‖ ≤ 0.00000013142 := by
  have hl := lg_4
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.2875134390278 19.2875134529408 (-0.4379575) 0.00000003141 0.9056197567488 (-0.4240906226106) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_5 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.920686316762):ℝ):ℂ) + ((0.3903033512324:ℝ):ℂ) * I)‖ ≤ 0.00000015367 := by
  have hl := lg_5
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.392109668462389817 22.39210968237540373 2.7406316 0.00000005366 (-0.920686316762) 0.3903033512324 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_6 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9792657435617:ℝ):ℂ) + ((0.2025798694012:ℝ):ℂ) * I)‖ ≤ 0.0000001406 := by
  have hl := lg_6
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.928749488136685732 24.928749502049699645 0.2039917 0.00000004059 0.9792657435617 0.2025798694012 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_7 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.361531869001):ℝ):ℂ) + (((-0.9323597522921):ℝ):ℂ) * I)‖ ≤ 0.00000013216 := by
  have hl := lg_7
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.073447896573326286 27.073447910486354112 (-1.9407067) 0.00000003215 (-0.361531869001) (-0.9323597522921) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_8 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.791866955459):ℝ):ℂ) + ((0.6106936423493:ℝ):ℂ) * I)‖ ≤ 0.00000014353 := by
  have hl := lg_8
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.9312701585417 28.9312701794112 2.4846564 0.00000004352 (-0.791866955459) 0.6106936423493 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_9 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6630271479135:ℝ):ℂ) + ((0.7485953520626:ℝ):ℂ) * I)‖ ≤ 0.00000011528 := by
  have hl := lg_9
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.569985537245571464 30.56998555115859929 0.845941 0.00000001527 0.6630271479135 0.7485953520626 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_10 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8139133754058:ℝ):ℂ) + (((-0.5809862453927):ℝ):ℂ) * I)‖ ≤ 0.00000014794 := by
  have hl := lg_10
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.035866387976289817 32.03586640884580373 (-0.6199399) 0.00000004793 0.8139133754058 (-0.5809862453927) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_11 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3664531087839):ℝ):ℂ) + (((-0.9304365207041):ℝ):ℂ) * I)‖ ≤ 0.00000011632 := by
  have hl := lg_11
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.361916919593849629 33.361916940463377455 (-1.9459904) 0.00000001631 (-0.3664531087839) (-0.9304365207041) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_12 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998876958931):ℝ):ℂ) + ((0.01498649226:ℝ):ℂ) * I)‖ ≤ 0.00000013544 := by
  have hl := lg_12
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.572506207650585732 34.572506228520099645 3.1266056 0.00000003543 (-0.9998876958931) 0.01498649226 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_13 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.427906357067):ℝ):ℂ) + ((0.9038230742672:ℝ):ℂ) * I)‖ ≤ 0.00000014358 := by
  have hl := lg_13
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.6861403995124921 35.686140420382019926 2.0129714 0.00000004357 (-0.427906357067) 0.9038230742672 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_14 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5554376100815:ℝ):ℂ) + ((0.8315582128191:ℝ):ℂ) * I)‖ ≤ 0.00000012701 := by
  have hl := lg_14
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.717204616087226286 36.717204636956754112 0.9819072 0.000000027 0.5554376100815 0.8315582128191 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_15 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.999757802933:ℝ):ℂ) + ((0.0220076231006:ℝ):ℂ) * I)‖ ≤ 0.00000011489 := by
  have hl := lg_15
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.677102437085175549 37.677102457954703375 0.0220094 0.00000001488 0.999757802933 0.0220076231006 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_16 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6402942876275:ℝ):ℂ) + (((-0.7681296929761):ℝ):ℂ) * I)‖ ≤ 0.00000016282 := by
  have hl := lg_16
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.5750268780556 38.5750269058816 (-0.875915) 0.00000006281 0.6402942876275 (-0.7681296929761) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_17 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1480429005844):ℝ):ℂ) + (((-0.9889809399508):ℝ):ℂ) * I)‖ ≤ 0.00000012615 := by
  have hl := lg_17
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.418497241387646242 39.418497269213660155 (-1.7193854) 0.00000002614 (-0.1480429005844) (-0.9889809399508) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_18 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8098134497249):ℝ):ℂ) + (((-0.5866874607416):ℝ):ℂ) * I)‖ ≤ 0.00000013457 := by
  have hl := lg_18
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.213742256759471464 40.21374227762899929 (-2.5146304) 0.00000003456 (-0.8098134497249) (-0.5866874607416) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_19 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9921633372727):ℝ):ℂ) + ((0.1249476359895:ℝ):ℂ) * I)‖ ≤ 0.00000014398 := by
  have hl := lg_19
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.965979506292807539 40.965979527162349278 3.0163176 0.00000004397 (-0.9921633372727) 0.1249476359895 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_20 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6682676526114):ℝ):ℂ) + ((0.7439209262107:ℝ):ℂ) * I)‖ ≤ 0.00000014278 := by
  have hl := lg_20
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.679623107490189817 41.67962313531620373 2.302674 0.00000004277 (-0.6682676526114) 0.7439209262107 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_21 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0530352792671):ℝ):ℂ) + ((0.9985926392442:ℝ):ℂ) * I)‖ ≤ 0.00000013582 := by
  have hl := lg_21
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.358440665196112018 42.358440686065653757 1.6238565 0.00000003581 (-0.0530352792671) 0.9985926392442 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_22 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5598235405744:ℝ):ℂ) + ((0.8286118532937:ℝ):ℂ) * I)‖ ≤ 0.00000011669 := by
  have hl := lg_22
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.005673639107749629 43.005673666933777455 0.9766235 0.00000001668 0.5598235405744 0.8286118532937 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_23 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9365412852336:ℝ):ℂ) + ((0.3505573006699:ℝ):ℂ) * I)‖ ≤ 0.00000013852 := by
  have hl := lg_23
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.624131011755749158 43.624131039581790897 0.3581661 0.00000003851 0.9365412852336 0.3505573006699 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_24 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9727546274195:ℝ):ℂ) + (((-0.231837086839):ℝ):ℂ) * I)‖ ≤ 0.00000012311 := by
  have hl := lg_24
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.216262927164485732 44.216262954990499645 (-0.2339658) 0.0000000231 0.9727546274195 (-0.231837086839) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_25 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6953265212044:ℝ):ℂ) + (((-0.7186939744493):ℝ):ℂ) * I)‖ ≤ 0.00000011451 := by
  have hl := lg_25
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.784219336924779634 44.78421936475080746 (-0.8019222) 0.0000000145 0.6953265212044 (-0.7186939744493) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_26 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2213477901648:ℝ):ℂ) + (((-0.9751949322003):ℝ):ℂ) * I)‖ ≤ 0.00000013125 := by
  have hl := lg_26
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.3298971190263921 45.329897146852419926 (-1.3476) 0.00000003124 0.2213477901648 (-0.9751949322003) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_27 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2973203687913):ℝ):ℂ) + (((-0.9547777743015):ℝ):ℂ) * I)‖ ≤ 0.0000001444 := by
  have hl := lg_27
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.854978305868357196 45.854978326737898935 (-1.8726812) 0.00000004439 (-0.2973203687913) (-0.9547777743015) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_28 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7228154311045):ℝ):ℂ) + (((-0.6910411366405):ℝ):ℂ) * I)‖ ≤ 0.00000011467 := by
  have hl := lg_28
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.360961335601126286 46.360961363427154112 (-2.3786642) 0.00000001466 (-0.7228154311045) (-0.6910411366405) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_29 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9625058171185):ℝ):ℂ) + (((-0.2712610399067):ℝ):ℂ) * I)‖ ≤ 0.00000014572 := by
  have hl := lg_29
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.849186868135325796 46.849186895961367535 (-2.8668897) 0.00000004571 (-0.9625058171185) (-0.2712610399067) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_30 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9806641724156):ℝ):ℂ) + ((0.1956981875536:ℝ):ℂ) * I)‖ ≤ 0.000000127 := by
  have hl := lg_30
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.320859156599075549 47.320859184425103375 2.9446233 0.00000002699 (-0.9806641724156) 0.1956981875536 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_31 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7941588367944):ℝ):ℂ) + ((0.6077102450135:ℝ):ℂ) * I)‖ ≤ 0.00000013194 := by
  have hl := lg_31
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.777063961535335419 47.777063989361377158 2.4884185 0.00000003193 (-0.7941588367944) 0.6077102450135 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_32 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4581408236813):ℝ):ℂ) + ((0.8888796238366:ℝ):ℂ) * I)‖ ≤ 0.00000015988 := by
  have hl := lg_32
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.2187835975695 48.218783632352 2.0466988 0.00000005987 (-0.4581408236813) 0.8888796238366 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_33 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.047758299585):ℝ):ℂ) + ((0.99885892138:ℝ):ℂ) * I)‖ ≤ 0.00000015862 := by
  have hl := lg_33
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.646909688216635361 48.6469097160426771 1.6185728 0.00000005861 (-0.047758299585) 0.99885892138 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_34 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3593467830508:ℝ):ℂ) + ((0.9332040985289:ℝ):ℂ) * I)‖ ≤ 0.00000013826 := by
  have hl := lg_34
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.062253960901546242 49.062253995684060155 1.2032285 0.00000003825 0.3593467830508 0.9332040985289 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_35 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6967605808248:ℝ):ℂ) + ((0.7173037662028:ℝ):ℂ) * I)‖ ≤ 0.00000013544 := by
  have hl := lg_35
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.465557565035716103 49.465557592861757842 0.7999249 0.00000003543 0.6967605808248 0.7173037662028 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_36 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9179227533509:ℝ):ℂ) + ((0.3967591446718:ℝ):ℂ) * I)‖ ≤ 0.00000014668 := by
  have hl := lg_36
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.857498976273371464 49.85749900409939929 0.4079835 0.00000004667 0.9179227533509 0.3967591446718 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_37 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9996413970636:ℝ):ℂ) + ((0.0267782986153:ℝ):ℂ) * I)‖ ≤ 0.0000001533 := by
  have hl := lg_37
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.238700904152601546 50.238700931978643285 0.0267815 0.00000005329 0.9996413970636 0.0267782986153 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_38 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9413275529415:ℝ):ℂ) + (((-0.3374943526538):ℝ):ℂ) * I)‖ ≤ 0.00000013164 := by
  have hl := lg_38
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.609736225806707539 50.609736253632749278 (-0.3442538) 0.00000003163 0.9413275529415 (-0.3374943526538) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_39 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7611897149418:ℝ):ℂ) + (((-0.6485292729452):ℝ):ℂ) * I)‖ ≤ 0.00000013854 := by
  have hl := lg_39
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.971133168135277832 50.971133195961319571 (-0.7056507) 0.00000003853 0.7611897149418 (-0.6485292729452) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p913_40 : ‖exp (-((((((13913:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4907052145128:ℝ):ℂ) + (((-0.8713256523539):ℝ):ℂ) * I)‖ ≤ 0.00000013045 := by
  have hl := lg_40
  refine (ecis_approx ((((13913:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.323379827004089817 51.32337986178660373 (-1.0578974) 0.00000003044 0.4907052145128 (-0.8713256523539) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_2 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9695529463605):ℝ):ℂ) + ((0.2448817754223:ℝ):ℂ) * I)‖ ≤ 0.00000014654 := by
  have hl := lg_2
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.6721757539062 9.6721757608832 2.8941949 0.00000004653 (-0.9695529463605) 0.2448817754223 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_3 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9294314272461):ℝ):ℂ) + (((-0.3689948805725):ℝ):ℂ) * I)‖ ≤ 0.00000014193 := by
  have hl := lg_3
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.330035872447520456 15.33003587942453441 (-2.7636653) 0.00000004192 (-0.9294314272461) (-0.3689948805725) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_4 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8800657879228:ℝ):ℂ) + (((-0.4748517757447):ℝ):ℂ) * I)‖ ≤ 0.00000011374 := by
  have hl := lg_4
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.3443515078124 19.3443515217664 (-0.4947956) 0.00000001373 0.8800657879228 (-0.4748517757447) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_5 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8929463184931):ℝ):ℂ) + ((0.4501631617325:ℝ):ℂ) * I)‖ ≤ 0.0000001081 := by
  have hl := lg_5
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.458096622850872386 22.45809663680488634 2.6746446 0.00000000809 (-0.8929463184931) 0.4501631617325 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_6 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9914931004213:ℝ):ℂ) + ((0.1301592555944:ℝ):ℂ) * I)‖ ≤ 0.0000001116 := by
  have hl := lg_6
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.002211626353720456 25.00221164030773441 0.1305296 0.00000001159 0.9914931004213 0.1301592555944 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_7 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4346887820525):ℝ):ℂ) + (((-0.9005807363883):ℝ):ℂ) * I)‖ ≤ 0.00000011607 := by
  have hl := lg_7
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.153230212663278588 27.153230226617306496 (-2.020489) 0.00000001606 (-0.4346887820525) (-0.9005807363883) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_8 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7369878317874):ℝ):ℂ) + ((0.6759060110448:ℝ):ℂ) * I)‖ ≤ 0.00000014677 := by
  have hl := lg_8
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.0165272617186 29.0165272826496 2.3993993 0.00000004676 (-0.7369878317874) 0.6759060110448 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_9 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7276854924322:ℝ):ℂ) + ((0.6859109447324:ℝ):ℂ) * I)‖ ≤ 0.00000012297 := by
  have hl := lg_9
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.660071744895040912 30.66007175884906882 0.7558548 0.00000002296 0.7276854924322 0.6859109447324 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_10 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7555219190011:ℝ):ℂ) + (((-0.6551233699914):ℝ):ℂ) * I)‖ ≤ 0.00000015916 := by
  have hl := lg_10
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.130272376757072386 32.13027239768808634 (-0.7143459) 0.00000005915 0.7555219190011 (-0.6551233699914) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_11 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4560109120567):ℝ):ℂ) + (((-0.8899741839404):ℝ):ℂ) * I)‖ ≤ 0.00000011079 := by
  have hl := lg_11
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.460230625746609482 33.46023064667763739 (-2.0443041) 0.00000001078 (-0.4560109120567) (-0.8899741839404) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_12 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9931786863288):ℝ):ℂ) + ((0.1166023009017:ℝ):ℂ) * I)‖ ≤ 0.00000015813 := by
  have hl := lg_12
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.674387380259920456 34.67438740119093441 3.0247245 0.00000005812 (-0.9931786863288) 0.1166023009017 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_13 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3306688201445):ℝ):ℂ) + ((0.9437468576807:ℝ):ℂ) * I)‖ ≤ 0.00000011996 := by
  have hl := lg_13
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.7913033231364418 35.791303344067469708 1.9078085 0.00000001995 (-0.3306688201445) 0.9437468576807 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_14 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6419895991953:ℝ):ℂ) + ((0.7667133457329:ℝ):ℂ) * I)‖ ≤ 0.00000014444 := by
  have hl := lg_14
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.825405966569478588 36.825405987500506496 0.8737059 0.00000004443 0.6419895991953 0.7667133457329 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_15 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9960402734877:ℝ):ℂ) + (((-0.0889031697444):ℝ):ℂ) * I)‖ ≤ 0.00000014779 := by
  have hl := lg_15
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.788132495298392842 37.78813251622942075 (-0.0890207) 0.00000004778 0.9960402734877 (-0.0889031697444) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_16 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5490315821443:ℝ):ℂ) + (((-0.8358016043345):ℝ):ℂ) * I)‖ ≤ 0.00000012747 := by
  have hl := lg_16
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.6887030156248 38.6887030435328 (-0.9895912) 0.00000002746 0.5490315821443 (-0.8358016043345) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_17 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.261668829623):ℝ):ℂ) + (((-0.9651577195476):ℝ):ℂ) * I)‖ ≤ 0.00000015464 := by
  have hl := lg_17
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.534658988451320036 39.53465901635933399 (-1.8355472) 0.00000005463 (-0.261668829623) (-0.9651577195476) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_18 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8734967484722):ℝ):ℂ) + (((-0.4868299809151):ℝ):ℂ) * I)‖ ≤ 0.00000014429 := by
  have hl := lg_18
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.332247498801240912 40.33224751973226882 (-2.6331357) 0.00000004428 (-0.8734967484722) (-0.4868299809151) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_19 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9698950010385):ℝ):ℂ) + ((0.2435234828294:ℝ):ℂ) * I)‖ ≤ 0.00000014587 := by
  have hl := lg_19
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.086701504406658262 41.086701525337700124 2.8955956 0.00000004586 (-0.9698950010385) 0.2435234828294 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_20 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5720907286327):ℝ):ℂ) + ((0.820190342666:ℝ):ℂ) * I)‖ ≤ 0.00000011961 := by
  have hl := lg_20
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.802448130663272386 41.80244815857128634 2.179849 0.0000000196 (-0.5720907286327) 0.820190342666 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_21 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0717036412061:ℝ):ℂ) + ((0.9974259811323:ℝ):ℂ) * I)‖ ≤ 0.0000001558 := by
  have hl := lg_21
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.483266085110799044 42.483266106041840906 1.4990311 0.00000005579 0.0717036412061 0.9974259811323 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_22 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.66006518177:ℝ):ℂ) + ((0.7512083305015:ℝ):ℂ) * I)‖ ≤ 0.00000015732 := by
  have hl := lg_22
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.132406379652809482 43.13240640756083739 0.8498908 0.00000005731 0.66006518177 0.7512083305015 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_23 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9737550273516:ℝ):ℂ) + ((0.2275986526927:ℝ):ℂ) * I)‖ ≤ 0.00000015223 := by
  have hl := lg_23
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.752686274566213164 43.752686302474255026 0.2296109 0.00000005222 0.9737550273516 0.2275986526927 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_24 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9343855102909:ℝ):ℂ) + (((-0.3562635515435):ℝ):ℂ) * I)‖ ≤ 0.00000011611 := by
  have hl := lg_24
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.346563134166120456 44.34656316207413441 (-0.364266) 0.0000000161 0.9343855102909 (-0.3562635515435) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_25 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5947062613039:ℝ):ℂ) + (((-0.803943071844):ℝ):ℂ) * I)‖ ≤ 0.00000012337 := by
  have hl := lg_25
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.916193245701744772 44.91619327360977268 (-0.9338961) 0.00000002336 0.5947062613039 (-0.803943071844) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_26 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0894945298391:ℝ):ℂ) + (((-0.9959873137389):ℝ):ℂ) * I)‖ ≤ 0.00000015471 := by
  have hl := lg_26
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.4634790770426418 45.463479104950669708 (-1.4811819) 0.0000000547 0.0894945298391 (-0.9959873137389) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_27 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4232361386631):ℝ):ℂ) + (((-0.9060194097953):ℝ):ℂ) * I)‖ ≤ 0.00000013293 := by
  have hl := lg_27
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.990107617342561368 45.99010763827360323 (-2.0078105) 0.00000003292 (-0.4232361386631) (-0.9060194097953) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_28 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8101970873433):ℝ):ℂ) + (((-0.586157555276):ℝ):ℂ) * I)‖ ≤ 0.0000001298 := by
  have hl := lg_28
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.497581720475678588 46.497581748383706496 (-2.5152846) 0.00000002979 (-0.8101970873433) (-0.586157555276) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_29 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9906787591448):ℝ):ℂ) + (((-0.1362189258688):ℝ):ℂ) * I)‖ ≤ 0.00000015315 := by
  have hl := lg_29
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.987245997122140168 46.98724602503018203 (-3.0049489) 0.00000005314 (-0.9906787591448) (-0.1362189258688) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_30 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9439430158328):ℝ):ℂ) + ((0.3301084407769:ℝ):ℂ) * I)‖ ≤ 0.00000011969 := by
  have hl := lg_30
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.460308249204592842 47.46030827711262075 2.8051742 0.00000001968 (-0.9439430158328) 0.3301084407769 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_31 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7010213472764):ℝ):ℂ) + ((0.7131402881894:ℝ):ℂ) * I)‖ ≤ 0.00000012058 := by
  have hl := lg_31
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.917857436876595302 47.917857464784637164 2.347625 0.00000002057 (-0.7010213472764) 0.7131402881894 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_32 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3276426072866):ℝ):ℂ) + ((0.9448017368149:ℝ):ℂ) * I)‖ ≤ 0.00000014699 := by
  have hl := lg_32
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.360878769531 48.360878804416 1.9046037 0.00000004698 (-0.3276426072866) 0.9448017368149 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_33 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0954349622119:ℝ):ℂ) + ((0.9954356674278:ℝ):ℂ) * I)‖ ≤ 0.00000015926 := by
  have hl := lg_33
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.790266498194129938 48.7902665261021718 1.4752159 0.00000005925 0.0954349622119 0.9954356674278 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_34 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4900513208159:ℝ):ℂ) + ((0.8716935831854:ℝ):ℂ) * I)‖ ≤ 0.00000011982 := by
  have hl := lg_34
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.206834742357520036 49.20683477724253399 1.0586477 0.00000001981 0.4900513208159 0.8716935831854 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_35 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7935620193795:ℝ):ℂ) + ((0.6084893765698:ℝ):ℂ) * I)‖ ≤ 0.00000012194 := by
  have hl := lg_35
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.611326835514150974 49.611326863422192836 0.6541556 0.00000002193 0.7935620193795 0.6084893765698 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_36 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9661171363662:ℝ):ℂ) + ((0.2581040077557:ℝ):ℂ) * I)‖ ≤ 0.00000012319 := by
  have hl := lg_36
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.004423252707440912 50.00442328061546882 0.2610592 0.00000002318 0.9661171363662 0.2581040077557 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_37 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9926562725281:ℝ):ℂ) + (((-0.1209691060171):ℝ):ℂ) * I)‖ ≤ 0.00000011892 := by
  have hl := lg_37
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.386748538528383668 50.38674856643642553 (-0.1212661) 0.00000001891 0.9926562725281 (-0.1209691060171) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_38 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8807300966224:ℝ):ℂ) + (((-0.4736185141055):ℝ):ℂ) * I)‖ ≤ 0.0000001288 := by
  have hl := lg_38
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.758877258312858262 50.758877286220900124 (-0.4933948) 0.00000002879 0.8807300966224 (-0.4736185141055) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_39 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6555717525899:ℝ):ℂ) + (((-0.7551328871173):ℝ):ℂ) * I)‖ ≤ 0.00000016187 := by
  have hl := lg_39
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.121339195583962256 51.121339223492004118 (-0.8558568) 0.00000006186 0.6555717525899 (-0.7551328871173) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p954_40 : ‖exp (-((((((13954:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3538225908977:ℝ):ℂ) + (((-0.9353125542675):ℝ):ℂ) * I)‖ ≤ 0.00000016203 := by
  have hl := lg_40
  refine (ecis_approx ((((13954:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.474623884569472386 51.47462391945448634 (-1.2091414) 0.00000006202 0.3538225908977 (-0.9353125542675) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_2 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9642515040307):ℝ):ℂ) + ((0.2649887483013:ℝ):ℂ) * I)‖ ≤ 0.00000014506 := by
  have hl := lg_2
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.6929701693152 9.6929701763072 2.8734004 0.00000004505 (-0.9642515040307) 0.2649887483013 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_3 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9410859180666):ℝ):ℂ) + (((-0.3381675540837):ℝ):ℂ) * I)‖ ≤ 0.00000013375 := by
  have hl := lg_3
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.362994241099765376 15.36299424809177936 (-2.7966236) 0.00000003374 (-0.9410859180666) (-0.3381675540837) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_4 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8595619811857:ℝ):ℂ) + (((-0.5110315063674):ℝ):ℂ) * I)‖ ≤ 0.00000013109 := by
  have hl := lg_4
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.3859403386304 19.3859403526144 (-0.5363844) 0.00000003108 0.8595619811857 (-0.5110315063674) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_5 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8701788478266):ℝ):ℂ) + ((0.4927360071145:ℝ):ℂ) * I)‖ ≤ 0.00000014549 := by
  have hl := lg_5
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.506379760208298656 22.50637977419231264 2.6263615 0.00000004548 (-0.8701788478266) 0.4927360071145 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_6 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9970541090071:ℝ):ℂ) + ((0.0767013931553:ℝ):ℂ) * I)‖ ≤ 0.00000011832 := by
  have hl := lg_6
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.055964410414965376 25.05596442439897936 0.0767768 0.00000001831 0.9970541090071 0.0767013931553 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_7 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.486491918413):ℝ):ℂ) + (((-0.8736850767371):ℝ):ℂ) * I)‖ ≤ 0.00000011161 := by
  have hl := lg_7
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.211607517119341248 27.211607531103369216 (-2.0788663) 0.0000000116 (-0.486491918413) (-0.8736850767371) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_8 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6934163339644):ℝ):ℂ) + ((0.7205371522474:ℝ):ℂ) * I)‖ ≤ 0.00000012797 := by
  have hl := lg_8
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.0789105079456 29.0789105289216 2.337016 0.00000002796 (-0.6934163339644) 0.7205371522474 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_9 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.77128547882:ℝ):ℂ) + ((0.6364893637456:ℝ):ℂ) * I)‖ ≤ 0.00000015371 := by
  have hl := lg_9
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.725988482199530752 30.72598849618355872 0.689938 0.0000000537 0.77128547882 0.6364893637456 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_10 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7085017701202:ℝ):ℂ) + (((-0.7057090347562):ℝ):ℂ) * I)‖ ≤ 0.00000011462 := by
  have hl := lg_10
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.199349929523498656 32.19934995049951264 (-0.7834234) 0.00000001461 0.7085017701202 (-0.7057090347562) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_11 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5187982914304):ℝ):ℂ) + (((-0.8548966796063):ℝ):ℂ) * I)‖ ≤ 0.00000015201 := by
  have hl := lg_11
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.532167483907165472 33.53216750488319344 (-2.116241) 0.000000052 (-0.5187982914304) (-0.8548966796063) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_12 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9817359493647):ℝ):ℂ) + ((0.1902485884029:ℝ):ℂ) * I)‖ ≤ 0.00000015764 := by
  have hl := lg_12
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.748934579730165376 34.74893460070617936 2.9501773 0.00000005763 (-0.9817359493647) 0.1902485884029 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_13 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2571420845184):ℝ):ℂ) + ((0.9663736070321:ℝ):ℂ) * I)‖ ≤ 0.00000013926 := by
  have hl := lg_13
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.8682518038368928 35.868251824812920768 1.83086 0.00000003925 (-0.2571420845184) 0.9663736070321 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_14 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7006172790797:ℝ):ℂ) + ((0.7135372647977:ℝ):ℂ) * I)‖ ≤ 0.00000015666 := by
  have hl := lg_14
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.904577686434541248 36.904577707410569216 0.7945341 0.00000005665 0.7006172790797 0.7135372647977 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_15 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9855403734192:ℝ):ℂ) + (((-0.1694407635744):ℝ):ℂ) * I)‖ ≤ 0.00000014178 := by
  have hl := lg_15
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.869374001308064032 37.869374022284092 (-0.1702622) 0.00000004177 0.9855403734192 (-0.1694407635744) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_16 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4776935989998:ℝ):ℂ) + (((-0.8785265081229):ℝ):ℂ) * I)‖ ≤ 0.00000016217 := by
  have hl := lg_16
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.7718806772608 38.7718807052288 (-1.0727688) 0.00000006216 0.4776935989998 (-0.8785265081229) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_17 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3426603918526):ℝ):ℂ) + (((-0.9394593423098):ℝ):ℂ) * I)‖ ≤ 0.00000015435 := by
  have hl := lg_17
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.619655388741813056 39.61965541670982704 (-1.9205436) 0.00000005434 (-0.3426603918526) (-0.9394593423098) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_18 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9123756590333):ℝ):ℂ) + (((-0.4093539503556):ℝ):ℂ) * I)‖ ≤ 0.00000012943 := by
  have hl := lg_18
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.418958651514730752 40.41895867249075872 (-2.7198468) 0.00000002942 (-0.9123756590333) (-0.4093539503556) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_19 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9446303225226):ℝ):ℂ) + ((0.3281364862081:ℝ):ℂ) * I)‖ ≤ 0.00000014449 := by
  have hl := lg_19
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.175034673758256352 41.175034694734298304 2.8072625 0.00000004448 (-0.9446303225226) 0.3281364862081 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_20 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4961689436392):ℝ):ℂ) + ((0.8682259955575:ℝ):ℂ) * I)‖ ≤ 0.00000015143 := by
  have hl := lg_20
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.892320098838698656 41.89232012680671264 2.089977 0.00000005142 (-0.4961689436392) 0.8682259955575 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_21 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1623787552626:ℝ):ℂ) + ((0.9867285036115:ℝ):ℂ) * I)‖ ≤ 0.00000012895 := by
  have hl := lg_21
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.574601758219106624 42.574601779195148576 1.4076954 0.00000002894 0.1623787552626 0.9867285036115 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_22 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7267899653282:ℝ):ℂ) + ((0.6868597719318:ℝ):ℂ) * I)‖ ≤ 0.00000013095 := by
  have hl := lg_22
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.225137653222365472 43.22513768119039344 0.7571595 0.00000003094 0.7267899653282 0.6868597719318 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_23 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9908276971966:ℝ):ℂ) + ((0.1351313230455:ℝ):ℂ) * I)‖ ≤ 0.00000014926 := by
  have hl := lg_23
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.846751101012894144 43.846751128980936096 0.135546 0.00000004925 0.9908276971966 0.1351313230455 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_24 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8962266337722:ℝ):ℂ) + (((-0.4435964617954):ℝ):ℂ) * I)‖ ≤ 0.00000012677 := by
  have hl := lg_24
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.441904749045365376 44.44190477701337936 (-0.4596076) 0.00000002676 0.8962266337722 (-0.4435964617954) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_25 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5144223748938:ℝ):ℂ) + (((-0.8575369497629):ℝ):ℂ) * I)‖ ≤ 0.00000012986 := by
  have hl := lg_25
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.012759520416597312 45.01275954838462528 (-1.0304624) 0.00000002985 0.5144223748938 (-0.8575369497629) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_26 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0081283836946):ℝ):ℂ) + (((-0.9999669641435):ℝ):ℂ) * I)‖ ≤ 0.00000015088 := by
  have hl := lg_26
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.5612219731520928 45.561222001120120768 (-1.5789248) 0.00000005087 (-0.0081283836946) (-0.9999669641435) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_27 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.510605851576):ℝ):ℂ) + (((-0.8598149012024):ℝ):ℂ) * I)‖ ≤ 0.00000012697 := by
  have hl := lg_27
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.088982723299296128 46.08898274427533808 (-2.1066856) 0.00000002696 (-0.510605851576) (-0.8598149012024) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_28 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8646505580576):ℝ):ℂ) + (((-0.502373777547):ℝ):ℂ) * I)‖ ≤ 0.00000013348 := by
  have hl := lg_28
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.597547855749741248 46.597547883717769216 (-2.6152507) 0.00000003347 (-0.8646505580576) (-0.502373777547) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_29 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993654981585):ℝ):ℂ) + (((-0.0356174183012):ℝ):ℂ) * I)‖ ≤ 0.00000014972 := by
  have hl := lg_29
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.088264871990540928 47.08826489995858288 (-3.1059677) 0.00000004971 (-0.9993654981585) (-0.0356174183012) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
