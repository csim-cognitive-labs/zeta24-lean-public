/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b2left (b2), angles 1

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

lemma cs_b2left_v16p487_2 : ‖exp (-((((((16487:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4189996597208:ℝ):ℂ) + ((0.9079863904012:ℝ):ℂ) * I)‖ ≤ 0.00000015277 := by
  have hl := lg_2
  refine (ecis_approx ((((16487:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.4279175616061 11.4279175698496 1.138453 0.00000005276 0.4189996597208 0.9079863904012 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p487_3 : ‖exp (-((((((16487:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7406661015452:ℝ):ℂ) + ((0.6718732961071:ℝ):ℂ) * I)‖ ≤ 0.00000012257 := by
  have hl := lg_3
  refine (ecis_approx ((((16487:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.112820798985399868 18.112820807228916355 0.7367351 0.00000002256 0.7406661015452 0.6718732961071 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p487_4 : ‖exp (-((((((16487:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6488786463951):ℝ):ℂ) + ((0.7608919123211:ℝ):ℂ) * I)‖ ≤ 0.000000111 := by
  have hl := lg_4
  refine (ecis_approx ((((16487:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.8558351232122 22.8558351396992 2.2769061 0.00000001099 (-0.6488786463951) 0.7608919123211 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p487_5 : ‖exp (-((((((16487:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1679351799794:ℝ):ℂ) + (((-0.9857980398262):ℝ):ℂ) * I)‖ ≤ 0.00000014151 := by
  have hl := lg_5
  refine (ecis_approx ((((16487:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.534802853729563783 26.53480287021658027 (-1.4020616) 0.0000000415 0.1679351799794 (-0.9857980398262) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p487_6 : ‖exp (-((((((16487:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2997130598281):ℝ):ℂ) + ((0.9540293925067:ℝ):ℂ) * I)‖ ≤ 0.0000001412 := by
  have hl := lg_6
  refine (ecis_approx ((((16487:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.540738360591499868 29.540738377078516355 1.8751882 0.00000004119 (-0.2997130598281) 0.9540293925067 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p487_7 : ‖exp (-((((((16487:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.786117590205:ℝ):ℂ) + (((-0.6180769647627):ℝ):ℂ) * I)‖ ≤ 0.00000011701 := by
  have hl := lg_7
  refine (ecis_approx ((((16487:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.082220618903502514 32.082220635390535488 (-0.6662941) 0.000000017 0.786117590205 (-0.6180769647627) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p487_8 : ‖exp (-((((((16487:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9627594309706):ℝ):ℂ) + (((-0.2703595343879):ℝ):ℂ) * I)‖ ≤ 0.00000015109 := by
  have hl := lg_8
  refine (ecis_approx ((((16487:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.2837526848183 34.2837527095488 (-2.8678262) 0.00000005108 (-0.9627594309706) (-0.2703595343879) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p487_9 : ‖exp (-((((((16487:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0971725479564:ℝ):ℂ) + ((0.9952675499199:ℝ):ℂ) * I)‖ ≤ 0.00000014512 := by
  have hl := lg_9
  refine (ecis_approx ((((16487:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.225641597970799736 36.22564161445783271 1.4734702 0.00000004511 0.0971725479564 0.9952675499199 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p487_10 : ‖exp (-((((((16487:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.965455987113:ℝ):ℂ) + (((-0.2605661853497):ℝ):ℂ) * I)‖ ≤ 0.00000012776 := by
  have hl := lg_10
  refine (ecis_approx ((((16487:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.962720415335663783 37.96272044006618027 (-0.2636086) 0.00000002775 0.965455987113 (-0.2605661853497) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p908_2 : ‖exp (-((((((16908:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6625051410374:ℝ):ℂ) + ((0.7490573663606:ℝ):ℂ) * I)‖ ≤ 0.00000011862 := by
  have hl := lg_2
  refine (ecis_approx ((((16908:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.7197325245124 11.7197325329664 0.8466381 0.00000001861 0.6625051410374 0.7490573663606 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p908_3 : ‖exp (-((((((16908:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9626369010049:ℝ):ℂ) + ((0.2707954889277:ℝ):ℂ) * I)‖ ≤ 0.00000014915 := by
  have hl := lg_3
  refine (ecis_approx ((((16908:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.575336572405236912 18.57533658085925382 0.2742193 0.00000004914 0.9626369010049 0.2707954889277 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p908_4 : ‖exp (-((((((16908:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1221738761982):ℝ):ℂ) + ((0.9925087122913:ℝ):ℂ) * I)‖ ≤ 0.00000013723 := by
  have hl := lg_4
  refine (ecis_approx ((((16908:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.4394650490248 23.4394650659328 1.6932762 0.00000003722 (-0.1221738761982) 0.9925087122913 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p908_5 : ‖exp (-((((((16908:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4871633763314):ℝ):ℂ) + (((-0.8733108523061):ℝ):ℂ) * I)‖ ≤ 0.00000011409 := by
  have hl := lg_5
  refine (ecis_approx ((((16908:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.212376214645445772 27.21237623155346268 (-2.079635) 0.00000001408 (-0.4871633763314) (-0.8733108523061) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v17p47_2 : ‖exp (-((((((17470:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8973408555682:ℝ):ℂ) + ((0.4413381797762:ℝ):ℂ) * I)‖ ≤ 0.00000013423 := by
  have hl := lg_2
  refine (ecis_approx ((((17470:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.109281239841 12.109281248576 0.4570894 0.00000003422 0.8973408555682 0.4413381797762 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v17p47_3 : ‖exp (-((((((17470:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.941682412553:ℝ):ℂ) + (((-0.3365029478154):ℝ):ℂ) * I)‖ ≤ 0.00000014306 := by
  have hl := lg_3
  refine (ecis_approx ((((17470:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.19275667849062508 19.19275668722564255 (-0.3432008) 0.00000004305 0.941682412553 (-0.3365029478154) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v17p47_4 : ‖exp (-((((((17470:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6104413013497:ℝ):ℂ) + ((0.7920614986265:ℝ):ℂ) * I)‖ ≤ 0.00000014905 := by
  have hl := lg_4
  refine (ecis_approx ((((17470:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.218562479682 24.218562497152 0.9141787 0.00000004904 0.6104413013497 0.7920614986265 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v17p47_5 : ‖exp (-((((((17470:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9876297772669):ℝ):ℂ) + (((-0.1568037712334):ℝ):ℂ) * I)‖ ≤ 0.00000010991 := by
  have hl := lg_5
  refine (ecis_approx ((((17470:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.11688032114123123 28.1168803386112487 (-2.9841391) 0.0000000099 (-0.9876297772669) (-0.1568037712334) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p032_2 : ‖exp (-((((((18032:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9977199938536:ℝ):ℂ) + ((0.067489361123:ℝ):ℂ) * I)‖ ≤ 0.00000014984 := by
  have hl := lg_2
  refine (ecis_approx ((((18032:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.4988299551696 12.4988299641856 0.0675407 0.00000004983 0.9977199938536 0.067489361123 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p032_3 : ‖exp (-((((((18032:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5730112395096:ℝ):ℂ) + (((-0.8195475089314):ℝ):ℂ) * I)‖ ≤ 0.00000013698 := by
  have hl := lg_3
  refine (ecis_approx ((((18032:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.810176784576013248 19.81017679359203128 (-0.9606209) 0.00000003697 0.5730112395096 (-0.8195475089314) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p032_4 : ‖exp (-((((((18032:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9908903857375:ℝ):ℂ) + ((0.1346708708407:ℝ):ℂ) * I)‖ ≤ 0.00000011839 := by
  have hl := lg_4
  refine (ecis_approx ((((18032:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.9976599103392 24.9976599283712 0.1350813 0.00000001838 0.9908903857375 0.1346708708407 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p032_5 : ‖exp (-((((((18032:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7336961403839):ℝ):ℂ) + ((0.6794777211621:ℝ):ℂ) * I)‖ ≤ 0.00000010979 := by
  have hl := lg_5
  refine (ecis_approx ((((18032:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.021384427637016688 29.02138444566903472 2.3945421 0.00000000978 (-0.7336961403839) 0.6794777211621 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p594_2 : ‖exp (-((((((18594:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9486018235177:ℝ):ℂ) + (((-0.3164720847389):ℝ):ℂ) * I)‖ ≤ 0.00000014388 := by
  have hl := lg_2
  refine (ecis_approx ((((18594:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.8883786704982 12.8883786797952 (-0.3220081) 0.00000004387 0.9486018235177 (-0.3164720847389) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p594_3 : ‖exp (-((((((18594:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0072446098322):ℝ):ℂ) + (((-0.9999737574697):ℝ):ℂ) * I)‖ ≤ 0.00000013089 := by
  have hl := lg_3
  refine (ecis_approx ((((18594:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.427596890661401416 20.42759689995842001 (-1.578041) 0.00000003088 (-0.0072446098322) (-0.9999737574697) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p594_4 : ‖exp (-((((((18594:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7996908992033:ℝ):ℂ) + (((-0.6004119133824):ℝ):ℂ) * I)‖ ≤ 0.00000013089 := by
  have hl := lg_4
  refine (ecis_approx ((((18594:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.7767573409964 25.7767573595904 (-0.6440161) 0.00000003088 0.7996908992033 (-0.6004119133824) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p594_5 : ‖exp (-((((((18594:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0806705723619:ℝ):ℂ) + ((0.9967408182445:ℝ):ℂ) * I)‖ ≤ 0.00000011684 := by
  have hl := lg_5
  refine (ecis_approx ((((18594:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.925888534132802146 29.92588855272682074 1.490038 0.00000001683 0.0806705723619 0.9967408182445 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p015_2 : ‖exp (-((((((19015:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8174519611749:ℝ):ℂ) + (((-0.5759967805217):ℝ):ℂ) * I)‖ ≤ 0.00000012857 := by
  have hl := lg_2
  refine (ecis_approx ((((19015:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.1801936334045 13.180193642912 (-0.613823) 0.00000002856 0.8174519611749 (-0.5759967805217) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p015_3 : ‖exp (-((((((19015:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4526726287272):ℝ):ℂ) + (((-0.8916767862833):ℝ):ℂ) * I)‖ ≤ 0.00000015206 := by
  have hl := lg_3
  refine (ecis_approx ((((19015:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.89011266408123846 20.890112673588757475 (-2.0405567) 0.00000005205 (-0.4526726287272) (-0.8916767862833) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p015_4 : ‖exp (-((((((19015:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3364554176572:ℝ):ℂ) + (((-0.9416993957358):ℝ):ℂ) * I)‖ ≤ 0.00000015712 := by
  have hl := lg_4
  refine (ecis_approx ((((19015:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.360387266809 26.360387285824 (-1.227646) 0.00000005711 0.3364554176572 (-0.9416993957358) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p015_5 : ‖exp (-((((((19015:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.687711262496:ℝ):ℂ) + ((0.7259843107369:ℝ):ℂ) * I)‖ ≤ 0.00000014086 := by
  have hl := lg_5
  refine (ecis_approx ((((19015:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.603461895048684135 30.60346191406370315 0.8124646 0.00000004085 0.687711262496 0.7259843107369 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p015_6 : ‖exp (-((((((19015:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8836411330788):ℝ):ℂ) + (((-0.4681648724881):ℝ):ℂ) * I)‖ ≤ 0.00000013843 := by
  have hl := lg_6
  refine (ecis_approx ((((19015:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.07030629748573846 34.070306316500757475 (-2.6543798) 0.00000003842 (-0.8836411330788) (-0.4681648724881) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p015_7 : ‖exp (-((((((19015:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7663665767926:ℝ):ℂ) + ((0.6424035102451:ℝ):ℂ) * I)‖ ≤ 0.00000015035 := by
  have hl := lg_7
  refine (ecis_approx ((((19015:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.00148147440104933 37.00148149341608736 0.6976304 0.00000005034 0.7663665767926 0.6424035102451 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p015_8 : ‖exp (-((((((19015:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2673797755105):ℝ):ℂ) + (((-0.9635912285023):ℝ):ℂ) * I)‖ ≤ 0.00000014288 := by
  have hl := lg_8
  refine (ecis_approx ((((19015:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.5405809002135 39.540580928736 (-1.8414691) 0.00000004287 (-0.2673797755105) (-0.9635912285023) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p015_9 : ‖exp (-((((((19015:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5901748958782):ℝ):ℂ) + ((0.8072754128944:ℝ):ℂ) * I)‖ ≤ 0.00000012211 := by
  have hl := lg_9
  refine (ecis_approx ((((19015:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.78022532816247692 41.78022534717751495 2.2020718 0.0000000221 (-0.5901748958782) 0.8072754128944 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p015_10 : ‖exp (-((((((19015:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9803355459431:ℝ):ℂ) + ((0.1973378254678:ℝ):ℂ) * I)‖ ≤ 0.00000012182 := by
  have hl := lg_10
  refine (ecis_approx ((((19015:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.783655528453184135 43.78365555697570315 0.1986416 0.00000002181 0.9803355459431 0.1973378254678 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p436_2 : ‖exp (-((((((19436:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.617183715006:ℝ):ℂ) + (((-0.7868190782711):ℝ):ℂ) * I)‖ ≤ 0.00000011806 := by
  have hl := lg_2
  refine (ecis_approx ((((19436:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.4720085963108 13.4720086060288 (-0.905638) 0.00000001805 0.617183715006 (-0.7868190782711) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p436_3 : ‖exp (-((((((19436:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8029786368086):ℝ):ℂ) + (((-0.5960078093269):ℝ):ℂ) * I)‖ ≤ 0.0000001257 := by
  have hl := lg_3
  refine (ecis_approx ((((19436:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.352628437501075504 21.35262844721909494 (-2.5030725) 0.00000002569 (-0.8029786368086) (-0.5960078093269) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p436_4 : ‖exp (-((((((19436:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2381685238629):ℝ):ℂ) + (((-0.9712238435293):ℝ):ℂ) * I)‖ ≤ 0.00000013611 := by
  have hl := lg_4
  refine (ecis_approx ((((19436:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.9440171926216 26.9440172120576 (-1.811276) 0.0000000361 (-0.2381685238629) (-0.9712238435293) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p436_5 : ‖exp (-((((((19436:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9909159553172:ℝ):ℂ) + ((0.1344825992377:ℝ):ℂ) * I)‖ ≤ 0.00000013952 := by
  have hl := lg_5
  refine (ecis_approx ((((19436:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.281035255964566124 31.28103527540058556 0.1348913 0.00000003951 0.9909159553172 0.1344825992377 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p436_6 : ‖exp (-((((((19436:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.964535651352):ℝ):ℂ) + ((0.2639526037411:ℝ):ℂ) * I)‖ ≤ 0.00000011019 := by
  have hl := lg_6
  refine (ecis_approx ((((19436:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.824637033811875504 34.82463705324789494 2.8744748 0.00000001018 (-0.964535651352) 0.2639526037411 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p436_7 : ‖exp (-((((((19436:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9926160924679:ℝ):ℂ) + (((-0.1212983634418):ℝ):ℂ) * I)‖ ≤ 0.00000012331 := by
  have hl := lg_7
  refine (ecis_approx ((((19436:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.820709646934461992 37.820709666370500864 (-0.1215978) 0.0000000233 0.9926160924679 (-0.1212983634418) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p436_8 : ‖exp (-((((((19436:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9111711836764):ℝ):ℂ) + (((-0.4120280013634):ℝ):ℂ) * I)‖ ≤ 0.00000015416 := by
  have hl := lg_8
  refine (ecis_approx ((((19436:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.4160257889324 40.4160258180864 (-2.716914) 0.00000005415 (-0.9111711836764) (-0.4120280013634) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p436_9 : ‖exp (-((((((19436:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2895493892475:ℝ):ℂ) + ((0.9571630745:ℝ):ℂ) * I)‖ ≤ 0.0000001442 := by
  have hl := lg_9
  refine (ecis_approx ((((19436:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.705256875002151008 42.70525689443818988 1.2770403 0.00000004419 0.2895493892475 0.9571630745 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p436_10 : ‖exp (-((((((19436:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7173906653371:ℝ):ℂ) + (((-0.6966711084057):ℝ):ℂ) * I)‖ ≤ 0.00000013119 := by
  have hl := lg_10
  refine (ecis_approx ((((19436:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.753043852275366124 44.75304388142938556 (-0.7707467) 0.00000003118 0.7173906653371 (-0.6966711084057) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p857_2 : ‖exp (-((((((19857:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3647305732287:ℝ):ℂ) + (((-0.9311131021268):ℝ):ℂ) * I)‖ ≤ 0.0000001548 := by
  have hl := lg_2
  refine (ecis_approx ((((19857:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.7638235592171 13.7638235691456 (-1.1974529) 0.00000005479 0.3647305732287 (-0.9311131021268) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p857_3 : ‖exp (-((((((19857:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9845511759917):ℝ):ℂ) + (((-0.1750970630736):ℝ):ℂ) * I)‖ ≤ 0.00000011063 := by
  have hl := lg_3
  refine (ecis_approx ((((19857:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.815144210920912548 21.815144220849432405 (-2.9655883) 0.00000001062 (-0.9845511759917) (-0.1750970630736) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p857_4 : ‖exp (-((((((19857:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7339432858209):ℝ):ℂ) + (((-0.6792107575475):ℝ):ℂ) * I)‖ ≤ 0.0000001103 := by
  have hl := lg_4
  refine (ecis_approx ((((19857:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.5276471184342 27.5276471382912 (-2.3949059) 0.00000001029 (-0.7339432858209) (-0.6792107575475) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p857_5 : ‖exp (-((((((19857:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8563266338433:ℝ):ℂ) + (((-0.5164346000905):ℝ):ℂ) * I)‖ ≤ 0.00000011903 := by
  have hl := lg_5
  refine (ecis_approx ((((19857:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.958608616880448113 31.95860863673746797 (-0.5426821) 0.00000001902 0.8563266338433 (-0.5164346000905) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p857_6 : ‖exp (-((((((19857:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5221310784577):ℝ):ℂ) + ((0.8528652513154:ℝ):ℂ) * I)‖ ≤ 0.00000014693 := by
  have hl := lg_6
  refine (ecis_approx ((((19857:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.578967770138012548 35.578967789995032405 2.1201441 0.00000004692 (-0.5221310784577) 0.8528652513154 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p857_7 : ‖exp (-((((((19857:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5891207809169:ℝ):ℂ) + (((-0.8080449897697):ℝ):ℂ) * I)‖ ≤ 0.00000012362 := by
  have hl := lg_7
  refine (ecis_approx ((((19857:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.639937819467874654 38.639937839324914368 (-0.940826) 0.00000002361 0.5891207809169 (-0.8080449897697) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p857_8 : ‖exp (-((((((19857:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9001135876683):ℝ):ℂ) + ((0.4356552871002:ℝ):ℂ) * I)‖ ≤ 0.00000015719 := by
  have hl := lg_8
  refine (ecis_approx ((((19857:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.2914706776513 41.2914707074368 2.6908265 0.00000005718 (-0.9001135876683) 0.4356552871002 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p857_9 : ‖exp (-((((((19857:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9386820393593:ℝ):ℂ) + ((0.3447840323801:ℝ):ℂ) * I)‖ ≤ 0.00000012843 := by
  have hl := lg_9
  refine (ecis_approx ((((19857:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.630288421841825096 43.63028844169886481 0.3520087 0.00000002842 0.9386820393593 0.3447840323801 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p857_10 : ‖exp (-((((((19857:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1685305185034):ℝ):ℂ) + (((-0.9856964361974):ℝ):ℂ) * I)‖ ≤ 0.00000015564 := by
  have hl := lg_10
  refine (ecis_approx ((((19857:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.722432176097548113 45.72243220588306797 (-1.740135) 0.00000005563 (-0.1685305185034) (-0.9856964361974) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_2 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1543821017875:ℝ):ℂ) + (((-0.9880112178754):ℝ):ℂ) * I)‖ ≤ 0.00000011675 := by
  have hl := lg_2
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.9821649210116 13.9821649310976 (-1.4157943) 0.00000001674 0.1543821017875 (-0.9880112178754) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_3 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9855748588317):ℝ):ℂ) + ((0.1692400581252:ℝ):ℂ) * I)‖ ≤ 0.00000014696 := by
  have hl := lg_3
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.161207081769484208 22.16120709185550438 2.9715341 0.00000004695 (-0.9855748588317) 0.1692400581252 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_4 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9523323332199):ℝ):ℂ) + (((-0.3050624967021):ℝ):ℂ) * I)‖ ≤ 0.00000013349 := by
  have hl := lg_4
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.9643298420232 27.9643298621952 (-2.8315886) 0.00000003348 (-0.9523323332199) (-0.3050624967021) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_5 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4978702792869:ℝ):ℂ) + (((-0.8672515119634):ℝ):ℂ) * I)‖ ≤ 0.00000014342 := by
  have hl := lg_5
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.465581559133423948 32.46558157930544412 (-1.049655) 0.00000004341 0.4978702792869 (-0.8672515119634) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_6 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.015055957918:ℝ):ℂ) + ((0.9998866526417:ℝ):ℂ) * I)‖ ≤ 0.00000014031 := by
  have hl := lg_6
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.143372002781084208 36.14337202295310438 1.5557398 0.0000000403 0.015055957918 0.9998866526417 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_7 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0170078067262:ℝ):ℂ) + (((-0.9998553567943):ℝ):ℂ) * I)‖ ≤ 0.00000012684 := by
  have hl := lg_7
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.252899516256532584 39.252899536428572928 (-1.5537877) 0.00000002683 0.0170078067262 (-0.9998553567943) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_8 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4484282297991):ℝ):ℂ) + ((0.8938188422241:ℝ):ℂ) * I)‖ ≤ 0.00000014305 := by
  have hl := lg_8
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.9464947630348 41.9464947932928 2.0358024 0.00000004304 (-0.4484282297991) 0.8938188422241 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_9 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.942715641086:ℝ):ℂ) + (((-0.3335973921539):ℝ):ℂ) * I)‖ ≤ 0.00000013347 := by
  have hl := lg_9
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.322414163538968416 44.32241418371100876 (-0.340117) 0.00000003346 0.942715641086 (-0.3335973921539) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_10 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7799919623973):ℝ):ℂ) + (((-0.6257895321538):ℝ):ℂ) * I)‖ ≤ 0.00000016016 := by
  have hl := lg_10
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.447746480145023948 46.44774651040304412 (-2.4654493) 0.00000006015 (-0.7799919623973) (-0.6257895321538) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_11 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3186858007041):ℝ):ℂ) + ((0.9478604118897:ℝ):ℂ) * I)‖ ≤ 0.00000013029 := by
  have hl := lg_11
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.370343427157847676 48.37034345741588802 1.895139 0.00000003028 (-0.3186858007041) 0.9478604118897 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_12 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9902235998418:ℝ):ℂ) + ((0.1394891476652:ℝ):ℂ) * I)‖ ≤ 0.00000013366 := by
  have hl := lg_12
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.125536923792684208 50.12553695405070438 0.1399455 0.00000003365 0.9902235998418 0.1394891476652 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_13 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0959723839933:ℝ):ℂ) + (((-0.9953839970135):ℝ):ℂ) * I)‖ ≤ 0.00000013447 := by
  have hl := lg_13
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.7401584229832524 51.740158453241292744 (-1.474676) 0.00000003446 0.0959723839933 (-0.9953839970135) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_14 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9852426076635):ℝ):ℂ) + (((-0.1711636751257):ℝ):ℂ) * I)‖ ≤ 0.00000012018 := by
  have hl := lg_14
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.235064437268132584 53.235064467526172928 (-2.969582) 0.00000002017 (-0.9852426076635) (-0.1711636751257) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p172_15 : ‖exp (-((((((20172:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3439147338536):ℝ):ℂ) + ((0.9390008817015:ℝ):ℂ) * I)‖ ≤ 0.00000012373 := by
  have hl := lg_15
  refine (ecis_approx ((((20172:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.626788640902908156 54.6267886711609485 1.9218791 0.00000002372 (-0.3439147338536) 0.9390008817015 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_2 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0632970300792):ℝ):ℂ) + (((-0.9979947324424):ℝ):ℂ) * I)‖ ≤ 0.00000013157 := by
  have hl := lg_2
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.2005062828061 14.2005062930496 (-1.6341357) 0.00000003156 (-0.0632970300792) (-0.9979947324424) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_3 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8697398695019):ℝ):ℂ) + ((0.4935104449869:ℝ):ℂ) * I)‖ ≤ 0.00000013416 := by
  have hl := lg_3
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.507269952618055868 22.507269962861576355 2.6254713 0.00000003415 (-0.8697398695019) 0.4935104449869 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_4 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9919869835025):ℝ):ℂ) + ((0.1263401129144:ℝ):ℂ) * I)‖ ≤ 0.00000015022 := by
  have hl := lg_4
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.4010125656122 28.4010125860992 3.014914 0.00000005021 (-0.9919869835025) 0.1263401129144 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_5 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0141678527711:ℝ):ℂ) + (((-0.9998996309369):ℝ):ℂ) * I)‖ ≤ 0.00000013453 := by
  have hl := lg_5
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.972554501386399783 32.97255452187342027 (-1.556628) 0.00000003452 0.0141678527711 (-0.9998996309369) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_6 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5475727752326:ℝ):ℂ) + ((0.8367580628975:ℝ):ℂ) * I)‖ ≤ 0.00000011285 := by
  have hl := lg_6
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.707776235424155868 36.707776255911176355 0.9913356 0.00000001284 0.5475727752326 0.8367580628975 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_7 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5612977859542):ℝ):ℂ) + (((-0.8276139169163):ℝ):ℂ) * I)‖ ≤ 0.00000013005 := by
  have hl := lg_7
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.865861213045190514 39.865861233532231488 (-2.1667494) 0.00000003004 (-0.5612977859542) (-0.8276139169163) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_8 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1888765973347:ℝ):ℂ) + ((0.9820008304371:ℝ):ℂ) * I)‖ ≤ 0.00000012891 := by
  have hl := lg_8
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.6015188484183 42.6015188791488 1.3807783 0.0000000289 0.1888765973347 0.9820008304371 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_9 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.512894801601:ℝ):ℂ) + (((-0.858451467755):ℝ):ℂ) * I)‖ ≤ 0.00000014504 := by
  have hl := lg_9
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.014539905236111736 45.01453992572315271 (-1.0322428) 0.00000004503 0.512894801601 (-0.858451467755) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_10 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9987913519368):ℝ):ℂ) + ((0.049151141609:ℝ):ℂ) * I)‖ ≤ 0.0000001575 := by
  have hl := lg_10
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.173060784192499783 47.17306081492302027 3.0924217 0.00000005749 (-0.9987913519368) 0.049151141609 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_11 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4177744052037:ℝ):ℂ) + ((0.9085507945936:ℝ):ℂ) * I)‖ ≤ 0.00000011961 := by
  have hl := lg_11
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.125680437843685571 49.125680468574226545 1.139802 0.0000000196 0.4177744052037 0.9085507945936 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_12 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8004204086762:ℝ):ℂ) + (((-0.5994390455873):ℝ):ℂ) * I)‖ ≤ 0.00000013922 := by
  have hl := lg_12
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.908282518230255868 50.908282548960776355 (-0.6428001) 0.00000003921 0.8004204086762 (-0.5994390455873) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_13 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.653227048062):ℝ):ℂ) + (((-0.7571620854632):ℝ):ℂ) * I)‖ ≤ 0.00000014365 := by
  have hl := lg_13
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.5481174703379879 52.548117501068528874 (-2.282635) 0.00000004364 (-0.653227048062) (-0.7571620854632) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_14 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7904259035918):ℝ):ℂ) + ((0.6125576633145:ℝ):ℂ) * I)‖ ≤ 0.00000016198 := by
  have hl := lg_14
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.066367495851290514 54.066367526581831488 2.4823003 0.00000006197 (-0.7904259035918) 0.6125576633145 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p487_15 : ‖exp (-((((((20487:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4811385654333:ℝ):ℂ) + ((0.8766445578755:ℝ):ℂ) * I)‖ ≤ 0.00000012013 := by
  have hl := lg_15
  refine (ecis_approx ((((20487:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.479824454004455651 55.479824484734996625 1.0688433 0.00000002012 0.4811385654333 0.8766445578755 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_2 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1849552958925):ℝ):ℂ) + (((-0.9827469351367):ℝ):ℂ) * I)‖ ≤ 0.00000012971 := by
  have hl := lg_2
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.3231933337192 14.3231933440512 (-1.7568227) 0.0000000297 (-0.1849552958925) (-0.9827469351367) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_3 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7579864546759):ℝ):ℂ) + ((0.6522702925107:ℝ):ℂ) * I)‖ ≤ 0.00000010929 := by
  have hl := lg_3
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.701724327666300896 22.70172433799832156 2.4310169 0.00000000928 (-0.7579864546759) 0.6522702925107 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_4 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.931583074379):ℝ):ℂ) + ((0.3635285069538:ℝ):ℂ) * I)‖ ≤ 0.00000015222 := by
  have hl := lg_4
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.6463866674384 28.6463866881024 2.7695399 0.00000005221 (-0.931583074379) 0.3635285069538 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_5 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.267408104977):ℝ):ℂ) + (((-0.9635833671205):ℝ):ℂ) * I)‖ ≤ 0.00000012412 := by
  have hl := lg_5
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.257425011795214776 33.25742503245923544 (-1.8414985) 0.00000002411 (-0.267408104977) (-0.9635833671205) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_6 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.781210239874:ℝ):ℂ) + ((0.6242680202574:ℝ):ℂ) * I)‖ ≤ 0.00000013899 := by
  have hl := lg_6
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.024917661385500896 37.02491768204952156 0.6741942 0.00000003898 0.781210239874 0.6242680202574 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_7 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8077816741522):ℝ):ℂ) + (((-0.5894817782183):ℝ):ℂ) * I)‖ ≤ 0.00000013376 := by
  have hl := lg_7
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.210287309335960208 40.210287330000001536 (-2.5111755) 0.00000003375 (-0.8077816741522) (-0.5894817782183) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_8 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5295578341356:ℝ):ℂ) + ((0.8482738356837:ℝ):ℂ) * I)‖ ≤ 0.00000014911 := by
  have hl := lg_8
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.9695800011576 42.9695800321536 1.0127171 0.0000000491 0.5295578341356 0.8482738356837 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_9 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1490869380624:ℝ):ℂ) + (((-0.9888240919896):ℝ):ℂ) * I)‖ ≤ 0.00000012575 := by
  have hl := lg_9
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.403448655332601792 45.40344867599664312 (-1.4211515) 0.00000002574 0.1490869380624 (-0.9888240919896) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_10 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.897500052408):ℝ):ℂ) + ((0.4410143487621:ℝ):ℂ) * I)‖ ≤ 0.00000011909 := by
  have hl := lg_10
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.580618345514414776 47.58061837651043544 2.6848641 0.00000001908 (-0.897500052408) 0.4410143487621 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_11 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7548476595437:ℝ):ℂ) + ((0.6559001531341:ℝ):ℂ) * I)‖ ≤ 0.00000015646 := by
  have hl := lg_11
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.550107900990965912 49.55010793198700724 0.7153745 0.00000005645 0.7548476595437 0.6559001531341 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_12 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4690084242226:ℝ):ℂ) + (((-0.8831936922376):ℝ):ℂ) * I)‖ ≤ 0.00000016235 := by
  have hl := lg_12
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.348110995104700896 51.34811102610072156 (-1.0826286) 0.00000006234 0.4690084242226 (-0.8831936922376) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_13 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9191175450487):ℝ):ℂ) + (((-0.3939834238163):ℝ):ℂ) * I)‖ ≤ 0.00000015098 := by
  have hl := lg_13
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.0021135064706488 53.002113537466690128 (-2.7366311) 0.00000005097 (-0.9191175450487) (-0.3939834238163) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_14 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4299079058485):ℝ):ℂ) + ((0.9028727443472:ℝ):ℂ) * I)‖ ≤ 0.00000012158 := by
  have hl := lg_14
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.533480643055160208 54.533480674051201536 2.0151871 0.00000002157 (-0.4299079058485) 0.9028727443472 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p664_15 : ‖exp (-((((((20664:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8312085261949:ℝ):ℂ) + ((0.5559607773764:ℝ):ℂ) * I)‖ ≤ 0.00000012517 := by
  have hl := lg_15
  refine (ecis_approx ((((20664:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.959149339461515672 55.959149370457557 0.5895184 0.00000002516 0.8312085261949 0.5559607773764 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_2 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2739731852037):ℝ):ℂ) + (((-0.9617373309734):ℝ):ℂ) * I)‖ ≤ 0.00000015286 := by
  have hl := lg_2
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.4146887615188 14.4146887719168 (-1.8483182) 0.00000005285 (-0.2739731852037) (-0.9617373309734) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_3 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6557712708523):ℝ):ℂ) + ((0.7549596282631:ℝ):ℂ) * I)‖ ≤ 0.00000013143 := by
  have hl := lg_3
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.846741149736178544 22.84674116013419934 2.2860001 0.00000003142 (-0.6557712708523) 0.7549596282631 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_4 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8498774364752):ℝ):ℂ) + ((0.5269804008657:ℝ):ℂ) * I)‖ ≤ 0.00000011288 := by
  have hl := lg_4
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.8293775230376 28.8293775438336 2.586549 0.00000001287 (-0.8498774364752) 0.5269804008657 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_5 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4645691191269):ℝ):ℂ) + (((-0.8855368617673):ℝ):ℂ) * I)‖ ≤ 0.00000011975 := by
  have hl := lg_5
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.469870816167890364 33.46987083696391116 (-2.0539443) 0.00000001974 (-0.4645691191269) (-0.8855368617673) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_6 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9057366017296:ℝ):ℂ) + ((0.4238410177028:ℝ):ℂ) * I)‖ ≤ 0.00000013184 := by
  have hl := lg_6
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.261429911254978544 37.26142993205099934 0.4376819 0.00000003183 0.9057366017296 0.4238410177028 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_7 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9310351646045):ℝ):ℂ) + (((-0.364929475527):ℝ):ℂ) * I)‖ ≤ 0.00000012668 := by
  have hl := lg_7
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.467147448942635912 40.467147469738677504 (-2.7680356) 0.00000002667 (-0.9310351646045) (-0.364929475527) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_8 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7396602852541:ℝ):ℂ) + ((0.6729804324182:ℝ):ℂ) * I)‖ ≤ 0.00000016551 := by
  have hl := lg_8
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.2440662845564 43.2440663157504 0.7382309 0.0000000655 0.7396602852541 0.6729804324182 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_9 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1399281725518):ℝ):ℂ) + (((-0.9901616567641):ℝ):ℂ) * I)‖ ≤ 0.0000001508 := by
  have hl := lg_9
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.693482299472357088 45.69348232026839868 (-1.7111852) 0.00000005079 (-0.1399281725518) (-0.9901616567641) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_10 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7243744405904):ℝ):ℂ) + ((0.6894067520638:ℝ):ℂ) * I)‖ ≤ 0.00000015146 := by
  have hl := lg_10
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.884559577686690364 47.88455960888071116 2.3809229 0.00000005145 (-0.7243744405904) 0.6894067520638 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_11 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9215072838824:ℝ):ℂ) + ((0.3883610765148:ℝ):ℂ) * I)‖ ≤ 0.00000015067 := by
  have hl := lg_11
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.866630076897412268 49.86663010809145386 0.3988524 0.00000005066 0.9215072838824 0.3883610765148 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_12 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1594762861118:ℝ):ℂ) + (((-0.9872017596054):ℝ):ℂ) * I)‖ ≤ 0.00000014655 := by
  have hl := lg_12
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.676118672773778544 51.67611870396779934 (-1.4106362) 0.00000004654 0.1594762861118 (-0.9872017596054) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_13 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9977971089024):ℝ):ℂ) + (((-0.0663394974858):ℝ):ℂ) * I)‖ ≤ 0.0000001359 := by
  have hl := lg_13
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.3406868215526332 53.340686852746674792 (-3.0752044) 0.00000003589 (-0.9977971089024) (-0.0663394974858) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_14 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.095887623125):ℝ):ℂ) + ((0.9953921657975:ℝ):ℂ) * I)‖ ≤ 0.00000015417 := by
  have hl := lg_14
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.881836210461435912 54.881836241655477504 1.6668315 0.00000005416 (-0.095887623125) 0.9953921657975 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_15 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9731956616336:ℝ):ℂ) + ((0.229978703748:ℝ):ℂ) * I)‖ ≤ 0.0000001325 := by
  have hl := lg_15
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.316611965904068908 56.3166119970981105 0.2320558 0.00000003249 0.9731956616336 0.229978703748 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_16 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4445833205521:ℝ):ℂ) + (((-0.8957375012172):ℝ):ℂ) * I)‖ ≤ 0.00000012307 := by
  have hl := lg_16
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.6587550460752 57.6587550876672 (-1.1100873) 0.00000002306 0.4445833205521 (-0.8957375012172) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_17 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7173843579294):ℝ):ℂ) + (((-0.6966776033227):ℝ):ℂ) * I)‖ ≤ 0.00000015836 := by
  have hl := lg_17
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.919504681369761464 58.91950472296178226 (-2.3708369) 0.00000005835 (-0.7173843579294) (-0.6966776033227) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_18 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9139388995057):ℝ):ℂ) + ((0.4058518052642:ℝ):ℂ) * I)‖ ≤ 0.0000001204 := by
  have hl := lg_18
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.108171060991157088 60.10817109218519868 2.723682 0.00000002039 (-0.9139388995057) 0.4058518052642 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_19 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0284999136418):ℝ):ℂ) + ((0.9995937949598:ℝ):ℂ) * I)‖ ≤ 0.00000015394 := by
  have hl := lg_19
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.232552994527795988 61.232553025721858376 1.5993001 0.00000005393 (-0.0284999136418) 0.9995937949598 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p796_20 : ‖exp (-((((((20796:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8614873824706:ℝ):ℂ) + ((0.5077789773553:ℝ):ℂ) * I)‖ ≤ 0.00000013261 := by
  have hl := lg_20
  refine (ecis_approx ((((20796:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.299248339205490364 62.29924838079751116 0.5326047 0.0000000326 0.8614873824706 0.5077789773553 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_2 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.360699034433):ℝ):ℂ) + (((-0.9326822645234):ℝ):ℂ) * I)‖ ≤ 0.00000012506 := by
  have hl := lg_2
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.5061841893184 14.5061841997824 (-1.9398136) 0.00000002505 (-0.360699034433) (-0.9326822645234) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_3 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5397894522239):ℝ):ℂ) + ((0.8418000637085:ℝ):ℂ) * I)‖ ≤ 0.00000015357 := by
  have hl := lg_3
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.991757971806056192 22.99175798227007712 2.1409833 0.00000005356 (-0.5397894522239) 0.8418000637085 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_4 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7397924082826):ℝ):ℂ) + ((0.6728351897872:ℝ):ℂ) * I)‖ ≤ 0.00000015728 := by
  have hl := lg_4
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.0123683786368 29.0123683995648 2.4035581 0.00000005727 (-0.7397924082826) 0.6728351897872 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_5 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6408413763217):ℝ):ℂ) + (((-0.7676733226954):ℝ):ℂ) * I)‖ ≤ 0.00000011537 := by
  have hl := lg_5
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.682316620540565952 33.68231664146858688 (-2.2663901) 0.00000001536 (-0.6408413763217) (-0.7676733226954) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_6 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9798335239155:ℝ):ℂ) + ((0.1998155785003:ℝ):ℂ) * I)‖ ≤ 0.00000013899 := by
  have hl := lg_6
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.497942161124456192 37.49794218205247712 0.2011697 0.00000003898 0.9798335239155 0.1998155785003 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_7 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.993198645731):ℝ):ℂ) + (((-0.1164321676827):ℝ):ℂ) * I)‖ ≤ 0.00000015454 := by
  have hl := lg_7
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.724007588549311616 40.724007609477353472 (-3.0248958) 0.00000005453 (-0.993198645731) (-0.1164321676827) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_8 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8943838110995:ℝ):ℂ) + ((0.4473003447833:ℝ):ℂ) * I)‖ ≤ 0.00000014911 := by
  have hl := lg_8
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.5185525679552 43.5185525993472 0.4637446 0.0000000491 0.8943838110995 0.4473003447833 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_9 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4172547788891):ℝ):ℂ) + (((-0.9087895518163):ℝ):ℂ) * I)‖ ≤ 0.0000001143 := by
  have hl := lg_9
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.983515943612112384 45.98351596454015424 (-2.0012188) 0.00000001429 (-0.4172547788891) (-0.9087895518163) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_10 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4848444210915):ℝ):ℂ) + ((0.8746004158076:ℝ):ℂ) * I)‖ ≤ 0.00000014759 := by
  have hl := lg_10
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.188500809858965952 48.18850084125098688 2.0769816 0.00000004758 (-0.4848444210915) 0.8746004158076 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_11 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9966127830196:ℝ):ℂ) + ((0.0822372222416:ℝ):ℂ) * I)‖ ≤ 0.00000012677 := by
  have hl := lg_11
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.183152252803858624 50.18315228419590048 0.0823302 0.00000002676 0.9966127830196 0.0822372222416 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_12 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1670605597384):ℝ):ℂ) + (((-0.9859466361722):ℝ):ℂ) * I)‖ ≤ 0.00000012441 := by
  have hl := lg_12
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.004126350442856192 52.00412638183487712 (-1.7386439) 0.0000000244 (-0.1670605597384) (-0.9859466361722) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_13 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9631857735129):ℝ):ℂ) + ((0.2688366891965:ℝ):ℂ) * I)‖ ≤ 0.000000128 := by
  have hl := lg_13
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.6792601366346176 53.679260168026659456 2.8694076 0.00000002799 (-0.9631857735129) 0.2688366891965 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_14 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2496514846903:ℝ):ℂ) + ((0.9683357559193:ℝ):ℂ) * I)‖ ≤ 0.00000014466 := by
  have hl := lg_14
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.230191777867711616 55.230191809259753472 1.318476 0.00000004465 0.2496514846903 0.9683357559193 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_15 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9921468674517:ℝ):ℂ) + (((-0.1250783490691):ℝ):ℂ) * I)‖ ≤ 0.00000015914 := by
  have hl := lg_15
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.674074592346622144 56.674074623738664 (-0.1254068) 0.00000005913 0.9921468674517 (-0.1250783490691) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_16 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0945857214192:ℝ):ℂ) + (((-0.9955167207554):ℝ):ℂ) * I)‖ ≤ 0.00000013453 := by
  have hl := lg_16
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.0247367572736 58.0247367991296 (-1.476069) 0.00000003452 0.0945857214192 (-0.9955167207554) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_17 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9223134079778):ℝ):ℂ) + (((-0.3864427219107):ℝ):ℂ) * I)‖ ≤ 0.00000012198 := by
  have hl := lg_17
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.293488842647930752 59.29348888450395168 (-2.7448211) 0.00000002197 (-0.9223134079778) (-0.3864427219107) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_18 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.697108496158):ℝ):ℂ) + ((0.7169656508934:ℝ):ℂ) * I)‖ ≤ 0.00000013888 := by
  have hl := lg_18
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.489700132930512384 60.48970016432255424 2.3421529 0.00000003887 (-0.697108496158) 0.7169656508934 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_19 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.352426056181:ℝ):ℂ) + ((0.9358396630431:ℝ):ℂ) * I)‖ ≤ 0.00000013214 := by
  have hl := lg_19
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.621218939674827584 61.621218971066890368 1.2106341 0.00000003213 0.352426056181 0.9358396630431 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p928_20 : ‖exp (-((((((20928:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9906071972368:ℝ):ℂ) + ((0.136738366169:ℝ):ℂ) * I)‖ ≤ 0.00000016925 := by
  have hl := lg_20
  refine (ecis_approx ((((20928:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.694684999177365952 62.69468504103338688 0.1371681 0.00000006924 0.9906071972368 0.136738366169 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_2 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.444407430709):ℝ):ℂ) + (((-0.8958247794777):ℝ):ℂ) * I)‖ ≤ 0.0000001133 := by
  have hl := lg_2
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.597679617118 14.597679627648 (-2.031309) 0.00000001329 (-0.444407430709) (-0.8958247794777) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_3 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4124757190569):ℝ):ℂ) + ((0.9109685950597:ℝ):ℂ) * I)‖ ≤ 0.00000013486 := by
  have hl := lg_3
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.13677479387593384 23.1367748044059549 1.9959664 0.00000003485 (-0.4124757190569) 0.9109685950597 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_4 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6050040653438):ℝ):ℂ) + ((0.796222381565:ℝ):ℂ) * I)‖ ≤ 0.00000011941 := by
  have hl := lg_4
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.195359234236 29.195359255296 2.2205673 0.0000000194 (-0.6050040653438) 0.796222381565 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_5 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7882990197005):ℝ):ℂ) + (((-0.6152923333622):ℝ):ℂ) * I)‖ ≤ 0.000000111 := by
  have hl := lg_5
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.89476242491324154 33.8947624459732626 (-2.4788359) 0.00000001099 (-0.7882990197005) (-0.6152923333622) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_6 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9993755153203:ℝ):ℂ) + (((-0.0353352427229):ℝ):ℂ) * I)‖ ≤ 0.0000001321 := by
  have hl := lg_6
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.73445441099393384 37.7344544320539549 (-0.0353426) 0.00000003209 0.9993755153203 (-0.0353352427229) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_7 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9901932019241):ℝ):ℂ) + ((0.1397047689035:ℝ):ℂ) * I)‖ ≤ 0.00000012212 := by
  have hl := lg_7
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.98086772815598732 40.98086774921602944 3.0014294 0.00000002211 (-0.9901932019241) 0.1397047689035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_8 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9821440416373:ℝ):ℂ) + ((0.1881304905547:ℝ):ℂ) * I)‖ ≤ 0.0000001327 := by
  have hl := lg_8
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.793038851354 43.793038882944 0.1892583 0.00000003269 0.9821440416373 0.1881304905547 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_9 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6597274818292):ℝ):ℂ) + (((-0.7515049232715):ℝ):ℂ) * I)‖ ≤ 0.00000015857 := by
  have hl := lg_9
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.27354958775186768 46.2735496088119098 (-2.2912524) 0.00000005856 (-0.6597274818292) (-0.7515049232715) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_10 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2008681698601):ℝ):ℂ) + ((0.9796182819528:ℝ):ℂ) * I)‖ ≤ 0.0000001162 := by
  have hl := lg_10
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.49244204203124154 48.4924420736212626 1.7730404 0.00000001619 (-0.2008681698601) 0.9796182819528 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_11 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9727021609847:ℝ):ℂ) + (((-0.2320571180027):ℝ):ℂ) * I)‖ ≤ 0.00000012874 := by
  have hl := lg_11
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.49967442871030498 50.4996744603003471 (-0.234192) 0.00000002873 0.9727021609847 (-0.2320571180027) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_12 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.475784091097):ℝ):ℂ) + (((-0.8795621061947):ℝ):ℂ) * I)‖ ≤ 0.00000012934 := by
  have hl := lg_12
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.33213402811193384 52.3321340597019549 (-2.0666516) 0.00000002933 (-0.475784091097) (-0.8795621061947) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_13 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8192133460898):ℝ):ℂ) + ((0.5734888782976:ℝ):ℂ) * I)‖ ≤ 0.00000011871 := by
  have hl := lg_13
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.017833451716602 54.01783348330664412 2.5308343 0.0000000187 (-0.8192133460898) 0.5734888782976 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_14 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5652002108234:ℝ):ℂ) + ((0.824953769423:ℝ):ℂ) * I)‖ ≤ 0.00000011936 := by
  have hl := lg_14
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.57854734527398732 55.57854737686402944 0.9701204 0.00000001935 0.5652002108234 0.824953769423 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_15 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8856661974845:ℝ):ℂ) + (((-0.4643225028289):ℝ):ℂ) * I)‖ ≤ 0.00000014584 := by
  have hl := lg_15
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.03153721878917538 57.0315372503792175 (-0.4828695) 0.00000004583 0.8856661974845 (-0.4643225028289) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_16 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2679401549156):ℝ):ℂ) + (((-0.9634355574622):ℝ):ℂ) * I)‖ ≤ 0.00000014599 := by
  have hl := lg_16
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.390718468472 58.390718510592 (-1.8420507) 0.00000004598 (-0.2679401549156) (-0.9634355574622) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_17 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997403791827):ℝ):ℂ) + (((-0.0227853812496):ℝ):ℂ) * I)‖ ≤ 0.00000016071 := by
  have hl := lg_17
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.66747300392610004 59.6674730460461211 (-3.1188053) 0.0000000607 (-0.9997403791827) (-0.0227853812496) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_18 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3800289303676):ℝ):ℂ) + ((0.924974600776:ℝ):ℂ) * I)‖ ≤ 0.00000016468 := by
  have hl := lg_18
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.87122920486986768 60.8712292364599098 1.9606239 0.00000006467 (-0.3800289303676) 0.924974600776 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_19 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.680780845597:ℝ):ℂ) + ((0.7324871604801:ℝ):ℂ) * I)‖ ≤ 0.00000014463 := by
  have hl := lg_19
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.00988488482185918 62.00988491641192236 0.8219682 0.00000004462 0.680780845597 0.7324871604801 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p06_20 : ‖exp (-((((((21060:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9668336386842:ℝ):ℂ) + (((-0.255406959789):ℝ):ℂ) * I)‖ ≤ 0.00000012949 := by
  have hl := lg_20
  refine (ecis_approx ((((21060:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.09012165914924154 63.0901217012692626 (-0.2582686) 0.00000002948 0.9668336386842 (-0.255406959789) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_2 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5243981055987):ℝ):ℂ) + (((-0.8514732097002):ℝ):ℂ) * I)‖ ≤ 0.00000014117 := by
  have hl := lg_2
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.6891750449176 14.6891750555136 (-2.1228044) 0.00000004116 (-0.5243981055987) (-0.8514732097002) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_3 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2765029493648):ℝ):ℂ) + ((0.9610130691053:ℝ):ℂ) * I)‖ ≤ 0.00000011279 := by
  have hl := lg_3
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.281791615945811488 23.28179162654183268 1.8509496 0.00000001278 (-0.2765029493648) 0.9610130691053 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_4 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4500131579748):ℝ):ℂ) + ((0.8930219245041:ℝ):ℂ) * I)‖ ≤ 0.00000014608 := by
  have hl := lg_4
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.3783500898352 29.3783501110272 2.0375764 0.00000004607 (-0.4500131579748) 0.8930219245041 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_5 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9003118046931):ℝ):ℂ) + (((-0.4352455102737):ℝ):ℂ) * I)‖ ≤ 0.0000001146 := by
  have hl := lg_5
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.107208229285917128 34.10720825047793832 (-2.6912817) 0.00000001459 (-0.9003118046931) (-0.4352455102737) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_6 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9632745053589:ℝ):ℂ) + (((-0.2685185791067):ℝ):ℂ) * I)‖ ≤ 0.00000013899 := by
  have hl := lg_6
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.970966660863411488 37.97096668205543268 (-0.2718548) 0.00000003898 0.9632745053589 (-0.2685185791067) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_7 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9222160724627):ℝ):ℂ) + ((0.3866749481736:ℝ):ℂ) * I)‖ ≤ 0.00000013871 := by
  have hl := lg_7
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.237727867762663024 41.237727888954705408 2.7445693 0.0000000387 (-0.9222160724627) 0.3866749481736 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_8 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9963702919326:ℝ):ℂ) + (((-0.0851248574396):ℝ):ℂ) * I)‖ ≤ 0.0000001163 := by
  have hl := lg_8
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.0675251347528 44.0675251665408 (-0.085228) 0.00000001629 0.9963702919326 (-0.0851248574396) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_9 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8470922341522):ℝ):ℂ) + (((-0.5314459020136):ℝ):ℂ) * I)‖ ≤ 0.00000011838 := by
  have hl := lg_9
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.563583231891622976 46.56358325308366536 (-2.5812861) 0.00000001837 (-0.8470922341522) (-0.5314459020136) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_10 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1015219202941:ℝ):ℂ) + ((0.9948333024682:ℝ):ℂ) * I)‖ ≤ 0.00000014857 := by
  have hl := lg_10
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.796383274203517128 48.79638330599153832 1.4690992 0.00000004856 0.1015219202941 0.9948333024682 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_11 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8521510014438:ℝ):ℂ) + (((-0.523295968586):ℝ):ℂ) * I)‖ ≤ 0.00000015283 := by
  have hl := lg_11
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.816196604616751336 50.81619663640479372 (-0.5507142) 0.00000005282 0.8521510014438 (-0.523295968586) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_12 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7337757701337):ℝ):ℂ) + (((-0.6793917273081):ℝ):ℂ) * I)‖ ≤ 0.00000015167 := by
  have hl := lg_12
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.660141705781011488 52.66014173756903268 (-2.3946593) 0.00000005166 (-0.7337757701337) (-0.6793917273081) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_13 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5822266028402):ℝ):ℂ) + ((0.8130265573365:ℝ):ℂ) * I)‖ ≤ 0.00000013399 := by
  have hl := lg_13
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.3564067667985864 54.356406798586628784 2.192261 0.00000003398 (-0.5822266028402) 0.8130265573365 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_14 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8128517789238:ℝ):ℂ) + ((0.5824705876697:ℝ):ℂ) * I)‖ ≤ 0.00000015195 := by
  have hl := lg_14
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.926902912680263024 55.926902944468305408 0.6217648 0.00000005194 0.8128517789238 0.5824705876697 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_15 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6672154930583:ℝ):ℂ) + (((-0.7448647433077):ℝ):ℂ) * I)‖ ≤ 0.0000001194 := by
  have hl := lg_15
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.388999845231728616 57.388999877019771 (-0.8403321) 0.00000001939 0.6672154930583 (-0.7448647433077) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_16 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5949762291534):ℝ):ℂ) + (((-0.8037432965386):ℝ):ℂ) * I)‖ ≤ 0.00000015745 := by
  have hl := lg_16
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.7567001796704 58.7567002220544 (-2.2080324) 0.00000005744 (-0.5949762291534) (-0.8037432965386) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_17 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9389616760093):ℝ):ℂ) + ((0.3440217592081:ℝ):ℂ) * I)‖ ≤ 0.00000013581 := by
  have hl := lg_17
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.041457165204269328 60.04145720758829052 2.7903959 0.0000000358 (-0.9389616760093) 0.3440217592081 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_18 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0082983779602):ℝ):ℂ) + ((0.9999655678687:ℝ):ℂ) * I)‖ ≤ 0.00000013682 := by
  have hl := lg_18
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.252758276809222976 61.25275830859726536 1.5790948 0.00000003681 (-0.0082983779602) 0.9999655678687 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_19 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9075842054977:ℝ):ℂ) + ((0.4198701107857:ℝ):ℂ) * I)‖ ≤ 0.00000014184 := by
  have hl := lg_19
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.398550829968890776 62.398550861756954352 0.4333022 0.00000004183 0.9075842054977 0.4198701107857 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p192_20 : ‖exp (-((((((21192:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7938359416812:ℝ):ℂ) + (((-0.6081319739128):ℝ):ℂ) * I)‖ ≤ 0.00000015269 := by
  have hl := lg_20
  refine (ecis_approx ((((21192:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.485558319121117128 63.48555836150513832 (-0.6537053) 0.00000005268 0.7938359416812 (-0.6081319739128) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_2 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6000019715267):ℝ):ℂ) + (((-0.7999985213436):ℝ):ℂ) * I)‖ ≤ 0.00000014166 := by
  have hl := lg_2
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.7806704727172 14.7806704833792 (-2.2142999) 0.00000004165 (-0.6000019715267) (-0.7999985213436) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_3 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1347255412342):ℝ):ℂ) + ((0.9908829540055:ℝ):ℂ) * I)‖ ≤ 0.00000011997 := by
  have hl := lg_3
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.426808438015689136 23.42680844867771046 1.7059328 0.00000001996 (-0.1347255412342) 0.9908829540055 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_4 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2799953574337):ℝ):ℂ) + ((0.9600013540689:ℝ):ℂ) * I)‖ ≤ 0.00000013088 := by
  have hl := lg_4
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.5613409454344 29.5613409667584 1.8545856 0.00000003087 (-0.2799953574337) 0.9600013540689 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_5 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9718432194862):ℝ):ℂ) + (((-0.2356284287999):ℝ):ℂ) * I)‖ ≤ 0.0000001191 := by
  have hl := lg_5
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.319654033658592716 34.31965405498261404 (-2.9037275) 0.00000001909 (-0.9718432194862) (-0.2356284287999) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_6 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8735404883916:ℝ):ℂ) + (((-0.4867514921811):ℝ):ℂ) * I)‖ ≤ 0.00000013236 := by
  have hl := lg_6
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.207478910732889136 38.20747893205691046 (-0.5083671) 0.00000003235 0.8735404883916 (-0.4867514921811) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_7 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7937275273532):ℝ):ℂ) + ((0.6082734683306:ℝ):ℂ) * I)‖ ≤ 0.0000001429 := by
  have hl := lg_7
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.494588007369338728 41.494588028693381376 2.4877091 0.00000004289 (-0.7937275273532) 0.6082734683306 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_8 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.935997430229:ℝ):ℂ) + (((-0.3520068331791):ℝ):ℂ) * I)‖ ≤ 0.00000013212 := by
  have hl := lg_8
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.3420114181516 44.3420114501376 (-0.3597143) 0.00000003211 0.935997430229 (-0.3520068331791) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_9 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9636980550685):ℝ):ℂ) + (((-0.2669944913498):ℝ):ℂ) * I)‖ ≤ 0.00000014711 := by
  have hl := lg_9
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.853616876031378272 46.85361689735542092 (-2.8713197) 0.0000000471 (-0.9636980550685) (-0.2669944913498) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_10 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3946054596297:ℝ):ℂ) + ((0.9188506577406:ℝ):ℂ) * I)‖ ≤ 0.00000015108 := by
  have hl := lg_10
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.100324506375792716 49.10032453836181404 1.1651579 0.00000005107 0.3946054596297 0.9188506577406 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_11 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.646936457831:ℝ):ℂ) + (((-0.7625439131808):ℝ):ℂ) * I)‖ ≤ 0.00000015509 := by
  have hl := lg_11
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.132718780523197692 51.13271881250924034 (-0.8672363) 0.00000005508 0.646936457831 (-0.7625439131808) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_12 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.913526448535):ℝ):ℂ) + (((-0.4067793353816):ℝ):ℂ) * I)‖ ≤ 0.00000015801 := by
  have hl := lg_12
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.988149383450089136 52.98814941543611046 (-2.7226669) 0.000000058 (-0.913526448535) (-0.4067793353816) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_13 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2791332594642):ℝ):ℂ) + ((0.9602523748783:ℝ):ℂ) * I)‖ ≤ 0.00000014927 := by
  have hl := lg_13
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.6949800818805708 54.694980113866613448 1.8536877 0.00000004926 (-0.2791332594642) 0.9602523748783 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_14 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.962855929534:ℝ):ℂ) + ((0.2700156642887:ℝ):ℂ) * I)‖ ≤ 0.00000014747 := by
  have hl := lg_14
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.275258480086538728 56.275258512072581376 0.2734093 0.00000004746 0.962855929534 0.2700156642887 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_15 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3644122974713:ℝ):ℂ) + (((-0.9312377126447):ℝ):ℂ) * I)‖ ≤ 0.00000013906 := by
  have hl := lg_15
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.746462471674281852 57.7464625036603245 (-1.1977947) 0.00000003905 0.3644122974713 (-0.9312377126447) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_16 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8432051957548):ℝ):ℂ) + (((-0.5375918505543):ℝ):ℂ) * I)‖ ≤ 0.00000016892 := by
  have hl := lg_16
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.1226818908688 59.1226819335168 (-2.5740141) 0.00000006891 (-0.8432051957548) (-0.5375918505543) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_17 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7483794129678):ℝ):ℂ) + ((0.6632708754442:ℝ):ℂ) * I)‖ ≤ 0.00000014533 := by
  have hl := lg_17
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.415441326482438616 60.41544136913045994 2.4164117 0.00000004532 (-0.7483794129678) 0.6632708754442 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_18 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3646255413506:ℝ):ℂ) + ((0.9311542378118:ℝ):ℂ) * I)‖ ≤ 0.00000012306 := by
  have hl := lg_18
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.634287348748578272 61.63428738073462092 1.1975657 0.00000002305 0.3646255413506 0.9311542378118 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_19 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9990039657525:ℝ):ℂ) + ((0.0446214792545:ℝ):ℂ) * I)‖ ≤ 0.00000013532 := by
  have hl := lg_19
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.787216775115922372 62.787216807101986344 0.0446363 0.00000003531 0.9990039657525 0.0446214792545 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p324_20 : ‖exp (-((((((21324:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4983152004806:ℝ):ℂ) + (((-0.8669959405729):ℝ):ℂ) * I)‖ ≤ 0.00000014996 := by
  have hl := lg_20
  refine (ecis_approx ((((21324:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.880994979092992716 63.88099502174101404 (-1.0491419) 0.00000004995 0.4983152004806 (-0.8669959405729) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_2 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6933953660397):ℝ):ℂ) + (((-0.7205573303576):ℝ):ℂ) * I)‖ ≤ 0.00000012004 := by
  have hl := lg_2
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.9033575236303 14.9033575343808 (-2.3369869) 0.00000002003 (-0.6933953660397) (-0.7205573303576) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_3 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0592831467423:ℝ):ℂ) + ((0.9982412075807:ℝ):ℂ) * I)‖ ≤ 0.00000011567 := by
  have hl := lg_3
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.621262813063934164 23.621262823814455665 1.5114784 0.00000001566 0.0592831467423 0.9982412075807 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_4 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.038405725527):ℝ):ℂ) + ((0.9992622279694:ℝ):ℂ) * I)‖ ≤ 0.00000013288 := by
  have hl := lg_4
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.8067150472606 29.8067150687616 1.6092115 0.00000003287 (-0.038405725527) 0.9992622279694 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_5 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9988954514871):ℝ):ℂ) + ((0.0469880454905:ℝ):ℂ) * I)‖ ≤ 0.00000012251 := by
  have hl := lg_5
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.604524544067407709 34.60452456556842921 3.0945873 0.0000000225 (-0.9988954514871) 0.0469880454905 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_6 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6781833603647:ℝ):ℂ) + (((-0.7348927334819):ℝ):ℂ) * I)‖ ≤ 0.00000011513 := by
  have hl := lg_6
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.524620336694234164 38.524620358195255665 (-0.8255085) 0.00000001512 0.6781833603647 (-0.7348927334819) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_7 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.541723910754):ℝ):ℂ) + ((0.84055648502:ℝ):ℂ) * I)‖ ≤ 0.00000014661 := by
  have hl := lg_7
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.839014103660108422 41.839014125161151424 2.143283 0.0000000466 (-0.541723910754) 0.84055648502 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_8 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7466560754357:ℝ):ℂ) + (((-0.6652102712789):ℝ):ℂ) * I)‖ ≤ 0.0000001529 := by
  have hl := lg_8
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.7100725708909 44.7100726031424 (-0.7277754) 0.00000005289 0.7466560754357 (-0.6652102712789) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_9 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9929710168264):ℝ):ℂ) + ((0.1183577597755:ℝ):ℂ) * I)‖ ≤ 0.00000013132 := by
  have hl := lg_9
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.242525626127868328 47.24252564762891133 3.0229568 0.00000003131 (-0.9929710168264) 0.1183577597755 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_10 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7264870582232:ℝ):ℂ) + ((0.6871801468569:ℝ):ℂ) * I)‖ ≤ 0.00000014253 := by
  have hl := lg_10
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.507882067697707709 49.50788209994922921 0.7576004 0.00000004252 0.7264870582232 0.6871801468569 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_11 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2755218548472:ℝ):ℂ) + (((-0.9612948077991):ℝ):ℂ) * I)‖ ≤ 0.0000001185 := by
  have hl := lg_11
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.557146243670478033 51.557146275922021035 (-1.2916638) 0.00000001849 0.2755218548472 (-0.9612948077991) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_12 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997815450876):ℝ):ℂ) + ((0.0209012311805:ℝ):ℂ) * I)‖ ≤ 0.00000012797 := by
  have hl := lg_12
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.427977860324534164 53.427977892576055665 3.1206899 0.00000002796 (-0.9997815450876) 0.0209012311805 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_13 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1702710475093:ℝ):ℂ) + ((0.9853972652591:ℝ):ℂ) * I)‖ ≤ 0.00000014662 := by
  have hl := lg_13
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.1489761180132317 55.148976150264774702 1.3996916 0.00000004661 0.1702710475093 0.9853972652591 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_14 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9812979862665:ℝ):ℂ) + (((-0.1924948366821):ℝ):ℂ) * I)‖ ≤ 0.00000013734 := by
  have hl := lg_14
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.742371627290408422 56.742371659541951424 (-0.1937039) 0.00000003733 0.9812979862665 (-0.1924948366821) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_15 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1061230620445):ℝ):ℂ) + (((-0.9943530035666):ℝ):ℂ) * I)‖ ≤ 0.00000012478 := by
  have hl := lg_15
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.225787357131341873 58.225787389382884875 (-1.6771196) 0.00000002477 (-0.1061230620445) (-0.9943530035666) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_16 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9970500073763):ℝ):ℂ) + (((-0.076754688926):ℝ):ℂ) * I)‖ ≤ 0.00000017011 := by
  have hl := lg_16
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.6134300945212 59.6134301375232 (-3.0647624) 0.0000000701 (-0.9970500073763) (-0.076754688926) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_17 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.33738409566):ℝ):ℂ) + ((0.9413670761151:ℝ):ℂ) * I)‖ ≤ 0.00000015942 := by
  have hl := lg_17
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.916920088196347434 60.916920131198368935 1.914933 0.00000005941 (-0.33738409566) 0.9413670761151 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_18 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.773805053384:ℝ):ℂ) + ((0.6334238228528:ℝ):ℂ) * I)‖ ≤ 0.00000012205 := by
  have hl := lg_18
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.145883149758168328 62.14588318200971133 0.6859699 0.00000002204 0.773805053384 0.6334238228528 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_19 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8885922284185:ℝ):ℂ) + (((-0.4586979960653):ℝ):ℂ) * I)‖ ≤ 0.00000013476 := by
  have hl := lg_19
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.308382474290351103 63.308382506541915606 (-0.4765294) 0.00000003475 0.8885922284185 (-0.4586979960653) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p501_20 : ‖exp (-((((((21501:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0085900675592):ℝ):ℂ) + (((-0.9999631046889):ℝ):ℂ) * I)‖ ≤ 0.00000016255 := by
  have hl := lg_20
  refine (ecis_approx ((((21501:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.411239591328007709 64.41123963433002921 (-1.5793865) 0.00000006254 (-0.0085900675592) (-0.9999631046889) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_2 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7763648522785):ℝ):ℂ) + (((-0.6302837584021):ℝ):ℂ) * I)‖ ≤ 0.00000013983 := by
  have hl := lg_2
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.0260445745434 15.0260445853824 (-2.459674) 0.00000003982 (-0.7763648522785) (-0.6302837584021) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_3 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2510572445433:ℝ):ℂ) + ((0.967972241318:ℝ):ℂ) * I)‖ ≤ 0.00000014062 := by
  have hl := lg_3
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.815717188112179192 23.81571719895120087 1.317024 0.00000004061 0.2510572445433 0.967972241318 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_4 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.205484676891:ℝ):ℂ) + ((0.9786603330896:ℝ):ℂ) * I)‖ ≤ 0.00000013488 := by
  have hl := lg_4
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.0520891490868 30.0520891707648 1.3638374 0.00000003487 0.205484676891 0.9786603330896 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_5 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9454328220608):ℝ):ℂ) + ((0.3258170940549:ℝ):ℂ) * I)‖ ≤ 0.00000013309 := by
  have hl := lg_5
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.889395054476222702 34.88939507615424438 2.8097168 0.00000003308 (-0.9454328220608) 0.3258170940549 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_6 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4151852527077:ℝ):ℂ) + (((-0.9097368883001):ℝ):ℂ) * I)‖ ≤ 0.00000014127 := by
  have hl := lg_6
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.841761762655579192 38.84176178433360087 (-1.1426499) 0.00000004126 0.4151852527077 (-0.9097368883001) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_7 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2260887412688):ℝ):ℂ) + ((0.9741067092831:ℝ):ℂ) * I)‖ ≤ 0.00000015032 := by
  have hl := lg_7
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.183440199950878116 42.183440221628921472 1.7988569 0.00000005031 (-0.2260887412688) 0.9741067092831 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_8 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4573026321399:ℝ):ℂ) + (((-0.8893111393871):ℝ):ℂ) * I)‖ ≤ 0.00000012664 := by
  have hl := lg_8
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.0781337236302 45.0781337561472 (-1.0958366) 0.00000002663 0.4573026321399 (-0.8893111393871) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_9 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8739405685035):ℝ):ℂ) + ((0.4860327999556:ℝ):ℂ) * I)‖ ≤ 0.00000014048 := by
  have hl := lg_9
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.631434376224358384 47.63143439790240174 2.6340481 0.00000004047 (-0.8739405685035) 0.4860327999556 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_10 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9393580359608:ℝ):ℂ) + ((0.3429380122935:ℝ):ℂ) * I)‖ ≤ 0.00000012843 := by
  have hl := lg_10
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.915439629019622702 49.91543966153664438 0.3500428 0.00000002842 0.9393580359608 0.3429380122935 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_11 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1447843011488):ℝ):ℂ) + (((-0.9894632414295):ℝ):ℂ) * I)‖ ≤ 0.00000015063 := by
  have hl := lg_11
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.981573706817758374 51.98157373933480173 (-1.7160913) 0.00000005062 (-0.1447843011488) (-0.9894632414295) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_12 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8957276193014):ℝ):ℂ) + ((0.4446032297556:ℝ):ℂ) * I)‖ ≤ 0.00000012743 := by
  have hl := lg_12
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.867806337198979192 53.86780636971600087 2.6808614 0.00000002742 (-0.8957276193014) 0.4446032297556 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_13 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.585178955688:ℝ):ℂ) + ((0.8109041804183:ℝ):ℂ) * I)‖ ≤ 0.00000012206 := by
  have hl := lg_13
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.6029721541458926 55.602972186662935956 0.9456956 0.00000002205 0.585178955688 0.8109041804183 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_14 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7894910514295:ℝ):ℂ) + (((-0.6137620709304):ℝ):ℂ) * I)‖ ≤ 0.00000014241 := by
  have hl := lg_14
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.209484774494278116 57.209484807011321472 (-0.660817) 0.0000000424 0.7894910514295 (-0.6137620709304) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p678_15 : ‖exp (-((((((21678:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5527396561294):ℝ):ℂ) + (((-0.8333539899305):ℝ):ℂ) * I)‖ ≤ 0.00000012204 := by
  have hl := lg_15
  refine (ecis_approx ((((21678:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.705112242588401894 58.70511227510544525 (-2.1564445) 0.00000002203 (-0.5527396561294) (-0.8333539899305) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_2 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8686448093656):ℝ):ℂ) + (((-0.495435359129):ℝ):ℂ) * I)‖ ≤ 0.00000010571 := by
  have hl := lg_2
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.1896273090942 15.1896273200512 (-2.6232567) 0.0000000057 (-0.8686448093656) (-0.495435359129) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_3 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4908323357022:ℝ):ℂ) + ((0.8712540491895:ℝ):ℂ) * I)‖ ≤ 0.00000014056 := by
  have hl := lg_3
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.074989688176505896 24.07498969913352781 1.0577515 0.00000004055 0.4908323357022 0.8712540491895 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_4 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5090876159346:ℝ):ℂ) + ((0.8607147026175:ℝ):ℂ) * I)‖ ≤ 0.00000011772 := by
  have hl := lg_4
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.3792546181884 30.3792546401024 1.0366719 0.00000001771 0.5090876159346 0.8607147026175 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_5 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7572505382795):ℝ):ℂ) + ((0.6531245074561:ℝ):ℂ) * I)‖ ≤ 0.0000001414 := by
  have hl := lg_5
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.269222401687976026 35.26922242360199794 2.4298894 0.00000004139 (-0.7572505382795) 0.6531245074561 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_6 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0052911021065:ℝ):ℂ) + (((-0.9999860020212):ℝ):ℂ) * I)‖ ≤ 0.00000014582 := by
  have hl := lg_6
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.264616997270705896 39.26461701918472781 (-1.5655052) 0.00000004581 0.0052911021065 (-0.9999860020212) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_7 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2291206712741:ℝ):ℂ) + ((0.9733980265004:ℝ):ℂ) * I)‖ ≤ 0.00000015527 := by
  have hl := lg_7
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.642674995005237708 42.642675016919281536 1.3396221 0.00000005526 0.2291206712741 0.9733980265004 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_8 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0157878172657):ℝ):ℂ) + (((-0.9998753646459):ℝ):ℂ) * I)‖ ≤ 0.00000012299 := by
  have hl := lg_8
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.5688819272826 45.5688819601536 (-1.5865848) 0.00000002298 (-0.0157878172657) (-0.9998753646459) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_9 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5181673219859):ℝ):ℂ) + ((0.8552792680867:ℝ):ℂ) * I)‖ ≤ 0.00000014085 := by
  have hl := lg_9
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.149979376353011792 48.14997939826705562 2.1155031 0.00000004084 (-0.5181673219859) 0.8552792680867 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_10 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.981362724437:ℝ):ℂ) + (((-0.1921645208814):ℝ):ℂ) * I)‖ ≤ 0.00000014667 := by
  have hl := lg_10
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.458849710782176026 50.45884974365319794 (-0.1933673) 0.00000004666 0.981362724437 (-0.1921645208814) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_11 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6527420275475):ℝ):ℂ) + (((-0.7575802567755):ℝ):ℂ) * I)‖ ≤ 0.00000016644 := by
  have hl := lg_11
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.547476991014132162 52.54747702388517599 (-2.2819946) 0.00000006643 (-0.6527420275475) (-0.7575802567755) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_12 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.500024506246):ℝ):ℂ) + ((0.8660112546308:ℝ):ℂ) * I)‖ ≤ 0.00000015827 := by
  have hl := lg_12
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.454244306364905896 54.45424433923592781 2.0944234 0.00000005826 (-0.500024506246) 0.8660112546308 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_13 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9426320453623:ℝ):ℂ) + ((0.3338335319528:ℝ):ℂ) * I)‖ ≤ 0.00000016231 := by
  have hl := lg_13
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.2083002023227738 56.208300235193817628 0.3403675 0.0000000623 0.9426320453623 0.3338335319528 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_14 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2832313190552:ℝ):ℂ) + (((-0.959051625256):ℝ):ℂ) * I)‖ ≤ 0.00000016053 := by
  have hl := lg_14
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.832302304099437708 57.832302336970481536 (-1.2836346) 0.00000006052 0.2832313190552 (-0.959051625256) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p914_15 : ‖exp (-((((((21914:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9407203857666):ℝ):ℂ) + (((-0.3391830709546):ℝ):ℂ) * I)‖ ≤ 0.00000015813 := by
  have hl := lg_15
  refine (ecis_approx ((((21914:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.344212089864481922 59.34421212273552575 (-2.7955443) 0.00000005812 (-0.9407203857666) (-0.3391830709546) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_2 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9553380985562):ℝ):ℂ) + (((-0.29551500339):ℝ):ℂ) * I)‖ ≤ 0.00000014349 := by
  have hl := lg_2
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.4079686708887 15.4079686820032 (-2.8415981) 0.00000004348 (-0.9553380985562) (-0.29551500339) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_3 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7572600435116:ℝ):ℂ) + ((0.6531134866934:ℝ):ℂ) * I)‖ ≤ 0.00000014144 := by
  have hl := lg_3
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.421052559025077556 24.421052570139599785 0.7116887 0.00000004143 0.7572600435116 0.6531134866934 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_4 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8253417130003:ℝ):ℂ) + ((0.5646335597375:ℝ):ℂ) * I)‖ ≤ 0.00000012812 := by
  have hl := lg_4
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.8159373417774 30.8159373640064 0.5999892 0.00000002811 0.8253417130003 0.5646335597375 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_5 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3448886681333):ℝ):ℂ) + ((0.9386435993448:ℝ):ℂ) * I)‖ ≤ 0.00000012311 := by
  have hl := lg_5
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.776195343940951861 35.77619536616997409 1.9229165 0.0000000231 (-0.3448886681333) 0.9386435993448 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_6 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5304345358331):ℝ):ℂ) + (((-0.8477259009773):ℝ):ℂ) * I)‖ ≤ 0.00000011318 := by
  have hl := lg_6
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.829021229913777556 39.829021252142799785 (-2.1299094) 0.00000001317 (-0.5304345358331) (-0.8477259009773) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_7 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7473973206038:ℝ):ℂ) + ((0.6643773364243:ℝ):ℂ) * I)‖ ≤ 0.00000015848 := by
  have hl := lg_7
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.255636691793895638 43.255636714022940096 0.7266604 0.00000005847 0.7473973206038 0.6643773364243 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_8 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6216226944377):ℝ):ℂ) + (((-0.7833168105857):ℝ):ℂ) * I)‖ ≤ 0.00000013761 := by
  have hl := lg_8
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.2239060126661 46.2239060460096 (-2.2416089) 0.0000000376 (-0.6216226944377) (-0.7833168105857) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_9 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1468856459138:ℝ):ℂ) + ((0.9891534800143:ℝ):ℂ) * I)‖ ≤ 0.0000001394 := by
  have hl := lg_9
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.842105118050155112 48.84210514027919957 1.4233773 0.00000003939 0.1468856459138 0.9891534800143 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_10 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6068685510037:ℝ):ℂ) + (((-0.7948022155245):ℝ):ℂ) * I)‖ ≤ 0.00000014262 := by
  have hl := lg_10
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.184164014829651861 51.18416404817317409 (-0.9186816) 0.00000004261 0.6068685510037 (-0.7948022155245) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_11 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9945697378931):ℝ):ℂ) + (((-0.1040722633511):ℝ):ℂ) * I)‖ ≤ 0.00000015575 := by
  have hl := lg_11
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.302814001699970057 53.302814035043514515 (-3.0373316) 0.00000005574 (-0.9945697378931) (-0.1040722633511) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_12 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2562286052559:ℝ):ℂ) + ((0.9666162122831:ℝ):ℂ) * I)‖ ≤ 0.00000016383 := by
  have hl := lg_12
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.236989900802477556 55.236989934145999785 1.3116778 0.00000006382 0.2562286052559 0.9666162122831 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_13 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8926564778235:ℝ):ℂ) + (((-0.4507376316659):ℝ):ℂ) * I)‖ ≤ 0.00000011842 := by
  have hl := lg_13
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.0162592496775093 57.016259283021053758 (-0.4675915) 0.00000001841 0.8926564778235 (-0.4507376316659) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_14 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5176835787331):ℝ):ℂ) + (((-0.8555721549367):ℝ):ℂ) * I)‖ ≤ 0.00000013142 := by
  have hl := lg_14
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.663605362682595638 58.663605396026140096 (-2.1149376) 0.00000003141 (-0.5176835787331) (-0.8555721549367) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p229_15 : ‖exp (-((((((22229:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.874211201744):ℝ):ℂ) + ((0.4855458522673:ℝ):ℂ) * I)‖ ≤ 0.00000016453 := by
  have hl := lg_15
  refine (ecis_approx ((((22229:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.197247902966029417 60.197247936309573875 2.6346052 0.00000006452 (-0.874211201744) 0.4855458522673 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p65_2 : ‖exp (-((((((22650:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999665464887):ℝ):ℂ) + (((-0.0081795620805):ℝ):ℂ) * I)‖ ≤ 0.00000013078 := by
  have hl := lg_2
  refine (ecis_approx ((((22650:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.699783633795 15.69978364512 (-3.133413) 0.00000003077 (-0.9999665464887) (-0.0081795620805) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p65_3 : ‖exp (-((((((22650:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9691167180882:ℝ):ℂ) + ((0.2466024872581:ℝ):ℂ) * I)‖ ≤ 0.00000011507 := by
  have hl := lg_3
  refine (ecis_approx ((((22650:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.8835683324449146 24.88356834376993725 0.2491729 0.00000001506 0.9691167180882 0.2466024872581 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p65_4 : ‖exp (-((((((22650:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9998661896361:ℝ):ℂ) + ((0.0163585703122:ℝ):ℂ) * I)‖ ≤ 0.00000015436 := by
  have hl := lg_4
  refine (ecis_approx ((((22650:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.39956726759 31.39956729024 0.0163593 0.00000005435 0.9998661896361 0.0163585703122 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p65_5 : ‖exp (-((((((22650:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3197382537484:ℝ):ℂ) + ((0.9475059097916:ℝ):ℂ) * I)‖ ≤ 0.00000013824 := by
  have hl := lg_5
  refine (ecis_approx ((((22650:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.45376870485683385 36.4537687275068565 1.2453431 0.00000003823 0.3197382537484 0.9475059097916 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p65_6 : ‖exp (-((((((22650:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9670671975259):ℝ):ℂ) + (((-0.2545211881363):ℝ):ℂ) * I)‖ ≤ 0.00000014583 := by
  have hl := lg_6
  refine (ecis_approx ((((22650:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.5833519662399146 40.58335198888993725 (-2.8842401) 0.00000004582 (-0.9670671975259) (-0.2545211881363) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p65_7 : ‖exp (-((((((22650:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.995718668917:ℝ):ℂ) + (((-0.0924355579323):ℝ):ℂ) * I)‖ ≤ 0.00000013674 := by
  have hl := lg_7
  refine (ecis_approx ((((22650:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.0748648643273083 44.0748648869773536 (-0.0925677) 0.00000003673 0.995718668917 (-0.0924355579323) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p65_8 : ‖exp (-((((((22650:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996989371323):ℝ):ℂ) + (((-0.0245363906806):ℝ):ℂ) * I)‖ ≤ 0.00000014889 := by
  have hl := lg_8
  refine (ecis_approx ((((22650:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.099350901385 47.09935093536 (-3.1170538) 0.00000004888 (-0.9996989371323) (-0.0245363906806) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p65_9 : ‖exp (-((((((22650:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8783744265563:ℝ):ℂ) + ((0.4779731862479:ℝ):ℂ) * I)‖ ≤ 0.00000013012 := by
  have hl := lg_9
  refine (ecis_approx ((((22650:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.7671366648898292 49.7671366875398745 0.4983458 0.00000003011 0.8783744265563 0.4779731862479 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22p65_10 : ‖exp (-((((((22650:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3119773737947):ℝ):ℂ) + (((-0.950089531696):ℝ):ℂ) * I)‖ ≤ 0.0000001188 := by
  have hl := lg_10
  refine (ecis_approx ((((22650:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.15355233865183385 52.1535523726268565 (-1.8880699) 0.00000001879 (-0.3119773737947) (-0.950089531696) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p071_2 : ‖exp (-((((((23071:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9600444393887):ℝ):ℂ) + ((0.2798475909589:ℝ):ℂ) * I)‖ ≤ 0.00000012485 := by
  have hl := lg_2
  refine (ecis_approx ((((23071:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.9915985967013 15.9915986082368 2.8579573 0.00000002484 (-0.9600444393887) 0.2798475909589 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p071_3 : ‖exp (-((((((23071:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9773285906898:ℝ):ℂ) + (((-0.211728188535):ℝ):ℂ) * I)‖ ≤ 0.00000012287 := by
  have hl := lg_3
  refine (ecis_approx ((((23071:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.346084105864751644 25.346084117400274715 (-0.2133429) 0.00000002286 0.9773285906898 (-0.211728188535) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p071_4 : ‖exp (-((((((23071:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8433706553931:ℝ):ℂ) + (((-0.5373322413757):ℝ):ℂ) * I)‖ ≤ 0.00000014251 := by
  have hl := lg_4
  refine (ecis_approx ((((23071:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.9831971934026 31.9831972164736 (-0.5672707) 0.0000000425 0.8433706553931 (-0.5373322413757) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p071_5 : ‖exp (-((((((23071:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8431023678404:ℝ):ℂ) + ((0.5377531007274:ℝ):ℂ) * I)‖ ≤ 0.00000014578 := by
  have hl := lg_5
  refine (ecis_approx ((((23071:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.131342065772715839 37.13134208884373891 0.5677698 0.00000004577 0.8431023678404 0.5377531007274 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p071_6 : ‖exp (-((((((23071:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8790272554811):ℝ):ℂ) + ((0.4767715218277:ℝ):ℂ) * I)‖ ≤ 0.00000014771 := by
  have hl := lg_6
  refine (ecis_approx ((((23071:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.337682702566051644 41.337682725637074715 2.6446144 0.0000000477 (-0.8790272554811) 0.4767715218277 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p071_7 : ‖exp (-((((((23071:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6123268907413:ℝ):ℂ) + (((-0.7906046919131):ℝ):ℂ) * I)‖ ≤ 0.00000011341 := by
  have hl := lg_7
  refine (ecis_approx ((((23071:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.894093036860720962 44.894093059931767104 (-0.9117959) 0.0000000134 0.6123268907413 (-0.7906046919131) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p071_8 : ‖exp (-((((((23071:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6593022499549):ℝ):ℂ) + ((0.7518780108411:ℝ):ℂ) * I)‖ ≤ 0.00000016729 := by
  have hl := lg_8
  refine (ecis_approx ((((23071:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.9747957901039 47.9747958247104 2.2906867 0.00000006728 (-0.6593022499549) 0.7518780108411 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p071_9 : ‖exp (-((((((23071:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9103423483594:ℝ):ℂ) + (((-0.4138560242205):ℝ):ℂ) * I)‖ ≤ 0.00000014572 := by
  have hl := lg_9
  refine (ecis_approx ((((23071:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.692168211729503288 50.69216823480054943 (-0.4266858) 0.00000004571 0.9103423483594 (-0.4138560242205) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p071_10 : ‖exp (-((((((23071:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9599046478881):ℝ):ℂ) + (((-0.2803267142638):ℝ):ℂ) * I)‖ ≤ 0.00000013966 := by
  have hl := lg_10
  refine (ecis_approx ((((23071:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.122940662474015839 53.12294069708053891 (-2.8574582) 0.00000003965 (-0.9599046478881) (-0.2803267142638) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p492_2 : ‖exp (-((((((23492:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8389473537823):ℝ):ℂ) + ((0.5442125848549:ℝ):ℂ) * I)‖ ≤ 0.00000014983 := by
  have hl := lg_2
  refine (ecis_approx ((((23492:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.2834135596076 16.2834135713536 2.5661424 0.00000004982 (-0.8389473537823) 0.5442125848549 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p492_3 : ‖exp (-((((((23492:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7801700640393:ℝ):ℂ) + (((-0.6255674793153):ℝ):ℂ) * I)‖ ≤ 0.00000014945 := by
  have hl := lg_3
  refine (ecis_approx ((((23492:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.808599879284588688 25.80859989103061218 (-0.6758587) 0.00000004944 0.7801700640393 (-0.6255674793153) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p492_4 : ‖exp (-((((((23492:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4076652401326:ℝ):ℂ) + (((-0.9131314538376):ℝ):ℂ) * I)‖ ≤ 0.0000001167 := by
  have hl := lg_4
  refine (ecis_approx ((((23492:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.5668271192152 32.5668271427072 (-1.1509006) 0.00000001669 0.4076652401326 (-0.9131314538376) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p492_5 : ‖exp (-((((((23492:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9939776392449:ℝ):ℂ) + (((-0.1095830857436):ℝ):ℂ) * I)‖ ≤ 0.0000001164 := by
  have hl := lg_5
  refine (ecis_approx ((((23492:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.808915426688597828 37.80891545018062132 (-0.1098036) 0.00000001639 0.9939776392449 (-0.1095830857436) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p492_6 : ‖exp (-((((((23492:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3140799157957):ℝ):ℂ) + ((0.9493965485991:ℝ):ℂ) * I)‖ ≤ 0.00000011214 := by
  have hl := lg_6
  refine (ecis_approx ((((23492:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.092013438892188688 42.09201346238421218 1.8902837 0.00000001213 (-0.3140799157957) 0.9493965485991 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p492_7 : ‖exp (-((((((23492:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1595430664021):ℝ):ℂ) + (((-0.9871909693481):ℝ):ℂ) * I)‖ ≤ 0.00000014088 := by
  have hl := lg_7
  refine (ecis_approx ((((23492:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.713321209394133624 45.713321232886180608 (-1.7310241) 0.00000004087 (-0.1595430664021) (-0.9871909693481) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p492_8 : ‖exp (-((((((23492:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1549279543946:ℝ):ℂ) + ((0.9879257709702:ℝ):ℂ) * I)‖ ≤ 0.00000015664 := by
  have hl := lg_8
  refine (ecis_approx ((((23492:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.8502406788228 48.8502407140608 1.4152418 0.00000005663 0.1549279543946 0.9879257709702 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p492_9 : ‖exp (-((((((23492:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2173307552559:ℝ):ℂ) + (((-0.9760980190636):ℝ):ℂ) * I)‖ ≤ 0.00000012464 := by
  have hl := lg_9
  refine (ecis_approx ((((23492:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.617199758569177376 51.61719978206122436 (-1.3517173) 0.00000002463 0.2173307552559 (-0.9760980190636) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p492_10 : ‖exp (-((((((23492:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7742584158186):ℝ):ℂ) + ((0.6328695801614:ℝ):ℂ) * I)‖ ≤ 0.00000015693 := by
  have hl := lg_10
  refine (ecis_approx ((((23492:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.092328986296197828 54.09232902153422132 2.4563388 0.00000005692 (-0.7742584158186) 0.6328695801614 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_2 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6469143791745):ℝ):ℂ) + ((0.7625626439846:ℝ):ℂ) * I)‖ ≤ 0.00000011295 := by
  have hl := lg_2
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.5752285225139 16.5752285344704 2.2743274 0.00000001294 (-0.6469143791745) 0.7625626439846 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_3 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4190710261567:ℝ):ℂ) + (((-0.9079534542232):ℝ):ℂ) * I)‖ ≤ 0.00000013596 := by
  have hl := lg_3
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.271115652704425732 26.271115664660949645 (-1.1383744) 0.00000003595 0.4190710261567 (-0.9079534542232) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_4 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1630035649467):ℝ):ℂ) + (((-0.9866254800146):ℝ):ℂ) * I)‖ ≤ 0.00000013306 := by
  have hl := lg_4
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.1504570450278 33.1504570689408 (-1.7345305) 0.00000003305 (-0.1630035649467) (-0.9866254800146) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_5 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7057061488773:ℝ):ℂ) + (((-0.708504644612):ℝ):ℂ) * I)‖ ≤ 0.00000015549 := by
  have hl := lg_5
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.486488787604479817 38.48648881151750373 (-0.787377) 0.00000005548 0.7057061488773 (-0.708504644612) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_6 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.421268313959:ℝ):ℂ) + ((0.9069360548871:ℝ):ℂ) * I)‖ ≤ 0.00000014889 := by
  have hl := lg_6
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.846344175218325732 42.846344199131349645 1.135953 0.00000004888 0.421268313959 0.9069360548871 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_7 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8301941566552):ℝ):ℂ) + (((-0.5574743601216):ℝ):ℂ) * I)‖ ≤ 0.0000001556 := by
  have hl := lg_7
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.532549381927546286 46.532549405840594112 (-2.5502522) 0.00000005559 (-0.8301941566552) (-0.5574743601216) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_8 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8578130846929:ℝ):ℂ) + ((0.5139617804172:ℝ):ℂ) * I)‖ ≤ 0.00000014599 := by
  have hl := lg_8
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.7256855675417 49.7256856034112 0.5397969 0.00000004598 0.8578130846929 0.5139617804172 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_9 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6487590261695):ℝ):ℂ) + (((-0.7609939066424):ℝ):ℂ) * I)‖ ≤ 0.00000015204 := by
  have hl := lg_9
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.542231305408851464 52.54223132932189929 (-2.2767489) 0.00000005203 (-0.6487590261695) (-0.7609939066424) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_10 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0837477198955:ℝ):ℂ) + ((0.9964869890832:ℝ):ℂ) * I)‖ ≤ 0.00000015451 := by
  have hl := lg_10
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.061717310118379817 55.06171734598790373 1.4869504 0.0000000545 0.0837477198955 0.9964869890832 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_11 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7022794837973:ℝ):ℂ) + (((-0.711901346141):ℝ):ℂ) * I)‖ ≤ 0.00000012485 := by
  have hl := lg_11
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.340869639779179629 57.340869675648727455 (-0.7922019) 0.00000002484 0.7022794837973 (-0.711901346141) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_12 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9641201102865):ℝ):ℂ) + (((-0.2654664059602):ℝ):ℂ) * I)‖ ≤ 0.0000001669 := by
  have hl := lg_12
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.421572697732225732 59.421572733601749645 (-2.872905) 0.00000006689 (-0.9641201102865) (-0.2654664059602) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_13 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0745081158762:ℝ):ℂ) + ((0.9972204072663:ℝ):ℂ) * I)‖ ≤ 0.00000013042 := by
  have hl := lg_13
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.3356339663294921 61.335634002199039926 1.4962191 0.00000003041 0.0745081158762 0.9972204072663 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_14 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9621736322536:ℝ):ℂ) + (((-0.2724369677484):ℝ):ℂ) * I)‖ ≤ 0.00000016737 := by
  have hl := lg_14
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.107777904441446286 63.107777940310994112 (-0.2759249) 0.00000006736 0.9621736322536 (-0.2724369677484) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v23p913_15 : ‖exp (-((((((23913:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3475482394336):ℝ):ℂ) + (((-0.9376621039928):ℝ):ℂ) * I)‖ ≤ 0.0000001315 := by
  have hl := lg_15
  refine (ecis_approx ((((23913:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.757604440308905549 64.757604476178453375 (-1.9257514) 0.00000003149 (-0.3475482394336) (-0.9376621039928) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p228_2 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4663761501946):ℝ):ℂ) + ((0.8845865059589:ℝ):ℂ) * I)‖ ≤ 0.00000013725 := by
  have hl := lg_2
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.7935698843084 16.7935698964224 2.055986 0.00000003724 (-0.4663761501946) 0.8845865059589 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p228_3 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0862517242503:ℝ):ℂ) + (((-0.9962733761693):ℝ):ℂ) * I)‖ ≤ 0.00000010696 := by
  have hl := lg_3
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.617178523552997392 26.61717853566702162 (-1.4844373) 0.00000000695 0.0862517242503 (-0.9962733761693) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p228_4 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5649864846249):ℝ):ℂ) + (((-0.8251001588787):ℝ):ℂ) * I)‖ ≤ 0.00000015696 := by
  have hl := lg_4
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.5871397686168 33.5871397928448 (-2.1712132) 0.00000005695 (-0.5649864846249) (-0.8251001588787) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p228_5 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2729387300062:ℝ):ℂ) + (((-0.9620314182305):ℝ):ℂ) * I)‖ ≤ 0.00000011324 := by
  have hl := lg_5
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.993461729857455652 38.99346175408547988 (-1.2943499) 0.00000001323 0.2729387300062 (-0.9620314182305) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p228_6 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8410642377048:ℝ):ℂ) + ((0.540935253107:ℝ):ℂ) * I)‖ ≤ 0.00000014241 := by
  have hl := lg_6
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.410748407861397392 43.41074843208942162 0.5715487 0.0000000424 0.8410642377048 0.540935253107 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p228_7 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997662694904):ℝ):ℂ) + ((0.0216195687646:ℝ):ℂ) * I)‖ ≤ 0.00000014552 := by
  have hl := lg_7
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.145511078716204216 47.145511102944252672 3.1199714 0.00000004551 (-0.9997662694904) 0.0216195687646 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p228_8 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9933686882274:ℝ):ℂ) + (((-0.1149723847251):ℝ):ℂ) * I)‖ ≤ 0.00000013185 := by
  have hl := lg_8
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.3807096529252 50.3807096892672 (-0.1152272) 0.00000003184 0.9933686882274 (-0.1149723847251) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p228_9 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9851212799752):ℝ):ℂ) + (((-0.1718605928623):ℝ):ℂ) * I)‖ ≤ 0.00000011391 := by
  have hl := lg_9
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.234357047105994784 53.23435707133404324 (-2.9688746) 0.0000000139 (-0.9851212799752) (-0.1718605928623) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v24p228_10 : ‖exp (-((((((24228:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7237078967387:ℝ):ℂ) + ((0.6901064267184:ℝ):ℂ) * I)‖ ≤ 0.00000015047 := by
  have hl := lg_10
  refine (ecis_approx ((((24228:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.787031614165855652 55.78703165050787988 0.7616361 0.00000005046 0.7237078967387 0.6901064267184 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
