/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Base
/-!
# Certificat (V2), côté b2left (b2), angles 0

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

lemma cs_b2left_vm1_2 : ‖exp (-((((((-1000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7692388889425:ℝ):ℂ) + ((0.6389612912677:ℝ):ℂ) * I)‖ ≤ 0.00000011971 := by
  have hl := lg_2
  refine (ecis_approx ((((-1000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.6931471808) (-0.6931471803) 0.6931472 0.0000000197 0.7692388889425 0.6389612912677 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm1_3 : ‖exp (-((((((-1000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4548324127347:ℝ):ℂ) + ((0.8905770468219:ℝ):ℂ) * I)‖ ≤ 0.00000011161 := by
  have hl := lg_3
  refine (ecis_approx ((((-1000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-1.098612288908165) (-1.098612288408164) 1.0986123 0.0000000116 0.4548324127347 0.8905770468219 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm1_4 : ‖exp (-((((((-1000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1834569365231:ℝ):ℂ) + ((0.983027747544:ℝ):ℂ) * I)‖ ≤ 0.00000013941 := by
  have hl := lg_4
  refine (ecis_approx ((((-1000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-1.3862943616) (-1.3862943606) 1.3862944 0.0000000394 0.1834569365231 0.983027747544 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm1_5 : ‖exp (-((((((-1000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0386319575092):ℝ):ℂ) + ((0.9992535073037:ℝ):ℂ) * I)‖ ≤ 0.00000011293 := by
  have hl := lg_5
  refine (ecis_approx ((((-1000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-1.60943791291421) (-1.609437911914209) 1.6094379 0.00000001292 (-0.0386319575092) 0.9992535073037 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p769_2 : ‖exp (-((((((-769:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.861271244536:ℝ):ℂ) + ((0.5081454942587:ℝ):ℂ) * I)‖ ≤ 0.00000011836 := by
  have hl := lg_2
  refine (ecis_approx ((((-769:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.5330301820352) (-0.5330301816507) 0.5330302 0.00000001835 0.861271244536 0.5081454942587 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p769_3 : ‖exp (-((((((-769:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6638563339787:ℝ):ℂ) + ((0.74786012585:ℝ):ℂ) * I)‖ ≤ 0.00000015019 := by
  have hl := lg_3
  refine (ecis_approx ((((-769:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.844832850170378885) (-0.844832849785878116) 0.8448328 0.00000005018 0.6638563339787 0.74786012585 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p769_4 : ‖exp (-((((((-769:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4835763133291:ℝ):ℂ) + ((0.8753022044911:ℝ):ℂ) * I)‖ ≤ 0.00000013671 := by
  have hl := lg_4
  refine (ecis_approx ((((-769:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-1.0660603640704) (-1.0660603633014) 1.0660604 0.0000000367 0.4835763133291 0.8753022044911 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p769_5 : ‖exp (-((((((-769:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3270106067972:ℝ):ℂ) + ((0.9450206680502:ℝ):ℂ) * I)‖ ≤ 0.00000014575 := by
  have hl := lg_5
  refine (ecis_approx ((((-769:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-1.23765775503102749) (-1.237657754262026721) 1.2376578 0.00000004574 0.3270106067972 0.9450206680502 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p475_2 : ‖exp (-((((((-475:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9462867586906:ℝ):ℂ) + ((0.3233285795084:ℝ):ℂ) * I)‖ ≤ 0.00000011089 := by
  have hl := lg_2
  refine (ecis_approx ((((-475:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.32924491088) (-0.3292449106425) 0.3292449 0.00000001088 0.9462867586906 0.3233285795084 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p475_3 : ‖exp (-((((((-475:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8669030529149:ℝ):ℂ) + ((0.4984767766375:ℝ):ℂ) * I)‖ ≤ 0.00000013725 := by
  have hl := lg_3
  refine (ecis_approx ((((-475:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.521840837231378375) (-0.5218408369938779) 0.5218408 0.00000003724 0.8669030529149 0.4984767766375 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p475_4 : ‖exp (-((((((-475:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7909172593462:ℝ):ℂ) + ((0.61192310699:ℝ):ℂ) * I)‖ ≤ 0.00000012177 := by
  have hl := lg_4
  refine (ecis_approx ((((-475:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.65848982176) (-0.658489821285) 0.6584898 0.00000002176 0.7909172593462 0.61192310699 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p475_5 : ‖exp (-((((((-475:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7217403026401:ℝ):ℂ) + ((0.6921639513475:ℝ):ℂ) * I)‖ ≤ 0.00000010865 := by
  have hl := lg_5
  refine (ecis_approx ((((-475:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.76448300863424975) (-0.764483008159249275) 0.764483 0.00000000864 0.7217403026401 0.6921639513475 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p232_2 : ‖exp (-((((((-232:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9870978957707:ℝ):ℂ) + ((0.1601179070718:ℝ):ℂ) * I)‖ ≤ 0.00000014596 := by
  have hl := lg_2
  refine (ecis_approx ((((-232:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.1608101459456) (-0.1608101458296) 0.1608101 0.00000004595 0.9870978957707 0.1601179070718 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p232_3 : ‖exp (-((((((-232:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9676940372143:ℝ):ℂ) + ((0.2521274486048:ℝ):ℂ) * I)‖ ≤ 0.0000001491 := by
  have hl := lg_3
  refine (ecis_approx ((((-232:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.25487805102669428) (-0.254878050910694048) 0.2548781 0.00000004909 0.9676940372143 0.2521274486048 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p232_4 : ‖exp (-((((((-232:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9487244800595:ℝ):ℂ) + ((0.316104193164:ℝ):ℂ) * I)‖ ≤ 0.00000010836 := by
  have hl := lg_4
  refine (ecis_approx ((((-232:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.3216202918912) (-0.3216202916592) 0.3216203 0.00000000835 0.9487244800595 0.316104193164 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p232_5 : ‖exp (-((((((-232:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9310962603547:ℝ):ℂ) + ((0.3647735653161:ℝ):ℂ) * I)‖ ≤ 0.00000010445 := by
  have hl := lg_5
  refine (ecis_approx ((((-232:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.37338959579609672) (-0.373389595564096488) 0.3733896 0.00000000444 0.9310962603547 0.3647735653161 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p067_2 : ‖exp (-((((((-67:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9989218152064:ℝ):ℂ) + ((0.0464242081759:ℝ):ℂ) * I)‖ ≤ 0.00000013893 := by
  have hl := lg_2
  refine (ecis_approx ((((-67:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.0464408611136) (-0.0464408610801) 0.0464409 0.00000003892 0.9989218152064 0.0464242081759 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p067_3 : ‖exp (-((((((-67:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9972922276638:ℝ):ℂ) + ((0.0735405509997:ℝ):ℂ) * I)‖ ≤ 0.00000012337 := by
  have hl := lg_3
  refine (ecis_approx ((((-67:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.073607023356847055) (-0.073607023323346988) 0.073607 0.00000002336 0.9972922276638 0.0735405509997 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p067_4 : ‖exp (-((((((-67:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9956895950653:ℝ):ℂ) + ((0.0927482090323:ℝ):ℂ) * I)‖ ≤ 0.00000012224 := by
  have hl := lg_4
  refine (ecis_approx ((((-67:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.0928817222272) (-0.0928817221602) 0.0928817 0.00000002223 0.9956895950653 0.0927482090323 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p067_5 : ‖exp (-((((((-67:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9941917289322:ℝ):ℂ) + ((0.1076234459712:ℝ):ℂ) * I)‖ ≤ 0.00000014018 := by
  have hl := lg_5
  refine (ecis_approx ((((-67:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.10783234016525207) (-0.107832340098252003) 0.1078323 0.00000004017 0.9941917289322 0.1076234459712 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p169_2 : ‖exp (-((((((169:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9931467298548:ℝ):ℂ) + (((-0.1168741758416):ℝ):ℂ) * I)‖ ≤ 0.00000012654 := by
  have hl := lg_2
  refine (ecis_approx ((((169:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.1171418734707 0.1171418735552 (-0.1171419) 0.00000002653 0.9931467298548 (-0.1168741758416) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p169_3 : ‖exp (-((((((169:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9828136165548:ℝ):ℂ) + (((-0.1846006368205):ℝ):ℂ) * I)‖ ≤ 0.00000012327 := by
  have hl := lg_3
  refine (ecis_approx ((((169:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.185665476740979716 0.185665476825479885 (-0.1856655) 0.00000002326 0.9828136165548 (-0.1846006368205) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p169_4 : ‖exp (-((((((169:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9726808772573:ℝ):ℂ) + (((-0.2321463138151):ℝ):ℂ) * I)‖ ≤ 0.00000014713 := by
  have hl := lg_4
  refine (ecis_approx ((((169:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.2342837469414 0.2342837471104 (-0.2342837) 0.00000004712 0.9726808772573 (-0.2321463138151) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p169_5 : ‖exp (-((((((169:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9632368495872:ℝ):ℂ) + (((-0.268653627553):ℝ):ℂ) * I)‖ ≤ 0.0000001073 := by
  have hl := lg_5
  refine (ecis_approx ((((169:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 0.271995007113501321 0.27199500728250149 (-0.271995) 0.00000000729 0.9632368495872 (-0.268653627553) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p346_2 : ‖exp (-((((((346:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9713786315532:ℝ):ℂ) + (((-0.2375364270211):ℝ):ℂ) * I)‖ ≤ 0.00000012457 := by
  have hl := lg_2
  refine (ecis_approx ((((346:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.2398289243838 0.2398289245568 (-0.2398289) 0.00000002456 0.9713786315532 (-0.2375364270211) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p346_3 : ‖exp (-((((((346:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9286201555371:ℝ):ℂ) + (((-0.3710318136363):ℝ):ℂ) * I)‖ ≤ 0.00000014823 := by
  have hl := lg_3
  refine (ecis_approx ((((346:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.380119851789224744 0.38011985196222509 (-0.3801199) 0.00000004822 0.9286201555371 (-0.3710318136363) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p346_4 : ‖exp (-((((((346:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8871528916761:ℝ):ℂ) + (((-0.4614756188475):ℝ):ℂ) * I)‖ ≤ 0.00000014913 := by
  have hl := lg_4
  refine (ecis_approx ((((346:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.4796578487676 0.4796578491136 (-0.4796578) 0.00000004912 0.8871528916761 (-0.4614756188475) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p346_5 : ‖exp (-((((((346:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8489159492488:ℝ):ℂ) + (((-0.5285278716502):ℝ):ℂ) * I)‖ ≤ 0.00000011788 := by
  have hl := lg_5
  refine (ecis_approx ((((346:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 0.556865517522316314 0.55686551786831666 (-0.5568655) 0.00000001787 0.8489159492488 (-0.5285278716502) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p661_2 : ‖exp (-((((((661:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8968632890208:ℝ):ℂ) + (((-0.4423078575006):ℝ):ℂ) * I)‖ ≤ 0.00000011384 := by
  have hl := lg_2
  refine (ecis_approx ((((661:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.4581702861783 0.4581702865088 (-0.4581703) 0.00000001383 0.8968632890208 (-0.4423078575006) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p661_3 : ‖exp (-((((((661:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7477146083683:ℝ):ℂ) + (((-0.6640202289333):ℝ):ℂ) * I)‖ ≤ 0.00000012298 := by
  have hl := lg_3
  refine (ecis_approx ((((661:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.726182722637796404 0.726182722968297065 (-0.7261827) 0.00000002297 0.7477146083683 (-0.6640202289333) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p661_4 : ‖exp (-((((((661:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6087275183865:ℝ):ℂ) + (((-0.7933793596755):ℝ):ℂ) * I)‖ ≤ 0.00000012766 := by
  have hl := lg_4
  refine (ecis_approx ((((661:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.9163405723566 0.9163405730176 (-0.9163406) 0.00000002765 0.6087275183865 (-0.7933793596755) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p661_5 : ‖exp (-((((((661:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4855199520282:ℝ):ℂ) + (((-0.8742255865522):ℝ):ℂ) * I)‖ ≤ 0.00000014024 := by
  have hl := lg_5
  refine (ecis_approx ((((661:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 1.063838459775292149 1.06383846043629281 (-1.0638385) 0.00000004023 0.4855199520282 (-0.8742255865522) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p976_2 : ‖exp (-((((((976:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7797614647762:ℝ):ℂ) + (((-0.626076718981):ℝ):ℂ) * I)‖ ≤ 0.00000014848 := by
  have hl := lg_2
  refine (ecis_approx ((((976:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.6765116479728 0.6765116484608 (-0.6765116) 0.00000004847 0.7797614647762 (-0.626076718981) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p976_3 : ‖exp (-((((((976:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4781531786663:ℝ):ℂ) + (((-0.8782764586002):ℝ):ℂ) * I)‖ ≤ 0.00000010653 := by
  have hl := lg_3
  refine (ecis_approx ((((976:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.072245593486368064 1.07224559397436904 (-1.0722456) 0.00000000652 0.4781531786663 (-0.8782764586002) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p976_4 : ‖exp (-((((((976:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2160557862618:ℝ):ℂ) + (((-0.9763810205154):ℝ):ℂ) * I)‖ ≤ 0.00000010407 := by
  have hl := lg_4
  refine (ecis_approx ((((976:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 1.3530232959456 1.3530232969216 (-1.3530233) 0.00000000406 0.2160557862618 (-0.9763810205154) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p976_5 : ‖exp (-((((((976:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0000150732051):ℝ):ℂ) + (((-0.9999999998863):ℝ):ℂ) * I)‖ ≤ 0.00000010302 := by
  have hl := lg_5
  refine (ecis_approx ((((976:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 1.570811402028267984 1.57081140300426896 (-1.5708114) 0.00000000301 (-0.0000150732051) (-0.9999999998863) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p397_2 : ‖exp (-((((((1397:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.566679102774:ℝ):ℂ) + (((-0.8239385865944):ℝ):ℂ) * I)‖ ≤ 0.00000011159 := by
  have hl := lg_2
  refine (ecis_approx ((((1397:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.9683266108791 0.9683266115776 (-0.9683266) 0.00000001158 0.566679102774 (-0.8239385865944) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p397_3 : ‖exp (-((((((1397:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0360271286467:ℝ):ℂ) + (((-0.9993508122783):ℝ):ℂ) * I)‖ ≤ 0.00000013311 := by
  have hl := lg_3
  refine (ecis_approx ((((1397:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.534761366906205108 1.534761367604706505 (-1.5347614) 0.0000000331 0.0360271286467 (-0.9993508122783) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p397_4 : ‖exp (-((((((1397:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3577495889585):ℝ):ℂ) + (((-0.9338175579831):ℝ):ℂ) * I)‖ ≤ 0.00000012317 := by
  have hl := lg_4
  refine (ecis_approx ((((1397:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 1.9366532217582 1.9366532231552 (-1.9366532) 0.00000002316 (-0.3577495889585) (-0.9338175579831) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p397_5 : ‖exp (-((((((1397:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6269160600285):ℝ):ℂ) + (((-0.7790868075279):ℝ):ℂ) * I)‖ ≤ 0.00000013707 := by
  have hl := lg_5
  refine (ecis_approx ((((1397:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 2.248384762944149973 2.24838476434115137 (-2.2483848) 0.00000003706 (-0.6269160600285) (-0.7790868075279) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p818_2 : ‖exp (-((((((1818:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3056820893205:ℝ):ℂ) + (((-0.9521336357196):ℝ):ℂ) * I)‖ ≤ 0.00000012623 := by
  have hl := lg_2
  refine (ecis_approx ((((1818:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.2601415737854 1.2601415746944 (-1.2601416) 0.00000002622 0.3056820893205 (-0.9521336357196) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p818_3 : ‖exp (-((((((1818:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4136693709495):ℝ):ℂ) + (((-0.9104271807974):ℝ):ℂ) * I)‖ ≤ 0.00000014125 := by
  have hl := lg_3
  refine (ecis_approx ((((1818:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.997277140326042152 1.99727714123504397 (-1.9972771) 0.00000004124 (-0.4136693709495) (-0.9104271807974) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p818_4 : ‖exp (-((((((1818:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8131168623156):ℝ):ℂ) + (((-0.5821004794394):ℝ):ℂ) * I)‖ ≤ 0.0000001494 := by
  have hl := lg_4
  refine (ecis_approx ((((1818:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 2.5202831475708 2.5202831493888 (-2.5202831) 0.00000004939 (-0.8131168623156) (-0.5821004794394) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p818_5 : ‖exp (-((((((1818:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9768408170226):ℝ):ℂ) + (((-0.213967329032):ℝ):ℂ) * I)‖ ≤ 0.00000012569 := by
  have hl := lg_5
  refine (ecis_approx ((((1818:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 2.925958123860031962 2.92595812567803378 (-2.9259581) 0.00000002568 (-0.9768408170226) (-0.213967329032) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p38_2 : ‖exp (-((((((2380:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.078812155918):ℝ):ℂ) + (((-0.9968894843859):ℝ):ℂ) * I)‖ ≤ 0.0000001109 := by
  have hl := lg_2
  refine (ecis_approx ((((2380:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.649690289114 1.649690290304 (-1.6496903) 0.00000001089 (-0.078812155918) (-0.9968894843859) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p38_3 : ‖exp (-((((((2380:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8643723617378):ℝ):ℂ) + (((-0.5028522846524):ℝ):ℂ) * I)‖ ≤ 0.00000014762 := by
  have hl := lg_3
  refine (ecis_approx ((((2380:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 2.61469724641143032 2.6146972476014327 (-2.6146972) 0.00000004761 (-0.8643723617378) (-0.5028522846524) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p38_4 : ‖exp (-((((((2380:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9875772868669):ℝ):ℂ) + ((0.1571340258578:ℝ):ℂ) * I)‖ ≤ 0.00000012897 := by
  have hl := lg_4
  refine (ecis_approx ((((2380:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.299380578228 3.299380580608 2.9838047 0.00000002896 (-0.9875772868669) 0.1571340258578 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p38_5 : ‖exp (-((((((2380:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.771965093218):ℝ):ℂ) + ((0.6356649233779:ℝ):ℂ) * I)‖ ≤ 0.00000012557 := by
  have hl := lg_5
  refine (ecis_approx ((((2380:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.83046223035581742 3.8304622327358198 2.4527231 0.00000002556 (-0.771965093218) 0.6356649233779 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p942_2 : ‖exp (-((((((2942:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4514972735707):ℝ):ℂ) + (((-0.8922724987097):ℝ):ℂ) * I)‖ ≤ 0.00000010593 := by
  have hl := lg_2
  refine (ecis_approx ((((2942:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.0392390044426 2.0392390059136 (-2.039239) 0.00000000592 (-0.4514972735707) (-0.8922724987097) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p942_3 : ‖exp (-((((((2942:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9959054406104):ℝ):ℂ) + ((0.0904010667498:ℝ):ℂ) * I)‖ ≤ 0.0000001468 := by
  have hl := lg_3
  refine (ecis_approx ((((2942:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.232117352496818488 3.23211735396782143 3.051068 0.00000004679 (-0.9959054406104) 0.0904010667498 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p942_4 : ‖exp (-((((((2942:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5923004181309):ℝ):ℂ) + ((0.8057172051474:ℝ):ℂ) * I)‖ ≤ 0.00000010466 := by
  have hl := lg_4
  refine (ecis_approx ((((2942:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.0784780088852 4.0784780118272 2.2047073 0.00000000465 (-0.5923004181309) 0.8057172051474 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p942_5 : ‖exp (-((((((2942:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0225754087656:ℝ):ℂ) + ((0.9997451429834:ℝ):ℂ) * I)‖ ≤ 0.00000013263 := by
  have hl := lg_5
  refine (ecis_approx ((((2942:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.734966336851602878 4.73496633979360582 1.548219 0.00000003262 0.0225754087656 0.9997451429834 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v3p504_2 : ‖exp (-((((((3504:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7565305316015):ℝ):ℂ) + (((-0.6539583738429):ℝ):ℂ) * I)‖ ≤ 0.00000012154 := by
  have hl := lg_2
  refine (ecis_approx ((((3504:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.4287877197712 2.4287877215232 (-2.4287877) 0.00000002153 (-0.7565305316015) (-0.6539583738429) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v3p504_3 : ‖exp (-((((((3504:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7596998873575):ℝ):ℂ) + ((0.6502738508603:ℝ):ℂ) * I)‖ ≤ 0.00000014861 := by
  have hl := lg_3
  refine (ecis_approx ((((3504:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.849537458582206656 3.84953746033421016 2.4336478 0.0000000486 (-0.7596998873575) 0.6502738508603 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v3p504_4 : ‖exp (-((((((3504:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1446768976131:ℝ):ℂ) + ((0.9894789514168:ℝ):ℂ) * I)‖ ≤ 0.00000013588 := by
  have hl := lg_4
  refine (ecis_approx ((((3504:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.8575754395424 4.8575754430464 1.4256099 0.00000003587 0.1446768976131 0.9894789514168 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v3p504_5 : ‖exp (-((((((3504:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7998717069943:ℝ):ℂ) + ((0.6001710192521:ℝ):ℂ) * I)‖ ≤ 0.00000013969 := by
  have hl := lg_5
  refine (ecis_approx ((((3504:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.639470443347388336 5.63947044685139184 0.6437149 0.00000003968 0.7998717069943 0.6001710192521 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p066_2 : ‖exp (-((((((4066:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9482060788741):ℝ):ℂ) + (((-0.3176558385856):ℝ):ℂ) * I)‖ ≤ 0.00000013715 := by
  have hl := lg_2
  refine (ecis_approx ((((4066:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.8183364350998 2.8183364371328 (-2.8183364) 0.00000003714 (-0.9482060788741) (-0.3176558385856) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p066_3 : ‖exp (-((((((4066:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2429747934552):ℝ):ℂ) + ((0.9700326024131:ℝ):ℂ) * I)‖ ≤ 0.00000014253 := by
  have hl := lg_3
  refine (ecis_approx ((((4066:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.466957564667594824 4.46695756670059889 1.8162277 0.00000004252 (-0.2429747934552) 0.9700326024131 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p066_4 : ‖exp (-((((((4066:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7981896008594:ℝ):ℂ) + ((0.6024063089642:ℝ):ℂ) * I)‖ ≤ 0.00000013699 := by
  have hl := lg_4
  refine (ecis_approx ((((4066:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.6366728701996 5.6366728742656 0.6465124 0.00000003698 0.7981896008594 0.6024063089642 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p066_5 : ‖exp (-((((((4066:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9661867892325:ℝ):ℂ) + (((-0.2578431467241):ℝ):ℂ) * I)‖ ≤ 0.00000014674 := by
  have hl := lg_5
  refine (ecis_approx ((((4066:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.543974549843173794 6.54397455390917786 (-0.2607892) 0.00000004673 0.9661867892325 (-0.2578431467241) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p628_2 : ‖exp (-((((((4628:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9978034596475):ℝ):ℂ) + ((0.0662439082184:ℝ):ℂ) * I)‖ ≤ 0.00000014558 := by
  have hl := lg_2
  refine (ecis_approx ((((4628:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.2078851504284 3.2078851527424 3.0753002 0.00000004557 (-0.9978034596475) 0.0662439082184 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p628_3 : ‖exp (-((((((4628:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3634688600161:ℝ):ℂ) + ((0.9316063480884:ℝ):ℂ) * I)‖ ≤ 0.00000013644 := by
  have hl := lg_3
  refine (ecis_approx ((((4628:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.084377670752982992 5.08437767306698762 1.1988076 0.00000003643 0.3634688600161 0.9316063480884 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p628_4 : ‖exp (-((((((4628:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9912234769113:ℝ):ℂ) + (((-0.1321968941383):ℝ):ℂ) * I)‖ ≤ 0.00000010634 := by
  have hl := lg_4
  refine (ecis_approx ((((4628:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.4157703008568 6.4157703054848 (-0.132585) 0.00000000633 0.9912234769113 (-0.1321968941383) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p628_5 : ‖exp (-((((((4628:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3944809517434:ℝ):ℂ) + (((-0.9189041183451):ℝ):ℂ) * I)‖ ≤ 0.00000015086 := by
  have hl := lg_5
  refine (ecis_approx ((((4628:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.448478656338959252 7.44847866096696388 (-1.1652934) 0.00000005085 0.3944809517434 (-0.9189041183451) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p19_2 : ‖exp (-((((((5190:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8978910110868):ℝ):ℂ) + ((0.4402178234642:ℝ):ℂ) * I)‖ ≤ 0.00000014144 := by
  have hl := lg_2
  refine (ecis_approx ((((5190:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.597433865757 3.597433868352 2.6857514 0.00000004143 (-0.8978910110868) 0.4402178234642 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p19_3 : ‖exp (-((((((5190:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8357014617863:ℝ):ℂ) + ((0.5491840008305:ℝ):ℂ) * I)‖ ≤ 0.00000013036 := by
  have hl := lg_3
  refine (ecis_approx ((((5190:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.70179777683837116 5.70179777943337635 0.5813875 0.00000003035 0.8357014617863 0.5491840008305 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p19_4 : ‖exp (-((((((5190:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6124166204296:ℝ):ℂ) + (((-0.7905351877188):ℝ):ℂ) * I)‖ ≤ 0.00000012954 := by
  have hl := lg_4
  refine (ecis_approx ((((5190:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.194867731514 7.194867736704 (-0.9116824) 0.00000002953 0.6124166204296 (-0.7905351877188) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p19_5 : ‖exp (-((((((5190:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4785487466217):ℝ):ℂ) + (((-0.8780609871195):ℝ):ℂ) * I)‖ ≤ 0.00000014436 := by
  have hl := lg_5
  refine (ecis_approx ((((5190:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.35298276283474471 8.3529827680247499 (-2.0697975) 0.00000004435 (-0.4785487466217) (-0.8780609871195) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p752_2 : ‖exp (-((((((5752:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6634395580072):ℝ):ℂ) + ((0.7482298796846:ℝ):ℂ) * I)‖ ≤ 0.00000012611 := by
  have hl := lg_2
  refine (ecis_approx ((((5752:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.9869825810856 3.9869825839616 2.2962027 0.0000000261 (-0.6634395580072) 0.7482298796846 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p752_3 : ‖exp (-((((((5752:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9993508961034:ℝ):ℂ) + (((-0.0360248033622):ℝ):ℂ) * I)‖ ≤ 0.00000012427 := by
  have hl := lg_3
  refine (ecis_approx ((((5752:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.319217882923759328 6.31921788579976508 (-0.0360326) 0.00000002426 0.9993508961034 (-0.0360248033622) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p752_4 : ‖exp (-((((((5752:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.119695898609):ℝ):ℂ) + (((-0.9928106022075):ℝ):ℂ) * I)‖ ≤ 0.00000014502 := by
  have hl := lg_4
  refine (ecis_approx ((((5752:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.9739651621712 7.9739651679232 (-1.6907799) 0.00000004501 (-0.119695898609) (-0.9928106022075) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p752_5 : ‖exp (-((((((5752:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9860394558088):ℝ):ℂ) + (((-0.1665118350739):ℝ):ℂ) * I)‖ ≤ 0.00000013786 := by
  have hl := lg_5
  refine (ecis_approx ((((5752:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.257486869330530168 9.25748687508253592 (-2.9743016) 0.00000003785 (-0.9860394558088) (-0.1665118350739) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p314_2 : ‖exp (-((((((6314:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3295790442701):ℝ):ℂ) + ((0.9441279858027:ℝ):ℂ) * I)‖ ≤ 0.00000011078 := by
  have hl := lg_2
  refine (ecis_approx ((((6314:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.3765312964142 4.3765312995712 1.906654 0.00000001077 (-0.3295790442701) 0.9441279858027 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p314_3 : ‖exp (-((((((6314:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7939895304901:ℝ):ℂ) + (((-0.6079314315546):ℝ):ℂ) * I)‖ ≤ 0.00000011819 := by
  have hl := lg_3
  refine (ecis_approx ((((6314:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.936637989009147496 6.93663799216615381 (-0.6534527) 0.00000001818 0.7939895304901 (-0.6079314315546) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p314_4 : ‖exp (-((((((6314:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7827553026799):ℝ):ℂ) + (((-0.6223296040551):ℝ):ℂ) * I)‖ ≤ 0.00000011437 := by
  have hl := lg_4
  refine (ecis_approx ((((6314:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.7530625928284 8.7530625991424 (-2.4698773) 0.00000001436 (-0.7827553026799) (-0.6223296040551) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p314_5 : ‖exp (-((((((6314:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7403448926998):ℝ):ℂ) + ((0.6722272233566:ℝ):ℂ) * I)‖ ≤ 0.00000013855 := by
  have hl := lg_5
  refine (ecis_approx ((((6314:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.161990975826315626 10.16199098214032194 2.4043796 0.00000003854 (-0.7403448926998) 0.6722272233566 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p876_2 : ‖exp (-((((((6876:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0536652344231:ℝ):ℂ) + ((0.9985589830422:ℝ):ℂ) * I)‖ ≤ 0.00000010802 := by
  have hl := lg_2
  refine (ecis_approx ((((6876:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.7660800117428 4.7660800151808 1.5171053 0.00000000801 0.0536652344231 0.9985589830422 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p876_3 : ‖exp (-((((((6876:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.295447148154:ℝ):ℂ) + (((-0.9553590857095):ℝ):ℂ) * I)‖ ≤ 0.0000001121 := by
  have hl := lg_3
  refine (ecis_approx ((((6876:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.554058095094535664 7.55405809853254254 (-1.2708728) 0.00000001209 0.295447148154 (-0.9553590857095) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p876_4 : ‖exp (-((((((6876:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9942400850194):ℝ):ℂ) + ((0.1071758036018:ℝ):ℂ) * I)‖ ≤ 0.00000011602 := by
  have hl := lg_4
  refine (ecis_approx ((((6876:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.5321600234856 9.5321600303616 3.0342106 0.00000001601 (-0.9942400850194) 0.1071758036018 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p876_5 : ‖exp (-((((((6876:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.070861389245:ℝ):ℂ) + ((0.9974861720917:ℝ):ℂ) * I)‖ ≤ 0.00000013205 := by
  have hl := lg_5
  refine (ecis_approx ((((6876:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.066495082322101084 11.06649508919810796 1.4998755 0.00000003204 0.070861389245 0.9974861720917 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p438_2 : ‖exp (-((((((7438:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4288683728525:ℝ):ℂ) + ((0.9033669900804:ℝ):ℂ) * I)‖ ≤ 0.00000012363 := by
  have hl := lg_2
  refine (ecis_approx ((((7438:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.1556287270714 5.1556287307904 1.1275566 0.00000002362 0.4288683728525 0.9033669900804 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p438_3 : ‖exp (-((((((7438:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3121892360014):ℝ):ℂ) + (((-0.9500199371187):ℝ):ℂ) * I)‖ ≤ 0.00000010601 := by
  have hl := lg_3
  refine (ecis_approx ((((7438:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.171478201179923832 8.17147820489893127 (-1.8882929) 0.000000006 (-0.3121892360014) (-0.9500199371187) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p438_4 : ‖exp (-((((((7438:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6321438375323):ℝ):ℂ) + ((0.7748510622404:ℝ):ℂ) * I)‖ ≤ 0.00000014724 := by
  have hl := lg_4
  refine (ecis_approx ((((7438:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.3112574541428 10.3112574615808 2.2551132 0.00000004723 (-0.6321438375323) 0.7748510622404 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p438_5 : ‖exp (-((((((7438:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8279402687764:ℝ):ℂ) + ((0.5608162901864:ℝ):ℂ) * I)‖ ≤ 0.00000012556 := by
  have hl := lg_5
  refine (ecis_approx ((((7438:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.970999188817886542 11.97099919625589398 0.5953714 0.00000002555 0.8279402687764 0.5608162901864 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8_2 : ‖exp (-((((((8000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.739810341498:ℝ):ℂ) + ((0.6728154714426:ℝ):ℂ) * I)‖ ≤ 0.00000013924 := by
  have hl := lg_2
  refine (ecis_approx ((((8000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.5451774424 5.5451774464 0.7380079 0.00000003923 0.739810341498 0.6728154714426 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8_3 : ‖exp (-((((((8000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8045495943219):ℝ):ℂ) + (((-0.5938854689463):ℝ):ℂ) * I)‖ ≤ 0.0000001041 := by
  have hl := lg_3
  refine (ecis_approx ((((8000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.788898307265312 8.78889831126532 (-2.505713) 0.00000000409 (-0.8045495943219) (-0.5938854689463) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8_4 : ‖exp (-((((((8000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.094638782326:ℝ):ℂ) + ((0.9955116779223:ℝ):ℂ) * I)‖ ≤ 0.00000012957 := by
  have hl := lg_4
  refine (ecis_approx ((((8000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.0903548848 11.0903548928 1.4760157 0.00000002956 0.094638782326 0.9955116779223 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8_5 : ‖exp (-((((((8000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9525977890309:ℝ):ℂ) + (((-0.3042325629079):ℝ):ℂ) * I)‖ ≤ 0.00000011906 := by
  have hl := lg_5
  refine (ecis_approx ((((8000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.875503295313672 12.87550330331368 (-0.3091327) 0.00000001905 0.9525977890309 (-0.3042325629079) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p562_2 : ‖exp (-((((((8562:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9398999686595:ℝ):ℂ) + ((0.3414499215315:ℝ):ℂ) * I)‖ ≤ 0.00000014947 := by
  have hl := lg_2
  refine (ecis_approx ((((8562:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.9347261577286 5.9347261620096 0.3484591 0.00000004946 0.9398999686595 0.3414499215315 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p562_3 : ‖exp (-((((((8562:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998296269624):ℝ):ℂ) + (((-0.0184585049548):ℝ):ℂ) * I)‖ ≤ 0.00000011047 := by
  have hl := lg_3
  refine (ecis_approx ((((8562:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.406318413350700168 9.40631841763170873 (-3.1231331) 0.00000001046 (-0.9998296269624) (-0.0184585049548) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p562_4 : ‖exp (-((((((8562:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7668238379865:ℝ):ℂ) + ((0.6418576177749:ℝ):ℂ) * I)‖ ≤ 0.00000010968 := by
  have hl := lg_4
  refine (ecis_approx ((((8562:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.8694523154572 11.8694523240192 0.6969183 0.00000000967 0.7668238379865 0.6418576177749 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p562_5 : ‖exp (-((((((8562:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3496144258754:ℝ):ℂ) + (((-0.9368936723128):ℝ):ℂ) * I)‖ ≤ 0.00000011256 := by
  have hl := lg_5
  refine (ecis_approx ((((8562:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.780007401809457458 13.78000741037146602 (-1.2136368) 0.00000001255 0.3496144258754 (-0.9368936723128) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p124_2 : ‖exp (-((((((9124:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9991559411519:ℝ):ℂ) + (((-0.0410780386692):ℝ):ℂ) * I)‖ ≤ 0.00000013414 := by
  have hl := lg_2
  refine (ecis_approx ((((9124:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.3242748730572 6.3242748776192 (-0.0410896) 0.00000003413 0.9991559411519 (-0.0410780386692) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p124_3 : ‖exp (-((((((9124:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.825922084516):ℝ):ℂ) + ((0.5637842763401:ℝ):ℂ) * I)‖ ≤ 0.00000010965 := by
  have hl := lg_3
  refine (ecis_approx ((((9124:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.023738519436088336 10.02373852399809746 2.5426321 0.00000000964 (-0.825922084516) 0.5637842763401 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p124_4 : ‖exp (-((((((9124:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9966251976869:ℝ):ℂ) + (((-0.0820866331119):ℝ):ℂ) * I)‖ ≤ 0.00000014089 := by
  have hl := lg_4
  refine (ecis_approx ((((9124:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.6485497461144 12.6485497552384 (-0.0821791) 0.00000004088 0.9966251976869 (-0.0820866331119) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p124_5 : ‖exp (-((((((9124:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5204215723228):ℝ):ℂ) + (((-0.8539094723997):ℝ):ℂ) * I)‖ ≤ 0.00000010607 := by
  have hl := lg_5
  refine (ecis_approx ((((9124:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.684511508305242916 14.68451151742925204 (-2.1181409) 0.00000000606 (-0.5204215723228) (-0.8539094723997) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p686_2 : ‖exp (-((((((9686:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9086994758912:ℝ):ℂ) + (((-0.4174509103056):ℝ):ℂ) * I)‖ ≤ 0.00000011881 := by
  have hl := lg_2
  refine (ecis_approx ((((9686:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.7138235883858 6.7138235932288 (-0.4306383) 0.0000000188 0.9086994758912 (-0.4174509103056) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p686_3 : ‖exp (-((((((9686:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3470424139593):ℝ):ℂ) + ((0.9378494350966:ℝ):ℂ) * I)‖ ≤ 0.00000011602 := by
  have hl := lg_3
  refine (ecis_approx ((((9686:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.641158625521476504 10.64115863036448619 1.925212 0.00000001601 (-0.3470424139593) 0.9378494350966 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p686_4 : ‖exp (-((((((9686:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.65146947497:ℝ):ℂ) + (((-0.7586748468101):ℝ):ℂ) * I)‖ ≤ 0.0000001376 := by
  have hl := lg_4
  refine (ecis_approx ((((9686:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.4276471767716 13.4276471864576 (-0.8612766) 0.00000003759 0.65146947497 (-0.7586748468101) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p686_5 : ‖exp (-((((((9686:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9929340646098):ℝ):ℂ) + (((-0.1186673623805):ℝ):ℂ) * I)‖ ≤ 0.00000011014 := by
  have hl := lg_5
  refine (ecis_approx ((((9686:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.589015614801028374 15.58901562448703806 (-3.022645) 0.00000001013 (-0.9929340646098) (-0.1186673623805) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p248_2 : ‖exp (-((((((10248:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.68208447109:ℝ):ℂ) + (((-0.7312733923082):ℝ):ℂ) * I)‖ ≤ 0.00000010348 := by
  have hl := lg_2
  refine (ecis_approx ((((10248:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.1033723037144 7.1033723088384 (-0.820187) 0.00000000347 0.68208447109 (-0.7312733923082) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p248_3 : ‖exp (-((((((10248:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2599828351905:ℝ):ℂ) + ((0.9656132380028:ℝ):ℂ) * I)‖ ≤ 0.00000012239 := by
  have hl := lg_3
  refine (ecis_approx ((((10248:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.258578731606864672 11.25857873673087492 1.3077919 0.00000002238 0.2599828351905 0.9656132380028 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p248_4 : ‖exp (-((((((10248:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0695215485959):ℝ):ℂ) + (((-0.9975804500292):ℝ):ℂ) * I)‖ ≤ 0.00000010695 := by
  have hl := lg_4
  refine (ecis_approx ((((10248:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.2067446074288 14.2067446176768 (-1.640374) 0.00000000694 (-0.0695215485959) (-0.9975804500292) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p248_5 : ‖exp (-((((((10248:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7069948442566):ℝ):ℂ) + ((0.7072187003818:ℝ):ℂ) * I)‖ ≤ 0.00000011002 := by
  have hl := lg_5
  refine (ecis_approx ((((10248:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.493519721296813832 16.49351973154482408 2.3560362 0.00000001001 (-0.7069948442566) 0.7072187003818 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p81_2 : ‖exp (-((((((10810:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3532666721957:ℝ):ℂ) + (((-0.9355226658482):ℝ):ℂ) * I)‖ ≤ 0.00000011728 := by
  have hl := lg_2
  refine (ecis_approx ((((10810:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.492921019043 7.492921024448 (-1.2097357) 0.00000001727 0.3532666721957 (-0.9355226658482) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p81_3 : ‖exp (-((((((10810:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7710092971715:ℝ):ℂ) + ((0.6368238874878:ℝ):ℂ) * I)‖ ≤ 0.00000012875 := by
  have hl := lg_3
  refine (ecis_approx ((((10810:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.87599883769225284 11.87599884309726365 0.6903718 0.00000002874 0.7710092971715 0.6368238874878 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p81_4 : ‖exp (-((((((10810:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7504053166259):ℝ):ℂ) + (((-0.6609779578365):ℝ):ℂ) * I)‖ ≤ 0.00000013455 := by
  have hl := lg_4
  refine (ecis_approx ((((10810:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.985842038086 14.985842048896 (-2.4194714) 0.00000003454 (-0.7504053166259) (-0.6609779578365) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p81_5 : ‖exp (-((((((10810:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1189816929589:ℝ):ℂ) + ((0.9928964481458:ℝ):ℂ) * I)‖ ≤ 0.00000011708 := by
  have hl := lg_5
  refine (ecis_approx ((((10810:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.39802382779259929 17.3980238386026101 1.4515321 0.00000001707 0.1189816929589 0.9928964481458 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p372_2 : ‖exp (-((((((11372:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0284842200158):ℝ):ℂ) + (((-0.9995942422853):ℝ):ℂ) * I)‖ ≤ 0.00000013289 := by
  have hl := lg_2
  refine (ecis_approx ((((11372:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.8824697343716 7.8824697400576 (-1.5992844) 0.00000003288 (-0.0284842200158) (-0.9995942422853) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p372_3 : ‖exp (-((((((11372:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9973402046558:ℝ):ℂ) + ((0.0728870096599:ℝ):ℂ) * I)‖ ≤ 0.00000013512 := by
  have hl := lg_3
  refine (ecis_approx ((((11372:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.493418943777641008 12.49341894946365238 0.0729517 0.00000003511 0.9973402046558 0.0728870096599 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p372_4 : ‖exp (-((((((11372:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9983772920518):ℝ):ℂ) + ((0.0569454313966:ℝ):ℂ) * I)‖ ≤ 0.00000015281 := by
  have hl := lg_4
  refine (ecis_approx ((((11372:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.7649394687432 15.7649394801152 3.0846164 0.0000000528 (-0.9983772920518) 0.0569454313966 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p372_5 : ‖exp (-((((((11372:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8540741811373:ℝ):ℂ) + ((0.520151221391:ℝ):ℂ) * I)‖ ≤ 0.00000012414 := by
  have hl := lg_5
  refine (ecis_approx ((((11372:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.302527934288384748 18.30252794566039612 0.547028 0.00000002413 0.8540741811373 0.520151221391 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p934_2 : ‖exp (-((((((11934:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4059670677304):ℝ):ℂ) + (((-0.9138877064032):ℝ):ℂ) * I)‖ ≤ 0.0000001485 := by
  have hl := lg_2
  refine (ecis_approx ((((11934:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.2720184497002 8.2720184556672 (-1.9888331) 0.00000004849 (-0.4059670677304) (-0.9138877064032) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p934_3 : ‖exp (-((((((11934:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8554027609956:ℝ):ℂ) + (((-0.517963431606):ℝ):ℂ) * I)‖ ≤ 0.00000014149 := by
  have hl := lg_3
  refine (ecis_approx ((((11934:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.110839049863029176 13.11083905583004111 (-0.5444684) 0.00000004148 0.8554027609956 (-0.517963431606) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p934_4 : ‖exp (-((((((11934:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6703814003056):ℝ):ℂ) + ((0.7420166966484:ℝ):ℂ) * I)‖ ≤ 0.00000012215 := by
  have hl := lg_4
  refine (ecis_approx ((((11934:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.5440368994004 16.5440369113344 2.305519 0.00000002214 (-0.6703814003056) 0.7420166966484 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p934_5 : ‖exp (-((((((11934:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9367829468082:ℝ):ℂ) + (((-0.3499110037842):ℝ):ℂ) * I)‖ ≤ 0.00000013119 := by
  have hl := lg_5
  refine (ecis_approx ((((11934:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.207032040784170206 19.20703205271818214 (-0.3574761) 0.00000003118 0.9367829468082 (-0.3499110037842) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p355_2 : ‖exp (-((((((12355:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6517213543091):ℝ):ℂ) + (((-0.7584584868801):ℝ):ℂ) * I)‖ ≤ 0.00000011162 := by
  have hl := lg_2
  refine (ecis_approx ((((12355:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.5638334126065 8.563833418784 (-2.2806481) 0.00000001161 (-0.6517213543091) (-0.7584584868801) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p355_3 : ‖exp (-((((((12355:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5344121743321:ℝ):ℂ) + (((-0.8452240105):ℝ):ℂ) * I)‖ ≤ 0.00000011512 := by
  have hl := lg_3
  refine (ecis_approx ((((12355:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.57335482328286622 13.573354829460378575 (-1.0069842) 0.00000001511 0.5344121743321 (-0.8452240105) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p355_4 : ‖exp (-((((((12355:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1505185455726):ℝ):ℂ) + ((0.9886071856092:ℝ):ℂ) * I)‖ ≤ 0.00000011604 := by
  have hl := lg_4
  refine (ecis_approx ((((12355:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.127666825213 17.127666837568 1.7218891 0.00000001603 (-0.1505185455726) 0.9886071856092 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p355_5 : ‖exp (-((((((12355:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5104833688501:ℝ):ℂ) + (((-0.8598876264533):ℝ):ℂ) * I)‖ ≤ 0.00000011985 := by
  have hl := lg_5
  refine (ecis_approx ((((12355:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.884605401700052195 19.88460541405506455 (-1.0350495) 0.00000001984 0.5104833688501 (-0.8598876264533) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p355_6 : ‖exp (-((((((12355:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9893551488842):ℝ):ℂ) + ((0.1455210946101:ℝ):ℂ) * I)‖ ≤ 0.00000011954 := by
  have hl := lg_6
  refine (ecis_approx ((((12355:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.13718823588936622 22.137188248244378575 2.995553 0.00000001953 (-0.9893551488842) 0.1455210946101 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p355_7 : ‖exp (-((((((12355:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4615796137665:ℝ):ℂ) + ((0.8870987882729:ℝ):ℂ) * I)‖ ≤ 0.00000014358 := by
  have hl := lg_7
  refine (ecis_approx ((((12355:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.04171988515513881 24.04171989751016352 1.0910213 0.00000004357 0.4615796137665 0.8870987882729 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p355_8 : ‖exp (-((((((12355:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8479136604952:ℝ):ℂ) + (((-0.5301343455632):ℝ):ℂ) * I)‖ ≤ 0.00000012765 := by
  have hl := lg_8
  refine (ecis_approx ((((12355:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.6915002378195 25.691500256352 (-0.558759) 0.00000002764 0.8479136604952 (-0.5301343455632) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p355_9 : ‖exp (-((((((12355:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4288072558513):ℝ):ℂ) + (((-0.9033960024957):ℝ):ℂ) * I)‖ ≤ 0.00000013022 := by
  have hl := lg_9
  refine (ecis_approx ((((12355:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.14670964656573244 27.14670965892075715 (-2.0139684) 0.00000003021 (-0.4288072558513) (-0.9033960024957) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p355_10 : ‖exp (-((((((12355:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9848819791601):ℝ):ℂ) + ((0.1732266918424:ℝ):ℂ) * I)‖ ≤ 0.00000012161 := by
  have hl := lg_10
  refine (ecis_approx ((((12355:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.448438814306552195 28.44843883283906455 2.9674877 0.0000000216 (-0.9848819791601) 0.1732266918424 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p776_2 : ‖exp (-((((((12776:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8423703769216):ℝ):ℂ) + (((-0.5388990146732):ℝ):ℂ) * I)‖ ≤ 0.00000013168 := by
  have hl := lg_2
  refine (ecis_approx ((((12776:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.8556483755128 8.8556483819008 (-2.5724631) 0.00000003167 (-0.8423703769216) (-0.5388990146732) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p776_3 : ‖exp (-((((((12776:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1011231829629:ℝ):ℂ) + (((-0.9948739125474):ℝ):ℂ) * I)‖ ≤ 0.00000011767 := by
  have hl := lg_3
  refine (ecis_approx ((((12776:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.035870596702703264 14.03587060309071604 (-1.4695) 0.00000001766 0.1011231829629 (-0.9948739125474) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p776_4 : ‖exp (-((((((12776:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4191756196137:ℝ):ℂ) + ((0.9079051712164:ℝ):ℂ) * I)‖ ≤ 0.00000014228 := by
  have hl := lg_4
  refine (ecis_approx ((((12776:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.7112967510256 17.7112967638016 1.1382592 0.00000004227 0.4191756196137 0.9079051712164 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p776_5 : ‖exp (-((((((12776:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1413514838649):ℝ):ℂ) + (((-0.9899594729122):ℝ):ℂ) * I)‖ ≤ 0.00000015387 := by
  have hl := lg_5
  refine (ecis_approx ((((12776:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.562178762615934184 20.56217877539194696 (-1.7126228) 0.00000005386 (-0.1413514838649) (-0.9899594729122) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p776_6 : ‖exp (-((((((12776:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6213198177126):ℝ):ℂ) + ((0.7835570713763:ℝ):ℂ) * I)‖ ≤ 0.00000015629 := by
  have hl := lg_6
  refine (ecis_approx ((((12776:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.891518972215503264 22.89151898499151604 2.2412223 0.00000005628 (-0.6213198177126) 0.7835570713763 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p776_7 : ‖exp (-((((((12776:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9632910442758:ℝ):ℂ) + ((0.2684592408878:ℝ):ℂ) * I)‖ ≤ 0.00000014176 := by
  have hl := lg_7
  refine (ecis_approx ((((12776:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.860948057688551472 24.860948070464577024 0.2717932 0.00000004175 0.9632910442758 0.2684592408878 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p776_8 : ‖exp (-((((((12776:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1361680775228:ℝ):ℂ) + (((-0.9906857497025):ℝ):ℂ) * I)‖ ≤ 0.000000117 := by
  have hl := lg_8
  refine (ecis_approx ((((12776:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.5669451265384 26.5669451457024 (-1.4342039) 0.00000001699 0.1361680775228 (-0.9906857497025) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p776_9 : ‖exp (-((((((12776:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9795482036035):ℝ):ℂ) + (((-0.2012096332078):ℝ):ℂ) * I)‖ ≤ 0.00000013533 := by
  have hl := lg_9
  refine (ecis_approx ((((12776:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.071741193405406528 28.07174120618143208 (-2.939) 0.00000003532 (-0.9795482036035) (-0.2012096332078) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p776_10 : ‖exp (-((((((12776:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.414417875279):ℝ):ℂ) + ((0.9100867127069:ℝ):ℂ) * I)‖ ≤ 0.00000012141 := by
  have hl := lg_10
  refine (ecis_approx ((((12776:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.417827138128734184 29.41782715729274696 1.9980994 0.0000000214 (-0.414417875279) 0.9100867127069 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p091_2 : ‖exp (-((((((13091:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9391021305506):ℝ):ℂ) + (((-0.3436381646701):ℝ):ℂ) * I)‖ ≤ 0.00000013669 := by
  have hl := lg_2
  refine (ecis_approx ((((13091:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.0739897373073 9.0739897438528 (-2.7908044) 0.00000003668 (-0.9391021305506) (-0.3436381646701) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p091_3 : ‖exp (-((((((13091:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2423298621361):ℝ):ℂ) + (((-0.9701939176865):ℝ):ℂ) * I)‖ ≤ 0.00000014682 := by
  have hl := lg_3
  refine (ecis_approx ((((13091:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.381933467551274924 14.381933474096788015 (-1.8155629) 0.00000004681 (-0.2423298621361) (-0.9701939176865) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p091_4 : ‖exp (-((((((13091:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7638256926126:ℝ):ℂ) + ((0.6454225835101:ℝ):ℂ) * I)‖ ≤ 0.00000014694 := by
  have hl := lg_4
  refine (ecis_approx ((((13091:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.1479794746146 18.1479794877056 0.7015764 0.00000004693 0.7638256926126 0.6454225835101 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p091_5 : ‖exp (-((((((13091:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6042302499167):ℝ):ℂ) + (((-0.7968097671799):ℝ):ℂ) * I)‖ ≤ 0.00000011668 := by
  have hl := lg_5
  refine (ecis_approx ((((13091:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.069151704868910019 21.06915171795992311 (-2.2195958) 0.00000001667 (-0.6042302499167) (-0.7968097671799) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p091_6 : ‖exp (-((((((13091:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1058231603565):ℝ):ℂ) + ((0.9943849650571:ℝ):ℂ) * I)‖ ≤ 0.00000012387 := by
  have hl := lg_6
  refine (ecis_approx ((((13091:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.455923204858574924 23.455923217949588015 1.676818 0.00000002386 (-0.1058231603565) 0.9943849650571 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p091_7 : ‖exp (-((((((13091:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.942364342335:ℝ):ℂ) + (((-0.3345884730465):ℝ):ℂ) * I)‖ ≤ 0.00000013886 := by
  have hl := lg_7
  refine (ecis_approx ((((13091:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.473909754477209402 25.473909767568235584 (-0.3411685) 0.00000003885 0.942364342335 (-0.3345884730465) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p091_8 : ‖exp (-((((((13091:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4955185032537):ℝ):ℂ) + (((-0.8685973825237):ℝ):ℂ) * I)‖ ≤ 0.00000011681 := by
  have hl := lg_8
  refine (ecis_approx ((((13091:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.2219692119219 27.2219692315584 (-2.089228) 0.0000000168 (-0.4955185032537) (-0.8685973825237) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p091_9 : ‖exp (-((((((13091:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8825525194525):ℝ):ℂ) + ((0.4702138346641:ℝ):ℂ) * I)‖ ≤ 0.00000011231 := by
  have hl := lg_9
  refine (ecis_approx ((((13091:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.763866935102549848 28.76386694819357603 2.6520596 0.0000000123 (-0.8825525194525) 0.4702138346641 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p091_10 : ‖exp (-((((((13091:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.293619675879:ℝ):ℂ) + ((0.9559223221249:ℝ):ℂ) * I)‖ ≤ 0.00000012593 := by
  have hl := lg_10
  refine (ecis_approx ((((13091:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.143141442176210019 30.14314146181272311 1.2727851 0.00000002592 0.293619675879 0.9559223221249 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_2 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9912417297937):ℝ):ℂ) + (((-0.1320599587106):ℝ):ℂ) * I)‖ ≤ 0.00000010809 := by
  have hl := lg_2
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.2923310991018 9.2923311058048 (-3.0091458) 0.00000000808 (-0.9912417297937) (-0.1320599587106) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_3 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5570499914184):ℝ):ℂ) + (((-0.8304789624378):ℝ):ℂ) * I)‖ ≤ 0.00000013076 := by
  have hl := lg_3
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.727996338399846584 14.72799634510285999 (-2.1616257) 0.00000003075 (-0.5570499914184) (-0.8304789624378) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_4 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9651203363839:ℝ):ℂ) + ((0.2618066773371:ℝ):ℂ) * I)‖ ≤ 0.00000012335 := by
  have hl := lg_4
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.5846621982036 18.5846622116096 0.2648937 0.00000002334 0.9651203363839 0.2618066773371 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_5 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9151066623437):ℝ):ℂ) + (((-0.4032118505184):ℝ):ℂ) * I)‖ ≤ 0.000000139 := by
  have hl := lg_5
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.576124647121885854 21.57612466052789926 (-2.7265687) 0.00000003899 (-0.9151066623437) (-0.4032118505184) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_6 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4424981859596:ℝ):ℂ) + ((0.8967693992451:ℝ):ℂ) * I)‖ ≤ 0.0000001222 := by
  have hl := lg_6
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.020327437501646584 24.02032745090765999 1.1124138 0.00000002219 0.4424981859596 0.8967693992451 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_7 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.578318568969:ℝ):ℂ) + (((-0.8158110276196):ℝ):ℂ) * I)‖ ≤ 0.00000013597 := by
  have hl := lg_7
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.086871451265867332 26.086871464671894144 (-0.9541302) 0.00000003596 0.578318568969 (-0.8158110276196) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_8 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9220933727765):ℝ):ℂ) + (((-0.3869674556542):ℝ):ℂ) * I)‖ ≤ 0.00000013143 := by
  have hl := lg_8
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.8769932973054 27.8769933174144 (-2.7442521) 0.00000003142 (-0.9220933727765) (-0.3869674556542) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_9 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3793906074778):ℝ):ℂ) + ((0.925236600527:ℝ):ℂ) * I)‖ ≤ 0.00000015432 := by
  have hl := lg_9
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.455992676799693168 29.45599269020571998 1.9599339 0.00000005431 (-0.3793906074778) 0.925236600527 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_10 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8538437744541:ℝ):ℂ) + ((0.5205293544326:ℝ):ℂ) * I)‖ ≤ 0.00000013045 := by
  have hl := lg_10
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.868455746223685854 30.86845576633269926 0.5474708 0.00000003044 0.8538437744541 0.5205293544326 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_11 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7450026587109:ℝ):ℂ) + (((-0.6670614953014):ℝ):ℂ) * I)‖ ≤ 0.00000011923 := by
  have hl := lg_11
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.146184016680453398 32.14618403678948021 (-0.7302575) 0.00000001922 0.7450026587109 (-0.6670614953014) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_12 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3201953373453):ℝ):ℂ) + (((-0.9473515429556):ℝ):ℂ) * I)‖ ≤ 0.00000012083 := by
  have hl := lg_12
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.312658536603446584 33.31265855671245999 (-1.896732) 0.00000002082 (-0.3201953373453) (-0.9473515429556) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_13 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9852772481068):ℝ):ℂ) + (((-0.1709641599895):ℝ):ℂ) * I)‖ ≤ 0.0000001599 := by
  have hl := lg_13
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.3857110756748702 34.385711095783897012 (-2.9697845) 0.00000005989 (-0.9852772481068) (-0.1709641599895) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_14 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6809894643114):ℝ):ℂ) + ((0.7322932127749:ℝ):ℂ) * I)‖ ≤ 0.00000012741 := by
  have hl := lg_14
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.379202550367667332 35.379202570476694144 2.3199093 0.0000000274 (-0.6809894643114) 0.7322932127749 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p406_15 : ‖exp (-((((((13406:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1749013046335:ℝ):ℂ) + ((0.9845859706686:ℝ):ℂ) * I)‖ ≤ 0.00000015757 := by
  have hl := lg_15
  refine (ecis_approx ((((13406:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.304120985521732438 36.30412100563075925 1.3949908 0.00000005756 0.1749013046335 0.9845859706686 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_2 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9995153181699):ℝ):ℂ) + ((0.0311308228253:ℝ):ℂ) * I)‖ ≤ 0.00000012613 := by
  have hl := lg_2
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.4559138336526 9.4559138404736 3.1104568 0.00000002612 (-0.9995153181699) 0.0311308228253 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_3 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7513476358343):ℝ):ℂ) + (((-0.6599066070983):ℝ):ℂ) * I)‖ ≤ 0.00000013094 := by
  have hl := lg_3
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.987268838464173288 14.98726884528518693 (-2.4208982) 0.00000003093 (-0.7513476358343) (-0.6599066070983) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_4 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9980617379295:ℝ):ℂ) + (((-0.0622315617761):ℝ):ℂ) * I)‖ ≤ 0.00000015425 := by
  have hl := lg_4
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.9118276673052 18.9118276809472 (-0.0622718) 0.00000005424 0.9980617379295 (-0.0622315617761) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_5 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993806649545):ℝ):ℂ) + (((-0.035189286866):ℝ):ℂ) * I)‖ ≤ 0.00000012722 := by
  have hl := lg_5
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.955951994333639178 21.95595200797565282 (-3.1063961) 0.00000002721 (-0.9993806649545) (-0.035189286866) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_6 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7715269709874:ℝ):ℂ) + ((0.6361966150798:ℝ):ℂ) * I)‖ ≤ 0.00000015662 := by
  have hl := lg_6
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.443182672116773288 24.44318268575878693 0.6895585 0.00000005661 0.7715269709874 0.6361966150798 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_7 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1567818195357:ℝ):ℂ) + (((-0.9876332624325):ℝ):ℂ) * I)‖ ≤ 0.00000013126 := by
  have hl := lg_7
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.546106246320226924 26.546106259962254208 (-1.413365) 0.00000003125 0.1567818195357 (-0.9876332624325) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_8 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9956406758732):ℝ):ℂ) + ((0.0932718824679:ℝ):ℂ) * I)‖ ≤ 0.00000013496 := by
  have hl := lg_8
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.3677415009578 28.3677415214208 3.048185 0.00000003495 (-0.9956406758732) 0.0932718824679 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_9 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1290465468846:ℝ):ℂ) + ((0.9916385373396:ℝ):ℂ) * I)‖ ≤ 0.00000015469 := by
  have hl := lg_9
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.974537676928346576 29.97453769057037386 1.4413889 0.00000005468 0.1290465468846 0.9916385373396 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_10 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999917553691:ℝ):ℂ) + ((0.0040606888403:ℝ):ℂ) * I)‖ ≤ 0.00000011257 := by
  have hl := lg_10
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.411865827986239178 31.41186584844925282 0.0040607 0.00000001256 0.9999917553691 0.0040606888403 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_11 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2711961407312:ℝ):ℂ) + (((-0.9625241052839):ℝ):ℂ) * I)‖ ≤ 0.00000013504 := by
  have hl := lg_11
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.712087300876827186 32.71208732133985447 (-1.2961608) 0.00000003503 0.2711961407312 (-0.9625241052839) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_12 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.790958345994):ℝ):ℂ) + (((-0.6118699983301):ℝ):ℂ) * I)‖ ≤ 0.00000013014 := by
  have hl := lg_12
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.899096505769373288 33.89909652623238693 (-2.48317) 0.00000003013 (-0.790958345994) (-0.6118699983301) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_13 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9074927557193):ℝ):ℂ) + ((0.4200677304811:ℝ):ℂ) * I)‖ ≤ 0.00000011924 := by
  have hl := lg_13
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.9910391238517514 34.991039144314778684 2.7080727 0.00000001923 (-0.9074927557193) 0.4200677304811 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_14 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1259599939001):ℝ):ℂ) + ((0.9920353219196:ℝ):ℂ) * I)‖ ≤ 0.00000015737 := by
  have hl := lg_14
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.002020079972826924 36.002020100435854208 1.6970918 0.00000005736 (-0.1259599939001) 0.9920353219196 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p642_15 : ‖exp (-((((((13642:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7276606619793:ℝ):ℂ) + ((0.6859372864978:ℝ):ℂ) * I)‖ ≤ 0.00000011029 := by
  have hl := lg_15
  refine (ecis_approx ((((13642:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.943220832797812466 36.94322085326083975 0.755891 0.00000001028 0.7276606619793 0.6859372864978 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_2 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9881925586923):ℝ):ℂ) + ((0.1532170570043:ℝ):ℂ) * I)‖ ≤ 0.00000012981 := by
  have hl := lg_2
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.5786008845657 9.5786008914752 2.9877697 0.0000000298 (-0.9881925586923) 0.1532170570043 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_3 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8647017454563):ℝ):ℂ) + (((-0.5022856670471):ℝ):ℂ) * I)‖ ≤ 0.00000010608 := by
  have hl := lg_3
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.181723213512418316 15.181723220421932135 (-2.6153526) 0.00000000607 (-0.8647017454563) (-0.5022856670471) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_4 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9530490689449:ℝ):ℂ) + (((-0.3028159047727):ℝ):ℂ) * I)‖ ≤ 0.00000015242 := by
  have hl := lg_4
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.1572017691314 19.1572017829504 (-0.3076459) 0.00000005241 0.9530490689449 (-0.3028159047727) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_5 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9689930352778):ℝ):ℂ) + ((0.2470880355579:ℝ):ℂ) * I)‖ ≤ 0.00000012399 := by
  have hl := lg_5
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.240822504742454171 22.24082251856146799 2.8919187 0.00000002398 (-0.9689930352778) 0.2470880355579 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_6 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9314505622961:ℝ):ℂ) + ((0.3638679018522:ℝ):ℂ) * I)‖ ≤ 0.00000013066 := by
  have hl := lg_6
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.760324098078118316 24.760324111897132135 0.3724171 0.00000003065 0.9314505622961 0.3638679018522 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_7 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1859069011503):ℝ):ℂ) + (((-0.9825673636468):ℝ):ℂ) * I)‖ ≤ 0.00000012773 := by
  have hl := lg_7
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.890532342610996618 26.890532356430024256 (-1.7577911) 0.00000002772 (-0.1859069011503) (-0.9825673636468) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_8 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8953994808533):ℝ):ℂ) + ((0.4452637079039:ℝ):ℂ) * I)‖ ≤ 0.00000013854 := by
  have hl := lg_8
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.7358026536971 28.7358026744256 2.6801239 0.00000003853 (-0.8953994808533) 0.4452637079039 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_9 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4954182235022:ℝ):ℂ) + ((0.8686545825712:ℝ):ℂ) * I)‖ ≤ 0.00000010889 := by
  have hl := lg_9
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.363446427024836632 30.36344644084386427 1.0524801 0.00000000888 0.4954182235022 0.8686545825712 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_10 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9196936082732:ℝ):ℂ) + (((-0.3926368129727):ℝ):ℂ) * I)‖ ≤ 0.0000001466 := by
  have hl := lg_10
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.819423389308154171 31.81942341003666799 (-0.4034969) 0.00000004659 0.9196936082732 (-0.3926368129727) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_11 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1492323394832):ℝ):ℂ) + (((-0.9888021585999):ℝ):ℂ) * I)‖ ≤ 0.00000014887 := by
  have hl := lg_11
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.136514764024107527 33.136514784752635165 (-1.7205882) 0.00000004886 (-0.1492323394832) (-0.9888021585999) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_12 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9762032820568):ℝ):ℂ) + (((-0.2168574458014):ℝ):ℂ) * I)‖ ≤ 0.00000015327 := by
  have hl := lg_12
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.338924982643818316 34.338925003372332135 (-2.9229985) 0.00000005326 (-0.9762032820568) (-0.2168574458014) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_13 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6313403649839):ℝ):ℂ) + ((0.775505862987:ℝ):ℂ) * I)‖ ≤ 0.00000013765 := by
  have hl := lg_13
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.4450351599844123 35.445035180712939938 2.2540767 0.00000003764 (-0.6313403649839) 0.775505862987 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_14 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3342578963083:ℝ):ℂ) + ((0.9424816490285:ℝ):ℂ) * I)‖ ≤ 0.00000011592 := by
  have hl := lg_14
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.469133227176696618 36.469133247905224256 1.2299786 0.00000001591 0.3342578963083 0.9424816490285 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_15 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.961998747889:ℝ):ℂ) + ((0.2730538574346:ℝ):ℂ) * I)‖ ≤ 0.00000012484 := by
  have hl := lg_15
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.422545718254872487 37.422545738983400125 0.2765661 0.00000002483 0.961998747889 0.2730538574346 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_16 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8166051133531:ℝ):ℂ) + (((-0.5771967505501):ℝ):ℂ) * I)‖ ≤ 0.00000012284 := by
  have hl := lg_16
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.3144035382628 38.3144035659008 (-0.6152917) 0.00000002283 0.8166051133531 (-0.5771967505501) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_17 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1174611317232:ℝ):ℂ) + (((-0.9930774806299):ℝ):ℂ) * I)‖ ≤ 0.00000015595 := by
  have hl := lg_17
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.152175187144101446 39.152175214782115265 (-1.4530634) 0.00000005594 0.1174611317232 (-0.9930774806299) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_18 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6226612952271):ℝ):ℂ) + (((-0.7824914768942):ℝ):ℂ) * I)‖ ≤ 0.0000001315 := by
  have hl := lg_18
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.942047311590536632 39.94204733231906427 (-2.2429355) 0.00000003149 (-0.6226612952271) (-0.7824914768942) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_19 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9885454681682):ℝ):ℂ) + (((-0.1509233480035):ℝ):ℂ) * I)‖ ≤ 0.00000011999 := by
  have hl := lg_19
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.689202242324466857 40.689202263053008314 (-2.9900904) 0.00000001998 (-0.9885454681682) (-0.1509233480035) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p819_20 : ‖exp (-((((((13819:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8486757759708):ℝ):ℂ) + ((0.5289134401841:ℝ):ℂ) * I)‖ ≤ 0.00000015127 := by
  have hl := lg_20
  refine (ecis_approx ((((13819:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.398024273873854171 41.39802430151186799 2.5842729 0.00000005126 (-0.8486757759708) 0.5289134401841 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_2 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9620140772766):ℝ):ℂ) + ((0.2729998441054:ℝ):ℂ) * I)‖ ≤ 0.00000012813 := by
  have hl := lg_2
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.7012879354788 9.7012879424768 2.8650827 0.00000002812 (-0.9620140772766) 0.2729998441054 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_3 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9454622069166):ℝ):ℂ) + (((-0.325731814689):ℝ):ℂ) * I)‖ ≤ 0.00000012581 := by
  have hl := lg_3
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.376177588560663344 15.37617759555867734 (-2.809807) 0.0000000258 (-0.9454622069166) (-0.325731814689) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_4 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8509421213482:ℝ):ℂ) + (((-0.5252594655172):ℝ):ℂ) * I)‖ ≤ 0.0000001506 := by
  have hl := lg_4
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.4025758709576 19.4025758849536 (-0.55302) 0.00000005059 0.8509421213482 (-0.5252594655172) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_5 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8605007962388):ℝ):ℂ) + ((0.5094490942102:ℝ):ℂ) * I)‖ ≤ 0.00000011358 := by
  have hl := lg_5
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.525693015151269164 22.52569302914728316 2.6070482 0.00000001357 (-0.8605007962388) 0.5094490942102 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_6 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9984726874338:ℝ):ℂ) + ((0.0552475560432:ℝ):ℂ) * I)‖ ≤ 0.00000010933 := by
  have hl := lg_6
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.077465524039463344 25.07746553803547734 0.0552757 0.00000000932 0.9984726874338 0.0552475560432 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_7 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5067587699342):ℝ):ℂ) + (((-0.8620879010218):ℝ):ℂ) * I)‖ ≤ 0.00000012419 := by
  have hl := lg_7
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.234958438901766312 27.234958452897794304 (-2.1022172) 0.00000002418 (-0.5067587699342) (-0.8620879010218) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_8 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6752225474933):ℝ):ℂ) + ((0.7376140666613:ℝ):ℂ) * I)‖ ≤ 0.00000012948 := by
  have hl := lg_8
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.1038638064364 29.1038638274304 2.3120627 0.00000002947 (-0.6752225474933) 0.7376140666613 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_9 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7877975124973:ℝ):ℂ) + ((0.615934314114:ℝ):ℂ) * I)‖ ≤ 0.00000015523 := by
  have hl := lg_9
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.752355177121326688 30.75235519111735468 0.6635714 0.00000005522 0.7877975124973 0.615934314114 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_10 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6887343614185:ℝ):ℂ) + (((-0.7250137787667):ℝ):ℂ) * I)‖ ≤ 0.00000013574 := by
  have hl := lg_10
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.226980950630069164 32.22698097162408316 (-0.8110544) 0.00000003573 0.6887343614185 (-0.7250137787667) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_11 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5431795290519):ℝ):ℂ) + (((-0.8396165786897):ℝ):ℂ) * I)‖ ≤ 0.00000011228 := by
  have hl := lg_11
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.560942227171387868 33.56094224816541586 (-2.1450157) 0.00000001227 (-0.5431795290519) (-0.8396165786897) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_12 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9756273552515):ℝ):ℂ) + ((0.2194339613324:ℝ):ℂ) * I)‖ ≤ 0.00000013745 := by
  have hl := lg_12
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.778753459518263344 34.77875348051227734 2.9203584 0.00000003744 (-0.9756273552515) 0.2194339613324 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_13 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2272805860742):ℝ):ℂ) + ((0.9738293152256:ℝ):ℂ) * I)‖ ≤ 0.00000014698 := by
  have hl := lg_13
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.8990311961170732 35.899031217111101192 1.8000806 0.00000004697 (-0.2272805860742) 0.9738293152256 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_14 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7228589331966:ℝ):ℂ) + ((0.6909956314608:ℝ):ℂ) * I)‖ ≤ 0.00000015231 := by
  have hl := lg_14
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.936246374380566312 36.936246395374594304 0.7628655 0.0000000523 0.7228589331966 0.6909956314608 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_15 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9795147599568:ℝ):ℂ) + (((-0.2013723790068):ℝ):ℂ) * I)‖ ≤ 0.00000013938 := by
  have hl := lg_15
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.901870603711932508 37.9018706247059605 (-0.2027588) 0.00000003937 0.9795147599568 (-0.2013723790068) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_16 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4482050771623:ℝ):ℂ) + (((-0.8939307628703):ℝ):ℂ) * I)‖ ≤ 0.00000012684 := by
  have hl := lg_16
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.8051517419152 38.8051517699072 (-1.1060399) 0.00000002683 0.4482050771623 (-0.8939307628703) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_17 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3743964262315):ℝ):ℂ) + (((-0.9272687399143):ℝ):ℂ) * I)‖ ≤ 0.00000013379 := by
  have hl := lg_17
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.653653948858010264 39.65365397685002426 (-1.9545421) 0.00000003378 (-0.3743964262315) (-0.9272687399143) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_18 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.926022303932):ℝ):ℂ) + (((-0.3774687966811):ℝ):ℂ) * I)‖ ≤ 0.00000013049 := by
  have hl := lg_18
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.453643112600126688 40.45364313359415468 (-2.7545313) 0.00000003048 (-0.926022303932) (-0.3774687966811) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_19 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9324489931255):ℝ):ℂ) + ((0.3613016399841:ℝ):ℂ) * I)‖ ≤ 0.00000011225 := by
  have hl := lg_19
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.210367941498895588 41.210367962492937576 2.7719292 0.00000001224 (-0.9324489931255) 0.3613016399841 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p996_20 : ‖exp (-((((((13996:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4646435025842):ℝ):ℂ) + ((0.8854978348372:ℝ):ℂ) * I)‖ ≤ 0.00000016386 := by
  have hl := lg_20
  refine (ecis_approx ((((13996:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.928268886108869164 41.92826891410088316 2.0540283 0.00000006385 (-0.4646435025842) 0.8854978348372 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_2 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9330467493357):ℝ):ℂ) + ((0.3597551436587:ℝ):ℂ) * I)‖ ≤ 0.0000001511 := by
  have hl := lg_2
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.7927833632784 9.7927833703424 2.7735872 0.00000005109 (-0.9330467493357) 0.3597551436587 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_3 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9826093384453):ℝ):ℂ) + (((-0.1856849149989):ℝ):ℂ) * I)‖ ≤ 0.00000010374 := by
  have hl := lg_3
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.521194410630540992 15.52119441769455512 (-2.9548238) 0.00000000373 (-0.9826093384453) (-0.1856849149989) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_4 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7411525450505:ℝ):ℂ) + (((-0.6713366554608):ℝ):ℂ) * I)‖ ≤ 0.00000011916 := by
  have hl := lg_4
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.5855667265568 19.5855667406848 (-0.7360108) 0.00000001915 0.7411525450505 (-0.6713366554608) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_5 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7337371115566):ℝ):ℂ) + ((0.6794334780496:ℝ):ℂ) * I)‖ ≤ 0.00000010921 := by
  have hl := lg_5
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.738138819523944752 22.73813883365195888 2.3946024 0.0000000092 (-0.7337371115566) 0.6794334780496 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_6 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9836215526373:ℝ):ℂ) + (((-0.1802460573421):ℝ):ℂ) * I)‖ ≤ 0.00000015482 := by
  have hl := lg_6
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.313977773908940992 25.31397778803695512 (-0.1812366) 0.00000005481 0.9836215526373 (-0.1802460573421) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_7 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7091423649938):ℝ):ℂ) + (((-0.7050653204815):ℝ):ℂ) * I)‖ ≤ 0.00000015022 := by
  have hl := lg_7
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.491818578508442016 27.491818592636470272 (-2.3590774) 0.00000005021 (-0.7091423649938) (-0.7050653204815) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_8 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4500131579748):ℝ):ℂ) + ((0.8930219245041:ℝ):ℂ) * I)‖ ≤ 0.00000014608 := by
  have hl := lg_8
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.3783500898352 29.3783501110272 2.0375764 0.00000004607 (-0.4500131579748) 0.8930219245041 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_9 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9310422271788:ℝ):ℂ) + ((0.3649114566714:ℝ):ℂ) * I)‖ ≤ 0.00000011465 := by
  have hl := lg_9
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.042388821261081984 31.04238883538911024 0.3735377 0.00000001464 0.9310422271788 0.3649114566714 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_10 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4401813447286:ℝ):ℂ) + (((-0.8979088950183):ℝ):ℂ) * I)‖ ≤ 0.00000015311 := by
  have hl := lg_10
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.530922182802344752 32.53092220399435888 (-1.1149957) 0.0000000531 0.4401813447286 (-0.8979088950183) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_11 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7775382889023):ℝ):ℂ) + (((-0.6288355979502):ℝ):ℂ) * I)‖ ≤ 0.00000013284 := by
  have hl := lg_11
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.877464403077834224 33.87746442426986248 (-2.4615379) 0.00000003283 (-0.7775382889023) (-0.6288355979502) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_12 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8529204982354):ℝ):ℂ) + ((0.5220408256202:ℝ):ℂ) * I)‖ ≤ 0.00000011532 := by
  have hl := lg_12
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.106761137187340992 35.10676115837935512 2.5923507 0.00000001531 (-0.8529204982354) 0.5220408256202 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_13 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1090715969985:ℝ):ℂ) + ((0.9940338961666:ℝ):ℂ) * I)‖ ≤ 0.00000013189 := by
  have hl := lg_13
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.2376045111990576 36.237604532391085856 1.4615073 0.00000003188 0.1090715969985 0.9940338961666 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_14 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.915313813967:ℝ):ℂ) + ((0.4027413834722:ℝ):ℂ) * I)‖ ≤ 0.00000011992 := by
  have hl := lg_14
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.284601941786842016 37.284601962978870272 0.4145099 0.00000001991 0.915313813967 0.4027413834722 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p128_15 : ‖exp (-((((((14128:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8471374856248:ℝ):ℂ) + (((-0.5313737671821):ℝ):ℂ) * I)‖ ≤ 0.00000011294 := by
  have hl := lg_15
  refine (ecis_approx ((((14128:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.259333230154485744 38.259333251346514 (-0.5602214) 0.00000001293 0.8471374856248 (-0.5313737671821) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_2 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8962739809632):ℝ):ℂ) + ((0.4435007902317:ℝ):ℂ) * I)‖ ≤ 0.0000001233 := by
  have hl := lg_2
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.884278791078 9.884278798208 2.6820918 0.00000002329 (-0.8962739809632) 0.4435007902317 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_3 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9991285093382):ℝ):ℂ) + (((-0.0417399237786):ℝ):ℂ) * I)‖ ≤ 0.00000012549 := by
  have hl := lg_3
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.66621123270041864 15.6662112398304329 (-3.0998406) 0.00000002548 (-0.9991285093382) (-0.0417399237786) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_4 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6066141037278:ℝ):ℂ) + (((-0.794996433425):ℝ):ℂ) * I)‖ ≤ 0.0000001394 := by
  have hl := lg_4
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.768557582156 19.768557596416 (-0.9190017) 0.00000003939 0.6066141037278 (-0.794996433425) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_5 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5739818749917):ℝ):ℂ) + ((0.818868003509:ℝ):ℂ) * I)‖ ≤ 0.00000010945 := by
  have hl := lg_5
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.95058462389662034 22.9505846381566346 2.1821566 0.00000000944 (-0.5739818749917) 0.818868003509 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_6 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9140045761475:ℝ):ℂ) + (((-0.4057038757289):ℝ):ℂ) * I)‖ ≤ 0.00000010934 := by
  have hl := lg_6
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.55049002377841864 25.5504900380384329 (-0.4177488) 0.00000000933 0.9140045761475 (-0.4057038757289) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_7 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8649953844155):ℝ):ℂ) + (((-0.5017798171069):ℝ):ℂ) * I)‖ ≤ 0.00000011062 := by
  have hl := lg_7
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.74867871811511772 27.74867873237514624 (-2.6159375) 0.00000001061 (-0.8649953844155) (-0.5017798171069) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_8 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1911109893296):ℝ):ℂ) + ((0.9815684335576:ℝ):ℂ) * I)‖ ≤ 0.00000015874 := by
  have hl := lg_8
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.652836373234 29.652836394624 1.7630902 0.00000005873 (-0.1911109893296) 0.9815684335576 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_9 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9965155580799:ℝ):ℂ) + ((0.0834070890557:ℝ):ℂ) * I)‖ ≤ 0.00000014378 := by
  have hl := lg_9
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.33242246540083728 31.3324224796608658 0.0835041 0.00000004377 0.9965155580799 0.0834070890557 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_10 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1512764205118:ℝ):ℂ) + (((-0.9884914995067):ℝ):ℂ) * I)‖ ≤ 0.00000012094 := by
  have hl := lg_10
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.83486341497462034 32.8348634363646346 (-1.4189369) 0.00000002093 0.1512764205118 (-0.9884914995067) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_11 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9346465591108):ℝ):ℂ) + (((-0.3555781339932):ℝ):ℂ) * I)‖ ≤ 0.00000015693 := by
  have hl := lg_11
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.19398657898428058 34.1939866003743091 (-2.7780601) 0.00000005692 (-0.9346465591108) (-0.3555781339932) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_12 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6392685306001):ℝ):ℂ) + ((0.7689835796483:ℝ):ℂ) * I)‖ ≤ 0.00000012824 := by
  have hl := lg_12
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.43476881485641864 35.4347688362464329 2.264343 0.00000002823 (-0.6392685306001) 0.7689835796483 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_13 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4330396801149:ℝ):ℂ) + ((0.9013748584501:ℝ):ℂ) * I)‖ ≤ 0.00000011681 := by
  have hl := lg_13
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.576177826281042 36.57617784767107052 1.122934 0.0000000168 0.4330396801149 0.9013748584501 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_14 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9978126022128:ℝ):ℂ) + ((0.0661060577059:ℝ):ℂ) * I)‖ ≤ 0.0000001339 := by
  have hl := lg_14
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.63295750919311772 37.63295753058314624 0.0661543 0.00000003389 0.9978126022128 0.0661060577059 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p26_15 : ‖exp (-((((((14260:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6076611435829:ℝ):ℂ) + (((-0.7941964080626):ℝ):ℂ) * I)‖ ≤ 0.00000013492 := by
  have hl := lg_15
  refine (ecis_approx ((((14260:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.61679585659703898 38.6167958779870675 (-0.917684) 0.00000003491 0.6076611435829 (-0.7941964080626) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_2 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8520033700246):ℝ):ℂ) + ((0.5235362999751:ℝ):ℂ) * I)‖ ≤ 0.00000011173 := by
  have hl := lg_2
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.9757742188776 9.9757742260736 2.5905964 0.00000001172 (-0.8520033700246) 0.5235362999751 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_3 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9946729314594):ℝ):ℂ) + ((0.1030813220325:ℝ):ℂ) * I)‖ ≤ 0.00000014044 := by
  have hl := lg_3
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.811228054770296288 15.81122806196631068 3.0383279 0.00000004043 (-0.9946729314594) 0.1030813220325 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_4 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4518194915349:ℝ):ℂ) + (((-0.8921093806643):ℝ):ℂ) * I)‖ ≤ 0.00000013062 := by
  have hl := lg_4
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.9515484377552 19.9515484521472 (-1.1019925) 0.00000003061 0.4518194915349 (-0.8921093806643) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_5 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3884182766773):ℝ):ℂ) + ((0.9214831752886:ℝ):ℂ) * I)‖ ≤ 0.00000011396 := by
  have hl := lg_5
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.163030428269295928 23.16303044266131032 1.9697108 0.00000001395 (-0.3884182766773) 0.9214831752886 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_6 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7934978193341:ℝ):ℂ) + (((-0.6085730939764):ℝ):ℂ) * I)‖ ≤ 0.00000015509 := by
  have hl := lg_6
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.787002273647896288 25.78700228803991068 (-0.6542611) 0.00000005508 0.7934978193341 (-0.6085730939764) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_7 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9640915936342):ℝ):ℂ) + (((-0.2655699509288):ℝ):ℂ) * I)‖ ≤ 0.00000014341 := by
  have hl := lg_7
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.005538857721793424 28.005538872113822208 (-2.8727976) 0.0000000434 (-0.9640915936342) (-0.2655699509288) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_8 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0820999149241:ℝ):ℂ) + ((0.9966241036466:ℝ):ℂ) * I)‖ ≤ 0.00000014234 := by
  have hl := lg_8
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.9273226566328 29.9273226782208 1.4886039 0.00000004233 0.0820999149241 0.9966241036466 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_9 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9787484629705:ℝ):ℂ) + (((-0.2050644928622):ℝ):ℂ) * I)‖ ≤ 0.00000012637 := by
  have hl := lg_9
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.622456109540592576 31.62245612393262136 (-0.2065296) 0.00000002636 0.9787484629705 (-0.2050644928622) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_10 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1514962043071):ℝ):ℂ) + (((-0.9884578393032):ℝ):ℂ) * I)‖ ≤ 0.00000013285 := by
  have hl := lg_10
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.138804647146895928 33.13880466873491032 (-1.7228781) 0.00000003284 (-0.1514962043071) (-0.9884578393032) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_11 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9988952118351):ℝ):ℂ) + (((-0.0469931398567):ℝ):ℂ) * I)‖ ≤ 0.0000001406 := by
  have hl := lg_11
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.510508754890726936 34.51050877647875572 (-3.0945822) 0.00000004059 (-0.9988952118351) (-0.0469931398567) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_12 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3574527102847):ℝ):ℂ) + ((0.9339312393895:ℝ):ℂ) * I)‖ ≤ 0.00000015057 := by
  have hl := lg_12
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.762776492525496288 35.76277651411351068 1.9363353 0.00000005056 (-0.3574527102847) 0.9339312393895 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_13 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7078399979183:ℝ):ℂ) + ((0.7063728033744:ℝ):ℂ) * I)‖ ≤ 0.00000011989 := by
  have hl := lg_13
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.9147511413630264 36.914751162951055184 0.7843607 0.00000001988 0.7078399979183 0.7063728033744 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_14 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9604447964573:ℝ):ℂ) + (((-0.2784704525764):ℝ):ℂ) * I)‖ ≤ 0.00000015512 := by
  have hl := lg_14
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.981313076599393424 37.981313098187422208 (-0.2822012) 0.00000005511 0.9604447964573 (-0.2784704525764) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p392_15 : ‖exp (-((((((14392:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2913613530407:ℝ):ℂ) + (((-0.9566130680449):ℝ):ℂ) * I)‖ ≤ 0.00000016005 := by
  have hl := lg_15
  refine (ecis_approx ((((14392:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.974258483039592216 38.974258504627621 (-1.2751467) 0.00000006004 0.2913613530407 (-0.9566130680449) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_2 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8006052654092):ℝ):ℂ) + ((0.5991921302467:ℝ):ℂ) * I)‖ ≤ 0.0000001396 := by
  have hl := lg_2
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.0672696466772 10.0672696539392 2.499101 0.00000003959 (-0.8006052654092) 0.5991921302467 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_3 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.969336116642):ℝ):ℂ) + ((0.2457386675:ℝ):ℂ) * I)‖ ≤ 0.00000014471 := by
  have hl := lg_3
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.956244876840173936 15.95624488410218846 2.893311 0.0000000447 (-0.969336116642) 0.2457386675 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_4 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2819374929794:ℝ):ℂ) + (((-0.9594327751607):ℝ):ℂ) * I)‖ ≤ 0.0000001282 := by
  have hl := lg_4
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.1345392933544 20.1345393078784 (-1.2849834) 0.00000002819 0.2819374929794 (-0.9594327751607) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_5 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1853899467564):ℝ):ℂ) + ((0.9826650332849:ℝ):ℂ) * I)‖ ≤ 0.00000011846 := by
  have hl := lg_5
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.375476232641971516 23.37547624716598604 1.757265 0.00000001845 (-0.1853899467564) 0.9826650332849 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_6 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6288109288593:ℝ):ℂ) + (((-0.7775582394568):ℝ):ℂ) * I)‖ ≤ 0.00000010934 := by
  have hl := lg_6
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.023514523517373936 26.02351453804138846 (-0.8907733) 0.00000000933 0.6288109288593 (-0.7775582394568) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_7 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999287801545):ℝ):ℂ) + (((-0.0119345699629):ℝ):ℂ) * I)‖ ≤ 0.0000001314 := by
  have hl := lg_7
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.262398997328469128 28.262399011852498176 (-3.1296578) 0.00000003139 (-0.9999287801545) (-0.0119345699629) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_8 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3491639270052:ℝ):ℂ) + ((0.9370616586321:ℝ):ℂ) * I)‖ ≤ 0.00000012593 := by
  have hl := lg_8
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.2018089400316 30.2018089618176 1.2141176 0.00000002592 0.3491639270052 0.9370616586321 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_9 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8792250655183:ℝ):ℂ) + (((-0.4764066374058):ℝ):ℂ) * I)‖ ≤ 0.00000013232 := by
  have hl := lg_9
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.912489753680347872 31.91248976820437692 (-0.4965632) 0.00000003231 0.8792250655183 (-0.4764066374058) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_10 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4403810704468):ℝ):ℂ) + (((-0.8978109560414):ℝ):ℂ) * I)‖ ≤ 0.00000015659 := by
  have hl := lg_10
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.442745879319171516 33.44274590110518604 (-2.0268194) 0.00000005658 (-0.4403810704468) (-0.8978109560414) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_11 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9639010120598):ℝ):ℂ) + ((0.266260847109:ℝ):ℂ) * I)‖ ≤ 0.0000001123 := by
  have hl := lg_11
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.827030930797173292 34.82703095258320234 2.8720809 0.00000001229 (-0.9639010120598) 0.266260847109 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_12 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0375225626855):ℝ):ℂ) + ((0.9992957806822:ℝ):ℂ) * I)‖ ≤ 0.00000014892 := by
  have hl := lg_12
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.090784170194573936 36.09078419198058846 1.6083277 0.00000004891 (-0.0375225626855) 0.9992957806822 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_13 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9022714430875:ℝ):ℂ) + ((0.4311684624237:ℝ):ℂ) * I)‖ ≤ 0.00000013517 := by
  have hl := lg_13
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.2533244564450108 37.253324478231039848 0.4457874 0.00000003516 0.9022714430875 0.4311684624237 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_14 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.807699347273:ℝ):ℂ) + (((-0.5895945763105):ℝ):ℂ) * I)‖ ≤ 0.00000012273 := by
  have hl := lg_14
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.329668644005669128 38.329668665791698176 (-0.6305568) 0.00000002272 0.807699347273 (-0.5895945763105) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p524_15 : ‖exp (-((((((14524:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0617736177734):ℝ):ℂ) + (((-0.9980901863794):ℝ):ℂ) * I)‖ ≤ 0.00000013361 := by
  have hl := lg_15
  refine (ecis_approx ((((14524:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.331721109482145452 39.3317211312681745 (-1.6326093) 0.0000000336 (-0.0617736177734) (-0.9980901863794) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_2 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6923363360147):ℝ):ℂ) + ((0.721574942616:ℝ):ℂ) * I)‖ ≤ 0.00000013315 := by
  have hl := lg_2
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.230852381228 10.230852388608 2.3355182 0.00000003314 (-0.6923363360147) 0.721574942616 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_3 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8739359025484):ℝ):ℂ) + ((0.4860411897627:ℝ):ℂ) * I)‖ ≤ 0.00000014465 := by
  have hl := lg_3
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.21551737690450064 16.2155173842845154 2.6340385 0.00000004464 (-0.8739359025484) 0.4860411897627 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_4 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0413406885716):ℝ):ℂ) + (((-0.9991451083142):ℝ):ℂ) * I)‖ ≤ 0.00000015569 := by
  have hl := lg_4
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.461704762456 20.461704777216 (-1.6121488) 0.00000005568 (-0.0413406885716) (-0.9991451083142) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_5 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1921561074504:ℝ):ℂ) + ((0.9813643718668:ℝ):ℂ) * I)‖ ≤ 0.00000014888 := by
  have hl := lg_5
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.75530357985372484 23.7553035946137396 1.3774376 0.00000004887 0.1921561074504 0.9813643718668 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_6 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2543425407022:ℝ):ℂ) + (((-0.9671141980083):ℝ):ℂ) * I)‖ ≤ 0.00000014419 := by
  have hl := lg_6
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.44636975813250064 26.4463697728925154 (-1.3136285) 0.00000004418 0.2543425407022 (-0.9671141980083) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_7 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9016182457791):ℝ):ℂ) + ((0.4325327025323:ℝ):ℂ) * I)‖ ≤ 0.00000014353 := by
  have hl := lg_7
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.72163379238282872 28.72163380714285824 2.6942927 0.00000004352 (-0.9016182457791) 0.4325327025323 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_8 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7495797350638:ℝ):ℂ) + ((0.661914058456:ℝ):ℂ) * I)‖ ≤ 0.00000012994 := by
  have hl := lg_8
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.692557143684 30.692557165824 0.7233694 0.00000002993 0.7495797350638 0.661914058456 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_9 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5275280146644:ℝ):ℂ) + (((-0.8495376352724):ℝ):ℂ) * I)‖ ≤ 0.00000013269 := by
  have hl := lg_9
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.43103475380900128 32.4310347685690308 (-1.0151082) 0.00000003268 0.5275280146644 (-0.8495376352724) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_10 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8411645377265):ℝ):ℂ) + (((-0.5407792714248):ℝ):ℂ) * I)‖ ≤ 0.00000014734 := by
  have hl := lg_10
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.98615596108172484 33.9861559832217396 (-2.5702294) 0.00000004733 (-0.8411645377265) (-0.5407792714248) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_11 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6708699470764):ℝ):ℂ) + ((0.7415750225637:ℝ):ℂ) * I)‖ ≤ 0.0000001281 := by
  have hl := lg_11
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.39293421499354708 35.3929342371335766 2.3061776 0.00000002809 (-0.6708699470764) 0.7415750225637 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_12 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5217547892202:ℝ):ℂ) + ((0.8530955045749:ℝ):ℂ) * I)‖ ≤ 0.00000011844 := by
  have hl := lg_12
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.67722213936050064 36.6772221615005154 1.0218897 0.00000001843 0.5217547892202 0.8530955045749 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_13 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9873003540944:ℝ):ℂ) + (((-0.1588647563343):ℝ):ℂ) * I)‖ ≤ 0.00000013847 := by
  have hl := lg_13
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.858652504621892 37.85865252676192152 (-0.1595407) 0.00000003846 0.9873003540944 (-0.1588647563343) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_14 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3121184145579:ℝ):ℂ) + (((-0.9500432070668):ℝ):ℂ) * I)‖ ≤ 0.00000015269 := by
  have hl := lg_14
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.95248617361082872 38.95248619575085824 (-1.2533743) 0.00000005268 0.3121184145579 (-0.9500432070668) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p76_15 : ‖exp (-((((((14760:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6449155462272):ℝ):ℂ) + (((-0.7642538440977):ℝ):ℂ) * I)‖ ≤ 0.00000013584 := by
  have hl := lg_15
  refine (ecis_approx ((((14760:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.97082095675822548 39.970820978898255 (-2.2717091) 0.00000003583 (-0.6449155462272) (-0.7642538440977) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p996_2 : ‖exp (-((((((14996:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5655823070362):ℝ):ℂ) + ((0.8246918539418:ℝ):ℂ) * I)‖ ≤ 0.00000010893 := by
  have hl := lg_2
  refine (ecis_approx ((((14996:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.3944351157788 10.3944351232768 2.1719355 0.00000000892 (-0.5655823070362) 0.8246918539418 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p996_3 : ‖exp (-((((((14996:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7201161294369):ℝ):ℂ) + ((0.6938535581069:ℝ):ℂ) * I)‖ ≤ 0.00000014458 := by
  have hl := lg_3
  refine (ecis_approx ((((14996:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.474789876968827344 16.47478988446684234 2.374766 0.00000004457 (-0.7201161294369) 0.6938535581069 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p996_4 : ‖exp (-((((((14996:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3602333012365):ℝ):ℂ) + (((-0.9328622452848):ℝ):ℂ) * I)‖ ≤ 0.00000012503 := by
  have hl := lg_4
  refine (ecis_approx ((((14996:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.7888702315576 20.7888702465536 (-1.9393143) 0.00000002502 (-0.3602333012365) (-0.9328622452848) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p996_5 : ‖exp (-((((((14996:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5423116244243:ℝ):ℂ) + ((0.8401774229377:ℝ):ℂ) * I)‖ ≤ 0.00000011336 := by
  have hl := lg_5
  refine (ecis_approx ((((14996:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.135130927065478164 24.13513094206149316 0.9976103 0.00000001335 0.5423116244243 0.8401774229377 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p996_6 : ‖exp (-((((((14996:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1649304283111):ℝ):ℂ) + (((-0.9863052031782):ℝ):ℂ) * I)‖ ≤ 0.00000013599 := by
  have hl := lg_6
  refine (ecis_approx ((((14996:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.869224992747627344 26.86922500774364234 (-1.7364838) 0.00000003598 (-0.1649304283111) (-0.9863052031782) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p996_7 : ‖exp (-((((((14996:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6164778841071):ℝ):ℂ) + ((0.7873722235343:ℝ):ℂ) * I)‖ ≤ 0.00000014848 := by
  have hl := lg_7
  refine (ecis_approx ((((14996:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.180868587437188312 29.180868602433218304 2.2350579 0.00000004847 (-0.6164778841071) 0.7873722235343 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p996_8 : ‖exp (-((((((14996:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9730654761272:ℝ):ℂ) + ((0.2305289117863:ℝ):ℂ) * I)‖ ≤ 0.00000013395 := by
  have hl := lg_8
  refine (ecis_approx ((((14996:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.1833053473364 31.1833053698304 0.2326212 0.00000003394 0.9730654761272 0.2305289117863 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p996_9 : ‖exp (-((((((14996:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0371345868676:ℝ):ℂ) + (((-0.9993102733676):ℝ):ℂ) * I)‖ ≤ 0.00000013305 := by
  have hl := lg_9
  refine (ecis_approx ((((14996:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.949579753937654688 32.94957976893368468 (-1.5336532) 0.00000003304 0.0371345868676 (-0.9993102733676) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p996_10 : ‖exp (-((((((14996:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996093357383):ℝ):ℂ) + (((-0.0279495131182):ℝ):ℂ) * I)‖ ≤ 0.00000012946 := by
  have hl := lg_10
  refine (ecis_approx ((((14996:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.529566042844278164 34.52956606533829316 (-3.1136395) 0.00000002945 (-0.9996093357383) (-0.0279495131182) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p417_2 : ‖exp (-((((((15417:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3044149542818):ℝ):ℂ) + ((0.9525395191843:ℝ):ℂ) * I)‖ ≤ 0.00000013569 := by
  have hl := lg_2
  refine (ecis_approx ((((15417:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.6862500786851 10.6862500863936 1.8801205 0.00000003568 (-0.3044149542818) 0.9525395191843 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p417_3 : ‖exp (-((((((15417:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3348574791785):ℝ):ℂ) + ((0.9422687878923:ℝ):ℂ) * I)‖ ≤ 0.00000013657 := by
  have hl := lg_3
  refine (ecis_approx ((((15417:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.937305650388664388 16.937305658097179805 1.9122503 0.00000003656 (-0.3348574791785) 0.9422687878923 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p417_4 : ‖exp (-((((((15417:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8146630090502):ℝ):ℂ) + (((-0.579934635653):ℝ):ℂ) * I)‖ ≤ 0.00000015126 := by
  have hl := lg_4
  refine (ecis_approx ((((15417:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.3725001573702 21.3725001727872 (-2.5229442) 0.00000005125 (-0.8146630090502) (-0.579934635653) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p417_5 : ‖exp (-((((((15417:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9492238099301:ℝ):ℂ) + ((0.3146015871889:ℝ):ℂ) * I)‖ ≤ 0.00000014075 := by
  have hl := lg_5
  refine (ecis_approx ((((15417:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.812704287981360153 24.81270430339837557 0.3200369 0.00000004074 0.9492238099301 0.3146015871889 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p417_6 : ‖exp (-((((((15417:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7956126295894):ℝ):ℂ) + (((-0.6058056978853):ℝ):ℂ) * I)‖ ≤ 0.00000011579 := by
  have hl := lg_6
  refine (ecis_approx ((((15417:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.623555729073764388 27.623555744490779805 (-2.4908145) 0.00000001578 (-0.7956126295894) (-0.6058056978853) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p417_7 : ‖exp (-((((((15417:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.154347027292:ℝ):ℂ) + ((0.9880166978174:ℝ):ℂ) * I)‖ ≤ 0.0000001395 := by
  have hl := lg_7
  refine (ecis_approx ((((15417:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.000096759970600974 30.000096775387631808 1.4158298 0.00000003949 0.154347027292 0.9880166978174 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p417_8 : ‖exp (-((((((15417:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8004062616918:ℝ):ℂ) + (((-0.599457935342):ℝ):ℂ) * I)‖ ≤ 0.0000001233 := by
  have hl := lg_8
  refine (ecis_approx ((((15417:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.0587502360553 32.0587502591808 (-0.6428237) 0.00000002329 0.8004062616918 (-0.599457935342) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p417_9 : ‖exp (-((((((15417:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7757409958434):ℝ):ℂ) + (((-0.6310514300173):ℝ):ℂ) * I)‖ ≤ 0.00000013514 := by
  have hl := lg_9
  refine (ecis_approx ((((15417:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.874611300777328776 33.87461131619435961 (-2.4586848) 0.00000003513 (-0.7757409958434) (-0.6310514300173) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p417_10 : ‖exp (-((((((15417:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5886284481384):ℝ):ℂ) + ((0.8084037048598:ℝ):ℂ) * I)‖ ≤ 0.00000014673 := by
  have hl := lg_10
  refine (ecis_approx ((((15417:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.498954366666460153 35.49895438979197557 2.2001575 0.00000004672 (-0.5886284481384) 0.8084037048598 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p838_2 : ‖exp (-((((((15838:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.017508378569):ℝ):ℂ) + ((0.9998467165919:ℝ):ℂ) * I)‖ ≤ 0.00000013517 := by
  have hl := lg_2
  refine (ecis_approx ((((15838:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.9780650415914 10.9780650495104 1.5883056 0.00000003516 (-0.017508378569) 0.9998467165919 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p838_3 : ‖exp (-((((((15838:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1207663304162:ℝ):ℂ) + ((0.9926809625644:ℝ):ℂ) * I)‖ ≤ 0.0000001102 := by
  have hl := lg_3
  refine (ecis_approx ((((15838:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.399821423808501432 17.39982143172751727 1.4497345 0.00000001019 0.1207663304162 0.9926809625644 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p838_4 : ‖exp (-((((((15838:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993869163163):ℝ):ℂ) + (((-0.0350112966122):ℝ):ℂ) * I)‖ ≤ 0.00000013837 := by
  have hl := lg_4
  refine (ecis_approx ((((15838:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.9561300831828 21.9561300990208 (-3.1065742) 0.00000003836 (-0.9993869163163) (-0.0350112966122) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
