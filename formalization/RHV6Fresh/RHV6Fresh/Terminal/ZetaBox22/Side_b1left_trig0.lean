/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Base
/-!
# Certificat (V2), côté b1left (b1), angles 0

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

lemma cs_b1left_vm1_2 : ‖exp (-((((((-1000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7692388889425:ℝ):ℂ) + ((0.6389612912677:ℝ):ℂ) * I)‖ ≤ 0.00000011971 := by
  have hl := lg_2
  refine (ecis_approx ((((-1000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.6931471808) (-0.6931471803) 0.6931472 0.0000000197 0.7692388889425 0.6389612912677 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm1_3 : ‖exp (-((((((-1000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4548324127347:ℝ):ℂ) + ((0.8905770468219:ℝ):ℂ) * I)‖ ≤ 0.00000011161 := by
  have hl := lg_3
  refine (ecis_approx ((((-1000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-1.098612288908165) (-1.098612288408164) 1.0986123 0.0000000116 0.4548324127347 0.8905770468219 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm1_4 : ‖exp (-((((((-1000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1834569365231:ℝ):ℂ) + ((0.983027747544:ℝ):ℂ) * I)‖ ≤ 0.00000013941 := by
  have hl := lg_4
  refine (ecis_approx ((((-1000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-1.3862943616) (-1.3862943606) 1.3862944 0.0000000394 0.1834569365231 0.983027747544 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm1_5 : ‖exp (-((((((-1000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0386319575092):ℝ):ℂ) + ((0.9992535073037:ℝ):ℂ) * I)‖ ≤ 0.00000011293 := by
  have hl := lg_5
  refine (ecis_approx ((((-1000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-1.60943791291421) (-1.609437911914209) 1.6094379 0.00000001292 (-0.0386319575092) 0.9992535073037 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p806_2 : ‖exp (-((((((-806:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8479573406866:ℝ):ℂ) + ((0.5300644756779:ℝ):ℂ) * I)‖ ≤ 0.00000012774 := by
  have hl := lg_2
  refine (ecis_approx ((((-806:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.5586766277248) (-0.5586766273218) 0.5586766 0.00000002773 0.8479573406866 0.5300644756779 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p806_3 : ‖exp (-((((((-806:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6329167880249:ℝ):ℂ) + ((0.7742198263002:ℝ):ℂ) * I)‖ ≤ 0.00000010487 := by
  have hl := lg_3
  refine (ecis_approx ((((-806:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.88548150485998099) (-0.885481504456980184) 0.8854815 0.00000000486 0.6329167880249 0.7742198263002 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p806_4 : ‖exp (-((((((-806:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4380632133543:ℝ):ℂ) + ((0.8989441701829:ℝ):ℂ) * I)‖ ≤ 0.00000014537 := by
  have hl := lg_4
  refine (ecis_approx ((((-806:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-1.1173532554496) (-1.1173532546436) 1.1173533 0.00000004536 0.4380632133543 0.8989441701829 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p806_5 : ‖exp (-((((((-806:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2701889997792:ℝ):ℂ) + ((0.9628073038767:ℝ):ℂ) * I)‖ ≤ 0.00000014301 := by
  have hl := lg_5
  refine (ecis_approx ((((-806:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-1.29720695780885326) (-1.297206957002852454) 1.297207 0.000000043 0.2701889997792 0.9628073038767 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p558_2 : ‖exp (-((((((-558:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9261299406342:ℝ):ℂ) + ((0.377204630222:ℝ):ℂ) * I)‖ ≤ 0.0000001269 := by
  have hl := lg_2
  refine (ecis_approx ((((-558:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.3867761268864) (-0.3867761266074) 0.3867761 0.00000002689 0.9261299406342 0.377204630222 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p558_3 : ‖exp (-((((((-558:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8179109435374:ℝ):ℂ) + ((0.5753448430652:ℝ):ℂ) * I)‖ ≤ 0.00000014308 := by
  have hl := lg_3
  refine (ecis_approx ((((-558:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.61302565721075607) (-0.613025656931755512) 0.6130257 0.00000004307 0.8179109435374 0.5753448430652 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p558_4 : ‖exp (-((((((-558:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7154332640101:ℝ):ℂ) + ((0.6986810751322:ℝ):ℂ) * I)‖ ≤ 0.0000001468 := by
  have hl := lg_4
  refine (ecis_approx ((((-558:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.7735522537728) (-0.7735522532148) 0.7735523 0.00000004679 0.7154332640101 0.6986810751322 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p558_5 : ‖exp (-((((((-558:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6231234461992:ℝ):ℂ) + ((0.7821235009874:ℝ):ℂ) * I)‖ ≤ 0.00000014517 := by
  have hl := lg_5
  refine (ecis_approx ((((-558:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.89806635540612918) (-0.898066354848128622) 0.8980664 0.00000004516 0.6231234461992 0.7821235009874 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p354_2 : ‖exp (-((((((-354:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9700465167679:ℝ):ℂ) + ((0.2429192361804:ℝ):ℂ) * I)‖ ≤ 0.00000010202 := by
  have hl := lg_2
  refine (ecis_approx ((((-354:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.2453741020032) (-0.2453741018262) 0.2453741 0.00000000201 0.9700465167679 0.2429192361804 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p354_3 : ‖exp (-((((((-354:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9253233707209:ℝ):ℂ) + ((0.3791789282089:ℝ):ℂ) * I)‖ ≤ 0.00000014992 := by
  have hl := lg_3
  refine (ecis_approx ((((-354:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.38890875027349041) (-0.388908750096490056) 0.3889088 0.00000004991 0.9253233707209 0.3791789282089 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p354_4 : ‖exp (-((((((-354:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8819804893871:ℝ):ℂ) + ((0.4712859178254:ℝ):ℂ) * I)‖ ≤ 0.00000010402 := by
  have hl := lg_4
  refine (ecis_approx ((((-354:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.4907482040064) (-0.4907482036524) 0.4907482 0.00000000401 0.8819804893871 0.4712859178254 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p354_5 : ‖exp (-((((((-354:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8420407116235:ℝ):ℂ) + ((0.5394139782843:ℝ):ℂ) * I)‖ ≤ 0.00000012119 := by
  have hl := lg_5
  refine (ecis_approx ((((-354:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.56974102117163034) (-0.569741020817629986) 0.569741 0.00000002118 0.8420407116235 0.5394139782843 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p155_2 : ‖exp (-((((((-155:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9942341090174:ℝ):ℂ) + ((0.1072312289696:ℝ):ℂ) * I)‖ ≤ 0.00000011304 := by
  have hl := lg_2
  refine (ecis_approx ((((-155:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.107437813024) (-0.1074378129465) 0.1074378 0.00000001303 0.9942341090174 0.1072312289696 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p155_3 : ‖exp (-((((((-155:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.98553652686:ℝ):ℂ) + ((0.1694631352972:ℝ):ℂ) * I)‖ ≤ 0.0000001048 := by
  have hl := lg_3
  refine (ecis_approx ((((-155:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.170284904780765575) (-0.17028490470326542) 0.1702849 0.00000000479 0.98553652686 0.1694631352972 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p155_4 : ‖exp (-((((((-155:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9770029270673:ℝ):ℂ) + ((0.2132258907868:ℝ):ℂ) * I)‖ ≤ 0.00000012606 := by
  have hl := lg_4
  refine (ecis_approx ((((-155:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.214875626048) (-0.214875625893) 0.2148756 0.00000002605 0.9770029270673 0.2132258907868 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p155_5 : ‖exp (-((((((-155:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9690451626166:ℝ):ℂ) + ((0.2468835207327:ℝ):ℂ) * I)‖ ≤ 0.00000012367 := by
  have hl := lg_5
  refine (ecis_approx ((((-155:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.24946287650170255) (-0.249462876346702395) 0.2494629 0.00000002366 0.9690451626166 0.2468835207327 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p081_2 : ‖exp (-((((((81:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9984242890868:ℝ):ℂ) + (((-0.0561154075238):ℝ):ℂ) * I)‖ ≤ 0.00000012166 := by
  have hl := lg_2
  refine (ecis_approx ((((81:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.0561449216043 0.0561449216448 (-0.0561449) 0.00000002165 0.9984242890868 (-0.0561154075238) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p081_3 : ‖exp (-((((((81:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.996043215637:ℝ):ℂ) + (((-0.0888702007627):ℝ):ℂ) * I)‖ ≤ 0.00000010465 := by
  have hl := lg_3
  refine (ecis_approx ((((81:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.088987595361061284 0.088987595401561365 (-0.0889876) 0.00000000464 0.996043215637 (-0.0888702007627) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p081_4 : ‖exp (-((((((81:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9937021220769:ℝ):ℂ) + (((-0.1120539717276):ℝ):ℂ) * I)‖ ≤ 0.0000001433 := by
  have hl := lg_4
  refine (ecis_approx ((((81:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.1122898432086 0.1122898432896 (-0.1122898) 0.00000004329 0.9937021220769 (-0.1120539717276) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p081_5 : ‖exp (-((((((81:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9915145762013:ℝ):ℂ) + (((-0.1299955583103):ℝ):ℂ) * I)‖ ≤ 0.00000012915 := by
  have hl := lg_5
  refine (ecis_approx ((((81:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 0.130364470865050929 0.13036447094605101 (-0.1303645) 0.00000002914 0.9915145762013 (-0.1299955583103) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p317_2 : ‖exp (-((((((317:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9759568370762:ℝ):ℂ) + (((-0.2179638781181):ℝ):ℂ) * I)‖ ≤ 0.00000014386 := by
  have hl := lg_2
  refine (ecis_approx ((((317:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.2197276561551 0.2197276563136 (-0.2197277) 0.00000004385 0.9759568370762 (-0.2179638781181) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p317_3 : ‖exp (-((((((317:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9399678985829:ℝ):ℂ) + (((-0.3412628746781):ℝ):ℂ) * I)‖ ≤ 0.00000010459 := by
  have hl := lg_3
  refine (ecis_approx ((((317:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.348260095425387988 0.348260095583888305 (-0.3482601) 0.00000000458 0.9399678985829 (-0.3412628746781) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p317_4 : ‖exp (-((((((317:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9049835382161:ℝ):ℂ) + (((-0.4254465836717):ℝ):ℂ) * I)‖ ≤ 0.00000011264 := by
  have hl := lg_4
  refine (ecis_approx ((((317:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.4394553123102 0.4394553126272 (-0.4394553) 0.00000001263 0.9049835382161 (-0.4254465836717) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p317_5 : ‖exp (-((((((317:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8726508591974:ℝ):ℂ) + (((-0.4883446302991):ℝ):ℂ) * I)‖ ≤ 0.00000011841 := by
  have hl := lg_5
  refine (ecis_approx ((((317:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 0.510191818076804253 0.51019181839380457 (-0.5101918) 0.0000000184 0.8726508591974 (-0.4883446302991) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p494_2 : ‖exp (-((((((494:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9419466465352:ℝ):ℂ) + (((-0.3357625873756):ℝ):ℂ) * I)‖ ≤ 0.00000010733 := by
  have hl := lg_2
  refine (ecis_approx ((((494:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.3424147070682 0.3424147073152 (-0.3424147) 0.00000000732 0.9419466465352 (-0.3357625873756) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p494_3 : ‖exp (-((((((494:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8563099009128:ℝ):ℂ) + (((-0.5164623448024):ℝ):ℂ) * I)‖ ≤ 0.00000012954 := by
  have hl := lg_3
  refine (ecis_approx ((((494:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.542714470473633016 0.54271447072063351 (-0.5427145) 0.00000002953 0.8563099009128 (-0.5164623448024) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p494_4 : ‖exp (-((((((494:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7745269698377:ℝ):ℂ) + (((-0.6325408864208):ℝ):ℂ) * I)‖ ≤ 0.00000011465 := by
  have hl := lg_4
  refine (ecis_approx ((((494:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.6848294141364 0.6848294146304 (-0.6848294) 0.00000001464 0.7745269698377 (-0.6325408864208) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p494_5 : ‖exp (-((((((494:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7002402909795:ℝ):ℂ) + (((-0.7139072312906):ℝ):ℂ) * I)‖ ≤ 0.00000012899 := by
  have hl := lg_5
  refine (ecis_approx ((((494:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 0.795062328485619246 0.79506232897961974 (-0.7950623) 0.00000002898 0.7002402909795 (-0.7139072312906) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p73_2 : ‖exp (-((((((730:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8746914896505:ℝ):ℂ) + (((-0.4846800985526):ℝ):ℂ) * I)‖ ≤ 0.000000142 := by
  have hl := lg_2
  refine (ecis_approx ((((730:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.505997441619 0.505997441984 (-0.5059974) 0.00000004199 0.8746914896505 (-0.4846800985526) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p73_3 : ‖exp (-((((((730:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.695279948375:ℝ):ℂ) + (((-0.718739030099):ℝ):ℂ) * I)‖ ≤ 0.00000012948 := by
  have hl := lg_3
  refine (ecis_approx ((((730:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.80198697053795972 0.80198697090296045 (-0.801987) 0.00000002947 0.695279948375 (-0.718739030099) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p73_4 : ‖exp (-((((((730:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.530170319345:ℝ):ℂ) + (((-0.8478911678309):ℝ):ℂ) * I)‖ ≤ 0.00000011678 := by
  have hl := lg_4
  refine (ecis_approx ((((730:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 1.011994883238 1.011994883968 (-1.0119949) 0.00000001677 0.530170319345 (-0.8478911678309) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p73_5 : ‖exp (-((((((730:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3856448439597:ℝ):ℂ) + (((-0.9226473076573):ℝ):ℂ) * I)‖ ≤ 0.00000012432 := by
  have hl := lg_5
  refine (ecis_approx ((((730:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 1.17488967569737257 1.1748896764273733 (-1.1748897) 0.00000002431 0.3856448439597 (-0.9226473076573) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p966_2 : ‖exp (-((((((966:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7840822867233:ℝ):ℂ) + (((-0.6206568839921):ℝ):ℂ) * I)‖ ≤ 0.00000012385 := by
  have hl := lg_2
  refine (ecis_approx ((((966:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.6695801761698 0.6695801766528 (-0.6695802) 0.00000002384 0.7840822867233 (-0.6206568839921) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p966_3 : ‖exp (-((((((966:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4877729626623:ℝ):ℂ) + (((-0.8729705246431):ℝ):ℂ) * I)‖ ≤ 0.00000012941 := by
  have hl := lg_3
  refine (ecis_approx ((((966:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.061259470602286424 1.06125947108528739 (-1.0612595) 0.0000000294 0.4877729626623 (-0.8729705246431) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p966_4 : ‖exp (-((((((966:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2295700647065:ℝ):ℂ) + (((-0.9732921377421):ℝ):ℂ) * I)‖ ≤ 0.00000014768 := by
  have hl := lg_4
  refine (ecis_approx ((((966:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 1.3391603523396 1.3391603533056 (-1.3391604) 0.00000004767 0.2295700647065 (-0.9732921377421) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p966_5 : ‖exp (-((((((966:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0160786339329:ℝ):ℂ) + (((-0.99987073041):ℝ):ℂ) * I)‖ ≤ 0.00000012389 := by
  have hl := lg_5
  refine (ecis_approx ((((966:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 1.554717022909125894 1.55471702387512686 (-1.554717) 0.00000002388 0.0160786339329 (-0.99987073041) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p281_2 : ‖exp (-((((((1281:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6310258094574:ℝ):ℂ) + (((-0.7757618370341):ℝ):ℂ) * I)‖ ≤ 0.00000013862 := by
  have hl := lg_2
  refine (ecis_approx ((((1281:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.8879215379643 0.8879215386048 (-0.8879215) 0.00000003861 0.6310258094574 (-0.7757618370341) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p281_3 : ‖exp (-((((((1281:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1627468923569:ℝ):ℂ) + (((-0.9866678514212):ℝ):ℂ) * I)‖ ≤ 0.00000014211 := by
  have hl := lg_3
  refine (ecis_approx ((((1281:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.407322341450858084 1.407322342091359365 (-1.4073223) 0.0000000421 0.1627468923569 (-0.9866678514212) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p281_4 : ‖exp (-((((((1281:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2036129535024):ℝ):ℂ) + (((-0.9790514619595):ℝ):ℂ) * I)‖ ≤ 0.00000012409 := by
  have hl := lg_4
  refine (ecis_approx ((((1281:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 1.7758430759286 1.7758430772096 (-1.7758431) 0.00000002408 (-0.2036129535024) (-0.9790514619595) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p281_5 : ‖exp (-((((((1281:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4714142173668):ℝ):ℂ) + (((-0.8819119205789):ℝ):ℂ) * I)‖ ≤ 0.00000013485 := by
  have hl := lg_5
  refine (ecis_approx ((((1281:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 2.061689965162101729 2.06168996644310301 (-2.06169) 0.00000003484 (-0.4714142173668) (-0.8819119205789) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p517_2 : ‖exp (-((((((1517:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4962656206443:ℝ):ℂ) + (((-0.8681707399852):ℝ):ℂ) * I)‖ ≤ 0.0000001275 := by
  have hl := lg_2
  refine (ecis_approx ((((1517:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.0515042725151 1.0515042732736 (-1.0515043) 0.00000002749 0.4962656206443 (-0.8681707399852) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p517_3 : ‖exp (-((((((1517:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0956520111154):ℝ):ℂ) + (((-0.9954148345133):ℝ):ℂ) * I)‖ ≤ 0.00000014229 := by
  have hl := lg_3
  refine (ecis_approx ((((1517:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.666594841515184788 1.666594842273686305 (-1.6665948) 0.00000004228 (-0.0956520111154) (-0.9954148345133) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p517_4 : ‖exp (-((((((1517:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5074407813641):ℝ):ℂ) + (((-0.8616866329484):ℝ):ℂ) * I)‖ ≤ 0.00000014656 := by
  have hl := lg_4
  refine (ecis_approx ((((1517:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 2.1030085450302 2.1030085465472 (-2.1030085) 0.00000004655 (-0.5074407813641) (-0.8616866329484) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p517_5 : ‖exp (-((((((1517:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.764793640991):ℝ):ℂ) + (((-0.6442753189918):ℝ):ℂ) * I)‖ ≤ 0.00000011391 := by
  have hl := lg_5
  refine (ecis_approx ((((1517:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 2.441517312373855053 2.44151731389085657 (-2.4415173) 0.0000000139 (-0.764793640991) (-0.6442753189918) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p753_2 : ‖exp (-((((((1753:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3482553755146:ℝ):ℂ) + (((-0.9373996977945):ℝ):ℂ) * I)‖ ≤ 0.00000010796 := by
  have hl := lg_2
  refine (ecis_approx ((((1753:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.2150870070659 1.2150870079424 (-1.215087) 0.00000000795 0.3482553755146 (-0.9373996977945) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p753_3 : ‖exp (-((((((1753:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.347656912137):ℝ):ℂ) + (((-0.9376218168542):ℝ):ℂ) * I)‖ ≤ 0.00000014247 := by
  have hl := lg_3
  refine (ecis_approx ((((1753:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.925867341579511492 1.925867342456013245 (-1.9258673) 0.00000004246 (-0.347656912137) (-0.9376218168542) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p753_4 : ‖exp (-((((((1753:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7574363868442):ℝ):ℂ) + (((-0.6529089675052):ℝ):ℂ) * I)‖ ≤ 0.0000001159 := by
  have hl := lg_4
  refine (ecis_approx ((((1753:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 2.4301740141318 2.4301740158848 (-2.430174) 0.00000001589 (-0.7574363868442) (-0.6529089675052) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p753_5 : ‖exp (-((((((1753:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.949157390924):ℝ):ℂ) + (((-0.3148019171688):ℝ):ℂ) * I)‖ ≤ 0.00000014043 := by
  have hl := lg_5
  refine (ecis_approx ((((1753:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 2.821344659585608377 2.82134466133861013 (-2.8213447) 0.00000004042 (-0.949157390924) (-0.3148019171688) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p989_2 : ‖exp (-((((((1989:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1909468228605:ℝ):ℂ) + (((-0.9816003824568):ℝ):ℂ) * I)‖ ≤ 0.00000014263 := by
  have hl := lg_2
  refine (ecis_approx ((((1989:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.3786697416167 1.3786697426112 (-1.3786697) 0.00000004262 0.1909468228605 (-0.9816003824568) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p989_3 : ‖exp (-((((((1989:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5764221643276):ℝ):ℂ) + (((-0.8171520595713):ℝ):ℂ) * I)‖ ≤ 0.00000014265 := by
  have hl := lg_3
  refine (ecis_approx ((((1989:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 2.185139841643838196 2.185139842638340185 (-2.1851398) 0.00000004264 (-0.5764221643276) (-0.8171520595713) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p989_4 : ‖exp (-((((((1989:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9270786591154):ℝ):ℂ) + (((-0.374866855908):ℝ):ℂ) * I)‖ ≤ 0.00000011678 := by
  have hl := lg_4
  refine (ecis_approx ((((1989:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 2.7573394832334 2.7573394852224 (-2.7573395) 0.00000001677 (-0.9270786591154) (-0.374866855908) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p989_5 : ‖exp (-((((((1989:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9982256750042):ℝ):ℂ) + ((0.0595441114586:ℝ):ℂ) * I)‖ ≤ 0.00000010162 := by
  have hl := lg_5
  refine (ecis_approx ((((1989:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.201172006797361701 3.20117200878636369 3.0820133 0.00000000161 (-0.9982256750042) 0.0595441114586 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p304_2 : ‖exp (-((((((2304:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0262117707803):ℝ):ℂ) + (((-0.99965641251):ℝ):ℂ) * I)‖ ≤ 0.00000010458 := by
  have hl := lg_2
  refine (ecis_approx ((((2304:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.5970111034112 1.5970111045632 (-1.5970111) 0.00000000457 (-0.0262117707803) (-0.99965641251) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p304_3 : ‖exp (-((((((2304:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8194245637966):ℝ):ℂ) + (((-0.5731870411911):ℝ):ℂ) * I)‖ ≤ 0.00000011366 := by
  have hl := lg_3
  refine (ecis_approx ((((2304:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 2.531202712492409856 2.53120271364441216 (-2.5312027) 0.00000001365 (-0.8194245637966) (-0.5731870411911) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p304_4 : ‖exp (-((((((2304:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9986258854982):ℝ):ℂ) + ((0.0524055363972:ℝ):ℂ) * I)‖ ≤ 0.00000010196 := by
  have hl := lg_4
  refine (ecis_approx ((((2304:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.1940222068224 3.1940222091264 3.0891631 0.00000000195 (-0.9986258854982) 0.0524055363972 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p304_5 : ‖exp (-((((((2304:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8437564821036):ℝ):ℂ) + ((0.5367261860931:ℝ):ℂ) * I)‖ ≤ 0.00000014419 := by
  have hl := lg_5
  refine (ecis_approx ((((2304:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.708144949050337536 3.70814495135433984 2.5750404 0.00000004418 (-0.8437564821036) 0.5367261860931 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p619_2 : ‖exp (-((((((2619:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2421257279736):ℝ):ℂ) + (((-0.9702448824148):ℝ):ℂ) * I)‖ ≤ 0.00000013481 := by
  have hl := lg_2
  refine (ecis_approx ((((2619:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.8153524652057 1.8153524665152 (-1.8153525) 0.0000000348 (-0.2421257279736) (-0.9702448824148) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p619_3 : ‖exp (-((((((2619:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9652685331496):ℝ):ℂ) + (((-0.2612597532327):ℝ):ℂ) * I)‖ ≤ 0.00000011667 := by
  have hl := lg_3
  refine (ecis_approx ((((2619:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 2.877265583340981516 2.877265584650484135 (-2.8772656) 0.00000001666 (-0.9652685331496) (-0.2612597532327) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p619_4 : ‖exp (-((((((2619:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8827503072903):ℝ):ℂ) + ((0.4698424149438:ℝ):ℂ) * I)‖ ≤ 0.00000012587 := by
  have hl := lg_4
  refine (ecis_approx ((((2619:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.6307049304114 3.6307049330304 2.6524804 0.00000002586 (-0.8827503072903) 0.4698424149438 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p619_5 : ‖exp (-((((((2619:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4770288978589):ℝ):ℂ) + ((0.8788876097671:ℝ):ℂ) * I)‖ ≤ 0.00000011589 := by
  have hl := lg_5
  refine (ecis_approx ((((2619:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.215117891303313371 4.21511789392231599 2.0680674 0.00000001588 (-0.4770288978589) 0.8788876097671 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p934_2 : ‖exp (-((((((2934:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4465425278859):ℝ):ℂ) + (((-0.8947624102435):ℝ):ℂ) * I)‖ ≤ 0.00000012848 := by
  have hl := lg_2
  refine (ecis_approx ((((2934:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.0336938270002 2.0336938284672 (-2.0336938) 0.00000002847 (-0.4465425278859) (-0.8947624102435) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p934_3 : ‖exp (-((((((2934:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9966614923173):ℝ):ℂ) + ((0.081644774618:ℝ):ℂ) * I)‖ ≤ 0.00000014849 := by
  have hl := lg_3
  refine (ecis_approx ((((2934:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.223328454189553176 3.22332845565655611 3.0598569 0.00000004848 (-0.9966614923173) 0.081644774618 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p934_4 : ‖exp (-((((((2934:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6011995358404):ℝ):ℂ) + ((0.7990989413665:ℝ):ℂ) * I)‖ ≤ 0.00000014977 := by
  have hl := lg_4
  refine (ecis_approx ((((2934:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.0673876540004 4.0673876569344 2.2157977 0.00000004976 (-0.6011995358404) 0.7990989413665 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p934_5 : ‖exp (-((((((2934:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0097016745975:ℝ):ℂ) + ((0.9999529376475:ℝ):ℂ) * I)‖ ≤ 0.00000012933 := by
  have hl := lg_5
  refine (ecis_approx ((((2934:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.722090833556289206 4.72209083649029214 1.5610945 0.00000002932 0.0097016745975 0.9999529376475 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p249_2 : ‖exp (-((((((3249:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6297558552391):ℝ):ℂ) + (((-0.776793127401):ℝ):ℂ) * I)‖ ≤ 0.00000011122 := by
  have hl := lg_2
  refine (ecis_approx ((((3249:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.2520351887947 2.2520351904192 (-2.2520352) 0.00000001121 (-0.6297558552391) (-0.776793127401) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p249_3 : ‖exp (-((((((3249:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9098812235495):ℝ):ℂ) + ((0.4148688454241:ℝ):ℂ) * I)‖ ≤ 0.0000001195 := by
  have hl := lg_3
  refine (ecis_approx ((((3249:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.569391325038124836 3.569391326662628085 2.713794 0.00000001949 (-0.9098812235495) 0.4148688454241 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p249_4 : ‖exp (-((((((3249:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2068151185564):ℝ):ℂ) + ((0.9783800420775:ℝ):ℂ) * I)‖ ≤ 0.00000012961 := by
  have hl := lg_4
  refine (ecis_approx ((((3249:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.5040703775894 4.5040703808384 1.7791149 0.0000000296 (-0.2068151185564) 0.9783800420775 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p249_5 : ‖exp (-((((((3249:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4939917471344:ℝ):ℂ) + ((0.8694665915164:ℝ):ℂ) * I)‖ ≤ 0.00000013139 := by
  have hl := lg_5
  refine (ecis_approx ((((3249:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.229063775809265041 5.22906377905826829 1.0541215 0.00000003138 0.4939917471344 0.8694665915164 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p67_2 : ‖exp (-((((((3670:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8266082172349):ℝ):ℂ) + (((-0.5627778026352):ℝ):ℂ) * I)‖ ≤ 0.00000014831 := by
  have hl := lg_2
  refine (ecis_approx ((((3670:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.543850151701 2.543850153536 (-2.5438502) 0.0000000483 (-0.8266082172349) (-0.5627778026352) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p67_3 : ‖exp (-((((((3670:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6291676424574):ℝ):ℂ) + ((0.7772696299676:ℝ):ℂ) * I)‖ ≤ 0.00000010874 := by
  have hl := lg_3
  refine (ecis_approx ((((3670:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.03190709845796188 4.03190710029296555 2.2512782 0.00000000873 (-0.6291676424574) 0.7772696299676 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p67_4 : ‖exp (-((((((3670:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3665622032866:ℝ):ℂ) + ((0.9303935463672:ℝ):ℂ) * I)‖ ≤ 0.00000010379 := by
  have hl := lg_4
  refine (ecis_approx ((((3670:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.087700303402 5.087700307072 1.195485 0.00000000378 0.3665622032866 0.9303935463672 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p67_5 : ‖exp (-((((((3670:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9299394438319:ℝ):ℂ) + ((0.3677127014473:ℝ):ℂ) * I)‖ ≤ 0.00000013323 := by
  have hl := lg_5
  refine (ecis_approx ((((3670:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.90663713672514703 5.9066371403951507 0.3765482 0.00000003322 0.9299394438319 0.3677127014473 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p091_2 : ‖exp (-((((((4091:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9535680041942):ℝ):ℂ) + (((-0.3011777899578):ℝ):ℂ) * I)‖ ≤ 0.00000011667 := by
  have hl := lg_2
  refine (ecis_approx ((((4091:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.8356651146073 2.8356651166528 (-2.8356651) 0.00000001666 (-0.9535680041942) (-0.3011777899578) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p091_3 : ‖exp (-((((((4091:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2162442690859):ℝ):ℂ) + ((0.9763392935279:ℝ):ℂ) * I)‖ ≤ 0.00000013532 := by
  have hl := lg_3
  refine (ecis_approx ((((4091:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.494422871877798924 4.494422873923303015 1.7887624 0.00000003531 (-0.2162442690859) 0.9763392935279 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p091_4 : ‖exp (-((((((4091:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8185838816635:ℝ):ℂ) + ((0.5743870025346:ℝ):ℂ) * I)‖ ≤ 0.00000012614 := by
  have hl := lg_4
  refine (ecis_approx ((((4091:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.6713302292146 5.6713302333056 0.6118551 0.00000002613 0.8185838816635 0.5743870025346 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p091_5 : ‖exp (-((((((4091:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9550330198168:ℝ):ℂ) + (((-0.2964994621574):ℝ):ℂ) * I)‖ ≤ 0.00000010955 := by
  have hl := lg_5
  refine (ecis_approx ((((4091:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.584210497641029019 6.58421050173203311 (-0.3010252) 0.00000000954 0.9550330198168 (-0.2964994621574) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p406_2 : ‖exp (-((((((4406:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9961667840501):ℝ):ℂ) + (((-0.0874742125248):ℝ):ℂ) * I)‖ ≤ 0.00000012361 := by
  have hl := lg_2
  refine (ecis_approx ((((4406:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 3.0540064764018 3.0540064786048 (-3.0540065) 0.0000000236 (-0.9961667840501) (-0.0874742125248) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p406_3 : ‖exp (-((((((4406:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1277466957791:ℝ):ℂ) + ((0.9918068268153:ℝ):ℂ) * I)‖ ≤ 0.00000013776 := by
  have hl := lg_3
  refine (ecis_approx ((((4406:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.840485742726370584 4.84048574492937499 1.4426996 0.00000003775 0.1277466957791 0.9918068268153 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p406_4 : ‖exp (-((((((4406:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9846965080283:ℝ):ℂ) + ((0.1742779018607:ℝ):ℂ) * I)‖ ≤ 0.00000015005 := by
  have hl := lg_4
  refine (ecis_approx ((((4406:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.1080129528036 6.1080129572096 0.1751724 0.00000005004 0.9846965080283 0.1742779018607 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p406_5 : ‖exp (-((((((4406:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6909470008599:ℝ):ℂ) + (((-0.7229054170517):ℝ):ℂ) * I)‖ ≤ 0.00000013714 := by
  have hl := lg_5
  refine (ecis_approx ((((4406:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.091183439894004854 7.09118344430000926 (-0.8079981) 0.00000003713 0.6909470008599 (-0.7229054170517) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p721_2 : ‖exp (-((((((4721:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9914637171264):ℝ):ℂ) + ((0.130382886907:ℝ):ℂ) * I)‖ ≤ 0.00000013339 := by
  have hl := lg_2
  refine (ecis_approx ((((4721:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.2723478381963 3.2723478405568 3.0108375 0.00000003338 (-0.9914637171264) 0.130382886907 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p721_3 : ‖exp (-((((((4721:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4565909479998:ℝ):ℂ) + ((0.8896767425333:ℝ):ℂ) * I)‖ ≤ 0.00000010877 := by
  have hl := lg_3
  refine (ecis_approx ((((4721:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.186548613574942244 5.186548615935446965 1.0966367 0.00000000876 0.4565909479998 0.8896767425333 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p721_4 : ‖exp (-((((((4721:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9660005815001:ℝ):ℂ) + (((-0.2585398935202):ℝ):ℂ) * I)‖ ≤ 0.0000001308 := by
  have hl := lg_4
  refine (ecis_approx ((((4721:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.5446956763926 6.5446956811136 (-0.2615104) 0.00000003079 0.9660005815001 (-0.2585398935202) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p721_5 : ‖exp (-((((((4721:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2530438643343:ℝ):ℂ) + (((-0.9674548065531):ℝ):ℂ) * I)‖ ≤ 0.00000012505 := by
  have hl := lg_5
  refine (ecis_approx ((((4721:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.598156382146980689 7.59815638686798541 (-1.3149711) 0.00000002504 0.2530438643343 (-0.9674548065531) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p036_2 : ‖exp (-((((((5036:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9396821191722):ℝ):ℂ) + ((0.3420489946327:ℝ):ℂ) * I)‖ ≤ 0.0000001072 := by
  have hl := lg_2
  refine (ecis_approx ((((5036:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.4906891999908 3.4906892025088 2.7924961 0.00000000719 (-0.9396821191722) 0.3420489946327 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p036_3 : ‖exp (-((((((5036:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7312976241218:ℝ):ℂ) + ((0.6820584908597:ℝ):ℂ) * I)‖ ≤ 0.00000012277 := by
  have hl := lg_3
  refine (ecis_approx ((((5036:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.532611484423513904 5.53261148694151894 0.7505738 0.00000002276 0.7312976241218 0.6820584908597 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p036_4 : ‖exp (-((((((5036:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7660049750286:ℝ):ℂ) + (((-0.6428346429926):ℝ):ℂ) * I)‖ ≤ 0.00000010721 := by
  have hl := lg_4
  refine (ecis_approx ((((5036:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.9813783999816 6.9813784050176 (-0.6981931) 0.0000000072 0.7660049750286 (-0.6428346429926) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p036_5 : ‖exp (-((((((5036:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2485157909005):ℝ):ℂ) + (((-0.9686278447742):ℝ):ℂ) * I)‖ ≤ 0.00000012227 := by
  have hl := lg_5
  refine (ecis_approx ((((5036:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.105129324399956524 8.10512932943596156 (-1.821944) 0.00000002226 (-0.2485157909005) (-0.9686278447742) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p351_2 : ‖exp (-((((((5351:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8432807728343):ℝ):ℂ) + ((0.5374732905905:ℝ):ℂ) * I)‖ ≤ 0.00000014541 := by
  have hl := lg_2
  refine (ecis_approx ((((5351:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.7090305617853 3.7090305644608 2.5741547 0.0000000454 (-0.8432807728343) 0.5374732905905 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p351_3 : ‖exp (-((((((5351:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9192949624436:ℝ):ℂ) + ((0.3935692722074:ℝ):ℂ) * I)‖ ≤ 0.00000015078 := by
  have hl := lg_3
  refine (ecis_approx ((((5351:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.878674355272085564 5.878674357947590915 0.404511 0.00000005077 0.9192949624436 0.3935692722074 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p351_4 : ‖exp (-((((((5351:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.422245020877:ℝ):ℂ) + (((-0.906481738561):ℝ):ℂ) * I)‖ ≤ 0.00000012176 := by
  have hl := lg_4
  refine (ecis_approx ((((5351:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.4180611235706 7.4180611289216 (-1.1348758) 0.00000002175 0.422245020877 (-0.906481738561) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p351_5 : ‖exp (-((((((5351:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6875580255829):ℝ):ℂ) + (((-0.7261294384852):ℝ):ℂ) * I)‖ ≤ 0.00000014054 := by
  have hl := lg_5
  refine (ecis_approx ((((5351:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.612102266652932359 8.61210227200393771 (-2.328917) 0.00000004053 (-0.6875580255829) (-0.7261294384852) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p666_2 : ‖exp (-((((((5666:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7068372583839):ℝ):ℂ) + ((0.7073762012787:ℝ):ℂ) * I)‖ ≤ 0.00000011925 := by
  have hl := lg_2
  refine (ecis_approx ((((5666:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.9273719235798 3.9273719264128 2.3558134 0.00000001924 (-0.7068372583839) 0.7073762012787 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p666_3 : ‖exp (-((((((5666:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9982923960098:ℝ):ℂ) + ((0.0584148274749:ℝ):ℂ) * I)‖ ≤ 0.00000012179 := by
  have hl := lg_3
  refine (ecis_approx ((((5666:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.224737226120657224 6.22473722895366289 0.0584481 0.00000002178 0.9982923960098 0.0584148274749 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p666_4 : ‖exp (-((((((5666:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0007621731314):ℝ):ℂ) + (((-0.9999997095459):ℝ):ℂ) * I)‖ ≤ 0.00000014566 := by
  have hl := lg_4
  refine (ecis_approx ((((5666:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.8547438471596 7.8547438528256 (-1.5715585) 0.00000004565 (-0.0007621731314) (-0.9999997095459) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p666_5 : ‖exp (-((((((5666:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9536356848664):ℝ):ℂ) + (((-0.3009634202621):ℝ):ℂ) * I)‖ ≤ 0.00000010741 := by
  have hl := lg_5
  refine (ecis_approx ((((5666:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.119075208905908194 9.11907521457191386 (-2.8358899) 0.0000000074 (-0.9536356848664) (-0.3009634202621) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p981_2 : ‖exp (-((((((5981:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5368303181439):ℝ):ℂ) + ((0.8436902331505:ℝ):ℂ) * I)‖ ≤ 0.00000012182 := by
  have hl := lg_2
  refine (ecis_approx ((((5981:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.1457132853743 4.1457132883648 2.137472 0.00000002181 (-0.5368303181439) 0.8436902331505 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p981_3 : ‖exp (-((((((5981:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9589232023041:ℝ):ℂ) + (((-0.2836658105638):ℝ):ℂ) * I)‖ ≤ 0.00000011023 := by
  have hl := lg_3
  refine (ecis_approx ((((5981:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.570800096969228884 6.570800099959734865 (-0.2876148) 0.00000001022 0.9589232023041 (-0.2836658105638) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p981_4 : ‖exp (-((((((5981:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4236264125388):ℝ):ℂ) + (((-0.9058369955989):ℝ):ℂ) * I)‖ ≤ 0.00000013645 := by
  have hl := lg_4
  refine (ecis_approx ((((5981:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.2914265707486 8.2914265767296 (-2.0082413) 0.00000003644 (-0.4236264125388) (-0.9058369955989) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p981_5 : ‖exp (-((((((5981:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9798134466474):ℝ):ℂ) + ((0.1999140051269:ℝ):ℂ) * I)‖ ≤ 0.0000001428 := by
  have hl := lg_5
  refine (ecis_approx ((((5981:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.626048151158884029 9.62604815713989001 2.9403225 0.00000004279 (-0.9798134466474) 0.1999140051269 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p402_2 : ‖exp (-((((((6402:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2714129389492):ℝ):ℂ) + ((0.9624629949092:ℝ):ℂ) * I)‖ ≤ 0.00000014432 := by
  have hl := lg_2
  refine (ecis_approx ((((6402:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.4375282482806 4.4375282514816 1.8456571 0.00000004431 (-0.2714129389492) 0.9624629949092 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p402_3 : ‖exp (-((((((6402:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.731599840612:ℝ):ℂ) + (((-0.6817343127762):ℝ):ℂ) * I)‖ ≤ 0.00000013681 := by
  have hl := lg_3
  refine (ecis_approx ((((6402:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.033315870389065928 7.03331587359007233 (-0.7501306) 0.0000000368 0.731599840612 (-0.6817343127762) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p402_4 : ‖exp (-((((((6402:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8526700816173):ℝ):ℂ) + (((-0.5224497409697):ℝ):ℂ) * I)‖ ≤ 0.00000011063 := by
  have hl := lg_4
  refine (ecis_approx ((((6402:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.8750564965612 8.8750565029632 (-2.5918712) 0.00000001062 (-0.8526700816173) (-0.5224497409697) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p402_5 : ‖exp (-((((((6402:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6380420361553):ℝ):ℂ) + ((0.7700015325201:ℝ):ℂ) * I)‖ ≤ 0.00000010413 := by
  have hl := lg_5
  refine (ecis_approx ((((6402:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.303621512074766018 10.30362151847677242 2.2627491 0.00000000412 (-0.6380420361553) 0.7700015325201 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p823_2 : ‖exp (-((((((6823:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0169534145696:ℝ):ℂ) + ((0.9998562805395:ℝ):ℂ) * I)‖ ≤ 0.00000010743 := by
  have hl := lg_2
  refine (ecis_approx ((((6823:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.7293432111869 4.7293432145984 1.5538421 0.00000000742 0.0169534145696 0.9998562805395 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p823_3 : ‖exp (-((((((6823:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3505422474045:ℝ):ℂ) + (((-0.936546919692):ℝ):ℂ) * I)‖ ≤ 0.00000014006 := by
  have hl := lg_3
  refine (ecis_approx ((((6823:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.495831643808902972 7.495831647220409795 (-1.2126463) 0.00000004005 0.3505422474045 (-0.936546919692) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p823_4 : ‖exp (-((((((6823:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9994251631741):ℝ):ℂ) + ((0.033901955793:ℝ):ℂ) * I)‖ ≤ 0.00000011485 := by
  have hl := lg_4
  refine (ecis_approx ((((6823:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.4586864223738 9.4586864291968 3.1076842 0.00000001484 (-0.9994251631741) 0.033901955793 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p823_5 : ‖exp (-((((((6823:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0143788776818):ℝ):ℂ) + ((0.9998966185943:ℝ):ℂ) * I)‖ ≤ 0.00000014138 := by
  have hl := lg_5
  refine (ecis_approx ((((6823:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.981194872990648007 10.98119487981365483 1.5851757 0.00000004137 (-0.0143788776818) 0.9998966185943 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p244_2 : ‖exp (-((((((7244:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3038862990474:ℝ):ℂ) + ((0.952708306488:ℝ):ℂ) * I)‖ ≤ 0.0000001331 := by
  have hl := lg_2
  refine (ecis_approx ((((7244:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.0211581740932 5.0211581777152 1.2620271 0.00000003309 0.3038862990474 0.952708306488 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p244_3 : ‖exp (-((((((7244:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1041764139616):ℝ):ℂ) + (((-0.9945588342444):ℝ):ℂ) * I)‖ ≤ 0.00000011369 := by
  have hl := lg_3
  refine (ecis_approx ((((7244:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.958347417228740016 7.95834742085074726 (-1.6751621) 0.00000001368 (-0.1041764139616) (-0.9945588342444) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p244_4 : ‖exp (-((((((7244:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8153062923935):ℝ):ℂ) + ((0.5790299210992:ℝ):ℂ) * I)‖ ≤ 0.00000014109 := by
  have hl := lg_4
  refine (ecis_approx ((((7244:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.0423163481864 10.0423163554304 2.5240543 0.00000004108 (-0.8153062923935) 0.5790299210992 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p244_5 : ‖exp (-((((((7244:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.615636897788:ℝ):ℂ) + ((0.7880299550664:ℝ):ℂ) * I)‖ ≤ 0.00000012681 := by
  have hl := lg_5
  refine (ecis_approx ((((7244:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.658768233906529996 11.65876824115053724 0.9076024 0.0000000268 0.615636897788 0.7880299550664 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p665_2 : ‖exp (-((((((7665:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5651244776859:ℝ):ℂ) + ((0.8250056513262:ℝ):ℂ) * I)‖ ≤ 0.00000013367 := by
  have hl := lg_2
  refine (ecis_approx ((((7665:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.3129731369995 5.312973140832 0.9702122 0.00000003366 0.5651244776859 0.8250056513262 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p665_3 : ‖exp (-((((((7665:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5370040225823):ℝ):ℂ) + (((-0.8435796819047):ℝ):ℂ) * I)‖ ≤ 0.00000011655 := by
  have hl := lg_3
  refine (ecis_approx ((((7665:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.42086319064857706 8.420863194481084725 (-2.1376779) 0.00000001654 (-0.5370040225823) (-0.8435796819047) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p665_4 : ‖exp (-((((((7665:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3612685561944):ℝ):ℂ) + ((0.9324618117128:ℝ):ℂ) * I)‖ ≤ 0.00000014038 := by
  have hl := lg_4
  refine (ecis_approx ((((7665:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.625946273999 10.625946281664 1.9404243 0.00000004037 (-0.3612685561944) 0.9324618117128 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p665_5 : ‖exp (-((((((7665:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9736597832478:ℝ):ℂ) + ((0.2280057597648:ℝ):ℂ) * I)‖ ≤ 0.00000011955 := by
  have hl := lg_5
  refine (ecis_approx ((((7665:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.336341594822411985 12.33634160248741965 0.230029 0.00000001954 0.9736597832478 0.2280057597648 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p086_2 : ‖exp (-((((((8086:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7785795489989:ℝ):ℂ) + ((0.6275459233241:ℝ):ℂ) * I)‖ ≤ 0.00000010729 := by
  have hl := lg_2
  refine (ecis_approx ((((8086:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.6047880999058 5.6047881039488 0.6783972 0.00000000728 0.7785795489989 0.6275459233241 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p086_3 : ‖exp (-((((((8086:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8569885898892):ℝ):ℂ) + (((-0.5153353827571):ℝ):ℂ) * I)‖ ≤ 0.00000014313 := by
  have hl := lg_3
  refine (ecis_approx ((((8086:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.883378964068414104 8.88337896811142219 (-2.6001937) 0.00000004312 (-0.8569885898892) (-0.5153353827571) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p086_4 : ‖exp (-((((((8086:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2123722282386:ℝ):ℂ) + ((0.9771888439155:ℝ):ℂ) * I)‖ ≤ 0.00000011456 := by
  have hl := lg_4
  refine (ecis_approx ((((8086:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.2095761998116 11.2095762078976 1.3567944 0.00000001455 0.2123722282386 0.9771888439155 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p086_5 : ‖exp (-((((((8086:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9015125310864:ℝ):ℂ) + (((-0.4327529968634):ℝ):ℂ) * I)‖ ≤ 0.00000014948 := by
  have hl := lg_5
  refine (ecis_approx ((((8086:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.013914955738293974 13.01391496382430206 (-0.4475443) 0.00000004947 0.9015125310864 (-0.4327529968634) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p507_2 : ‖exp (-((((((8507:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9262030632016:ℝ):ℂ) + ((0.3770250465367:ℝ):ℂ) * I)‖ ≤ 0.00000014438 := by
  have hl := lg_2
  refine (ecis_approx ((((8507:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.8966030628121 5.8966030670656 0.3865822 0.00000004437 0.9262030632016 0.3770250465367 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p507_3 : ‖exp (-((((((8507:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9968903289255):ℝ):ℂ) + (((-0.0788014694022):ℝ):ℂ) * I)‖ ≤ 0.00000013458 := by
  have hl := lg_3
  refine (ecis_approx ((((8507:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.345894737488251148 9.345894741741759655 (-3.0627094) 0.00000003457 (-0.9968903289255) (-0.0788014694022) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p507_4 : ‖exp (-((((((8507:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7157041587277:ℝ):ℂ) + ((0.6984035775824:ℝ):ℂ) * I)‖ ≤ 0.00000011979 := by
  have hl := lg_4
  refine (ecis_approx ((((8507:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.7932061256242 11.7932061341312 0.7731645 0.00000001978 0.7157041587277 0.6984035775824 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p507_5 : ‖exp (-((((((8507:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4310703169165:ℝ):ℂ) + (((-0.9023183373253):ℝ):ℂ) * I)‖ ≤ 0.00000011082 := by
  have hl := lg_5
  refine (ecis_approx ((((8507:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.691488316654175963 13.69148832516118447 (-1.1251177) 0.00000001081 0.4310703169165 (-0.9023183373253) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p928_2 : ‖exp (-((((((8928:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9955129390656:ℝ):ℂ) + ((0.0946255153377:ℝ):ℂ) * I)‖ ≤ 0.00000012302 := by
  have hl := lg_2
  refine (ecis_approx ((((8928:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.1884180257184 6.1884180301824 0.0947673 0.00000002301 0.9955129390656 0.0946255153377 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p928_3 : ‖exp (-((((((8928:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9273111229416):ℝ):ℂ) + ((0.3742914387399:ℝ):ℂ) * I)‖ ≤ 0.00000010347 := by
  have hl := lg_3
  refine (ecis_approx ((((8928:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.808410510908088192 9.80841051537209712 2.7579601 0.00000000346 (-0.9273111229416) 0.3742914387399 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p928_4 : ‖exp (-((((((8928:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9820920236942:ℝ):ℂ) + ((0.1884018497688:ℝ):ℂ) * I)‖ ≤ 0.00000014602 := by
  have hl := lg_4
  refine (ecis_approx ((((8928:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.3768360514368 12.3768360603648 0.1895346 0.00000004601 0.9820920236942 0.1884018497688 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p928_5 : ‖exp (-((((((8928:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.229821990189):ℝ):ℂ) + (((-0.9732326817491):ℝ):ℂ) * I)‖ ≤ 0.0000001368 := by
  have hl := lg_5
  refine (ecis_approx ((((8928:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.369061677570057952 14.36906168649806688 (-1.8026911) 0.00000003679 (-0.229821990189) (-0.9732326817491) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p349_2 : ‖exp (-((((((9349:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9806488372906:ℝ):ℂ) + (((-0.1957750186328):ℝ):ℂ) * I)‖ ≤ 0.00000011857 := by
  have hl := lg_2
  refine (ecis_approx ((((9349:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.4802329886247 6.4802329932992 (-0.1970477) 0.00000001856 0.9806488372906 (-0.1957750186328) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p349_3 : ‖exp (-((((((9349:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6628719097254):ℝ):ℂ) + ((0.7487328170173:ℝ):ℂ) * I)‖ ≤ 0.00000013005 := by
  have hl := lg_3
  refine (ecis_approx ((((9349:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.270926284327925236 10.270926289002434585 2.2954443 0.00000003004 (-0.6628719097254) 0.7487328170173 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p349_4 : ‖exp (-((((((9349:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9233442841587:ℝ):ℂ) + (((-0.3839730887855):ℝ):ℂ) * I)‖ ≤ 0.00000013712 := by
  have hl := lg_4
  refine (ecis_approx ((((9349:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.9604659772494 12.9604659865984 (-0.3940954) 0.00000003711 0.9233442841587 (-0.3839730887855) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p349_5 : ‖exp (-((((((9349:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7891771601935):ℝ):ℂ) + (((-0.6141656208089):ℝ):ℂ) * I)‖ ≤ 0.00000013349 := by
  have hl := lg_5
  refine (ecis_approx ((((9349:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.046635038485939941 15.04663504783494929 (-2.4802644) 0.00000003348 (-0.7891771601935) (-0.6141656208089) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p77_2 : ‖exp (-((((((9770:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8828675776523:ℝ):ℂ) + (((-0.4696220185748):ℝ):ℂ) * I)‖ ≤ 0.00000014925 := by
  have hl := lg_2
  refine (ecis_approx ((((9770:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.772047951531 6.772047956416 (-0.4888626) 0.00000004924 0.8828675776523 (-0.4696220185748) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p77_3 : ‖exp (-((((((9770:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2591405733673):ℝ):ℂ) + ((0.9658396156886:ℝ):ℂ) * I)‖ ≤ 0.00000014829 := by
  have hl := lg_3
  refine (ecis_approx ((((9770:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.73344205774776228 10.73344206263277205 1.8329286 0.00000004828 (-0.2591405733673) 0.9658396156886 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p77_4 : ‖exp (-((((((9770:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5589102364166:ℝ):ℂ) + (((-0.8292281637938):ℝ):ℂ) * I)‖ ≤ 0.00000011131 := by
  have hl := lg_4
  refine (ecis_approx ((((9770:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.544095903062 13.544095912832 (-0.9777253) 0.0000000113 0.5589102364166 (-0.8292281637938) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p77_5 : ‖exp (-((((((9770:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998680500748):ℝ):ℂ) + ((0.0162444387794:ℝ):ℂ) * I)‖ ≤ 0.00000012215 := by
  have hl := lg_5
  refine (ecis_approx ((((9770:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.72420839940182193 15.7242084091718317 3.1253475 0.00000002214 (-0.9998680500748) 0.0162444387794 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p191_2 : ‖exp (-((((((10191:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7104368327093:ℝ):ℂ) + (((-0.7037609727244):ℝ):ℂ) * I)‖ ≤ 0.00000011237 := by
  have hl := lg_2
  refine (ecis_approx ((((10191:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.0638629144373 7.0638629195328 (-0.7806776) 0.00000001236 0.7104368327093 (-0.7037609727244) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p191_3 : ‖exp (-((((((10191:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1990451979678:ℝ):ℂ) + ((0.979990310751:ℝ):ℂ) * I)‖ ≤ 0.00000012192 := by
  have hl := lg_3
  refine (ecis_approx ((((10191:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.195957831167599324 11.195957836263109515 1.3704128 0.00000002191 0.1990451979678 0.979990310751 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p191_4 : ‖exp (-((((((10191:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0094409865399:ℝ):ℂ) + (((-0.9999554328934):ℝ):ℂ) * I)‖ ≤ 0.00000012472 := by
  have hl := lg_4
  refine (ecis_approx ((((10191:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.1277258288746 14.1277258390656 (-1.5613552) 0.00000002471 0.0094409865399 (-0.9999554328934) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p191_5 : ‖exp (-((((((10191:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7688098106048):ℝ):ℂ) + ((0.6394775016206:ℝ):ℂ) * I)‖ ≤ 0.00000014898 := by
  have hl := lg_5
  refine (ecis_approx ((((10191:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.401781760317703919 16.40178177050871411 2.4477742 0.00000004897 (-0.7688098106048) 0.6394775016206 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p612_2 : ‖exp (-((((((10612:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4779362297974:ℝ):ℂ) + (((-0.8783945356427):ℝ):ℂ) * I)‖ ≤ 0.00000012985 := by
  have hl := lg_2
  refine (ecis_approx ((((10612:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.3556778773436 7.3556778826496 (-1.0724926) 0.00000002984 0.4779362297974 (-0.8783945356427) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p612_3 : ‖exp (-((((((10612:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6154047174513:ℝ):ℂ) + ((0.7882112874976:ℝ):ℂ) * I)‖ ≤ 0.00000010979 := by
  have hl := lg_3
  refine (ecis_approx ((((10612:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.658473604587436368 11.65847360989344698 0.907897 0.00000000978 0.6154047174513 0.7882112874976 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p612_4 : ‖exp (-((((((10612:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5431538365303):ℝ):ℂ) + (((-0.8396331995902):ℝ):ℂ) * I)‖ ≤ 0.00000015096 := by
  have hl := lg_4
  refine (ecis_approx ((((10612:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.7113557546872 14.7113557652992 (-2.1449851) 0.00000005095 (-0.5431538365303) (-0.8396331995902) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p612_5 : ‖exp (-((((((10612:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1980856396925):ℝ):ℂ) + ((0.9801847169522:ℝ):ℂ) * I)‖ ≤ 0.00000011032 := by
  have hl := lg_5
  refine (ecis_approx ((((10612:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.079355121233585908 17.07935513184559652 1.7702008 0.00000001031 (-0.1980856396925) 0.9801847169522 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p612_6 : ‖exp (-((((((10612:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9864846983281:ℝ):ℂ) + (((-0.1638534099876):ℝ):ℂ) * I)‖ ≤ 0.00000013962 := by
  have hl := lg_6
  refine (ecis_approx ((((10612:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.014151481931036368 19.01415149254304698 (-0.1645956) 0.00000003961 0.9864846983281 (-0.1638534099876) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p612_7 : ‖exp (-((((((10612:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2276330973867):ℝ):ℂ) + (((-0.973746975848):ℝ):ℂ) * I)‖ ≤ 0.0000001253 := by
  have hl := lg_7
  refine (ecis_approx ((((10612:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.649998496257898264 20.649998506869919488 (-1.8004426) 0.00000002529 (-0.2276330973867) (-0.973746975848) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p612_8 : ‖exp (-((((((10612:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9971221105129):ℝ):ℂ) + ((0.075812243112:ℝ):ℂ) * I)‖ ≤ 0.00000011925 := by
  have hl := lg_8
  refine (ecis_approx ((((10612:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.0670336320308 22.0670336479488 3.0657076 0.00000001924 (-0.9971221105129) 0.075812243112 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p612_9 : ‖exp (-((((((10612:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2425540674774):ℝ):ℂ) + ((0.9701378893482:ℝ):ℂ) * I)‖ ≤ 0.00000011956 := by
  have hl := lg_9
  refine (ecis_approx ((((10612:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.316947209174872736 23.31694721978689396 1.815794 0.00000001955 (-0.2425540674774) 0.9701378893482 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p612_10 : ‖exp (-((((((10612:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7663165954802:ℝ):ℂ) + ((0.6424631316206:ℝ):ℂ) * I)‖ ≤ 0.00000013016 := by
  have hl := lg_10
  refine (ecis_approx ((((10612:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.435032998577185908 24.43503301449519652 0.6977082 0.00000003015 0.7663165954802 0.6424631316206 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p033_2 : ‖exp (-((((((11033:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2050245859799:ℝ):ℂ) + (((-0.9787568232936):ℝ):ℂ) * I)‖ ≤ 0.0000001386 := by
  have hl := lg_2
  refine (ecis_approx ((((11033:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.6474928402499 7.6474928457664 (-1.3643075) 0.00000003859 0.2050245859799 (-0.9787568232936) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p033_3 : ‖exp (-((((((11033:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9024465092754:ℝ):ℂ) + ((0.4308019242026:ℝ):ℂ) * I)‖ ≤ 0.00000013637 := by
  have hl := lg_3
  refine (ecis_approx ((((11033:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.120989378007273412 12.120989383523784445 0.4453812 0.00000003636 0.9024465092754 0.4308019242026 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p033_4 : ‖exp (-((((((11033:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9159298783787):ℝ):ℂ) + (((-0.4013383332754):ℝ):ℂ) * I)‖ ≤ 0.00000013387 := by
  have hl := lg_4
  refine (ecis_approx ((((11033:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.2949856804998 15.2949856915328 (-2.7286151) 0.00000003386 (-0.9159298783787) (-0.4013383332754) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p033_5 : ‖exp (-((((((11033:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4601542496798:ℝ):ℂ) + ((0.887838986811:ℝ):ℂ) * I)‖ ≤ 0.0000001394 := by
  have hl := lg_5
  refine (ecis_approx ((((11033:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.756928482149467897 17.75692849318247893 1.0926274 0.00000003939 0.4601542496798 0.887838986811 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p033_6 : ‖exp (-((((((11033:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6066740447345:ℝ):ℂ) + (((-0.7949506924618):ℝ):ℂ) * I)‖ ≤ 0.00000010777 := by
  have hl := lg_6
  refine (ecis_approx ((((11033:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.768482218257173412 19.768482229290184445 (-0.9189263) 0.00000000776 0.6066740447345 (-0.7949506924618) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p033_7 : ‖exp (-((((((11033:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8668626467128):ℝ):ℂ) + (((-0.4985470405575):ℝ):ℂ) * I)‖ ≤ 0.00000015276 := by
  have hl := lg_7
  refine (ecis_approx ((((11033:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.469226668791310926 21.469226679824332992 (-2.6196708) 0.00000005275 (-0.8668626467128) (-0.4985470405575) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p033_8 : ‖exp (-((((((11033:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5806007704779):ℝ):ℂ) + ((0.8141883966932:ℝ):ℂ) * I)‖ ≤ 0.0000001086 := by
  have hl := lg_8
  refine (ecis_approx ((((11033:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.9424785207497 22.9424785372992 2.1902627 0.00000000859 (-0.5806007704779) 0.8141883966932 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p033_9 : ‖exp (-((((((11033:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6288193264516:ℝ):ℂ) + ((0.7775514482534:ℝ):ℂ) * I)‖ ≤ 0.00000013834 := by
  have hl := lg_9
  refine (ecis_approx ((((11033:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.241978756014546824 24.24197876704756889 0.8907625 0.00000003833 0.6288193264516 0.7775514482534 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p033_10 : ‖exp (-((((((11033:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9633214008549:ℝ):ℂ) + (((-0.2683502909539):ℝ):ℂ) * I)‖ ≤ 0.00000011025 := by
  have hl := lg_10
  refine (ecis_approx ((((11033:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.404421322399367897 25.40442133894887893 (-0.2716801) 0.00000001024 0.9633214008549 (-0.2683502909539) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p348_2 : ‖exp (-((((((11348:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.011852295692):ℝ):ℂ) + (((-0.9999297590764):ℝ):ℂ) * I)‖ ≤ 0.00000010515 := by
  have hl := lg_2
  refine (ecis_approx ((((11348:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.8658342020444 7.8658342077184 (-1.5826489) 0.00000000514 (-0.011852295692) (-0.9999297590764) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p348_3 : ‖exp (-((((((11348:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9950719806008:ℝ):ℂ) + ((0.0991551986701:ℝ):ℂ) * I)‖ ≤ 0.00000014019 := by
  have hl := lg_3
  refine (ecis_approx ((((11348:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.467052248855845072 12.46705225452985642 0.0993184 0.00000004018 0.9950719806008 0.0991551986701 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p348_4 : ‖exp (-((((((11348:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997190456947):ℝ):ℂ) + ((0.0237029332452:ℝ):ℂ) * I)‖ ≤ 0.00000011746 := by
  have hl := lg_4
  refine (ecis_approx ((((11348:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.7316684040888 15.7316684154368 3.1178875 0.00000001745 (-0.9997190456947) 0.0237029332452 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p348_5 : ‖exp (-((((((11348:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8333504928484:ℝ):ℂ) + ((0.5527449285786:ℝ):ℂ) * I)‖ ≤ 0.00000011423 := by
  have hl := lg_5
  refine (ecis_approx ((((11348:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.263901424402443732 18.26390143575045508 0.5856545 0.00000001422 0.8333504928484 0.5527449285786 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p348_6 : ‖exp (-((((((11348:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0873543465685:ℝ):ℂ) + (((-0.9961773025599):ℝ):ℂ) * I)‖ ≤ 0.00000014072 := by
  have hl := lg_6
  refine (ecis_approx ((((11348:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.332886450900245072 20.33288646224825642 (-1.4833305) 0.00000004071 0.0873543465685 (-0.9961773025599) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p348_7 : ‖exp (-((((((11348:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9958587429026):ℝ):ℂ) + ((0.0909140456271:ℝ):ℂ) * I)‖ ≤ 0.00000014822 := by
  have hl := lg_7
  refine (ecis_approx ((((11348:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.082188365579968856 22.082188376927991552 3.0505529 0.00000004821 (-0.9958587429026) 0.0909140456271 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p348_8 : ‖exp (-((((((11348:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0355502343551:ℝ):ℂ) + ((0.9993678906374:ℝ):ℂ) * I)‖ ≤ 0.0000001226 := by
  have hl := lg_8
  refine (ecis_approx ((((11348:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.5975026061332 23.5975026231552 1.5352386 0.00000002259 0.0355502343551 0.9993678906374 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p348_9 : ‖exp (-((((((11348:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9803365128867:ℝ):ℂ) + ((0.1973330218213:ℝ):ℂ) * I)‖ ≤ 0.00000013102 := by
  have hl := lg_9
  refine (ecis_approx ((((11348:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.934104497711690144 24.93410450905971284 0.1986367 0.00000003101 0.9803365128867 0.1973330218213 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p348_10 : ‖exp (-((((((11348:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5428289868081:ℝ):ℂ) + (((-0.8398432538759):ℝ):ℂ) * I)‖ ≤ 0.00000011477 := by
  have hl := lg_10
  refine (ecis_approx ((((11348:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.129735626446843732 26.12973564346885508 (-0.9969944) 0.00000001476 0.5428289868081 (-0.8398432538759) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p663_2 : ‖exp (-((((((11663:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2281663844366):ℝ):ℂ) + (((-0.9736221551568):ℝ):ℂ) * I)‖ ≤ 0.00000014336 := by
  have hl := lg_2
  refine (ecis_approx ((((11663:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.0841755638389 8.0841755696704 (-1.8009903) 0.00000004335 (-0.2281663844366) (-0.9736221551568) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p663_3 : ‖exp (-((((((11663:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9697127094792:ℝ):ℂ) + (((-0.2442483594102):ℝ):ℂ) * I)‖ ≤ 0.00000011119 := by
  have hl := lg_3
  refine (ecis_approx ((((11663:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.813115119704416732 12.813115125535928395 (-0.2467445) 0.00000001118 0.9697127094792 (-0.2442483594102) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p663_4 : ‖exp (-((((((11663:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8958802432337):ℝ):ℂ) + ((0.4442956106825:ℝ):ℂ) * I)‖ ≤ 0.00000011782 := by
  have hl := lg_4
  refine (ecis_approx ((((11663:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.1683511276778 16.1683511393408 2.6812048 0.00000001781 (-0.8958802432337) 0.4442956106825 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p663_5 : ‖exp (-((((((11663:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9969062073551:ℝ):ℂ) + ((0.0786003418367:ℝ):ℂ) * I)‖ ≤ 0.0000001549 := by
  have hl := lg_5
  refine (ecis_approx ((((11663:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.770874366655419567 18.77087437831843123 0.0786815 0.00000005489 0.9969062073551 0.0786003418367 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p663_6 : ‖exp (-((((((11663:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4590614569466):ℝ):ℂ) + (((-0.8884045130127):ℝ):ℂ) * I)‖ ≤ 0.00000013801 := by
  have hl := lg_6
  refine (ecis_approx ((((11663:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.897290683543316732 20.897290695206328395 (-2.0477348) 0.000000038 (-0.4590614569466) (-0.8884045130127) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p663_7 : ‖exp (-((((((11663:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7622582638027):ℝ):ℂ) + ((0.6472730020845:ℝ):ℂ) * I)‖ ≤ 0.00000014533 := by
  have hl := lg_7
  refine (ecis_approx ((((11663:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.695150062368626786 22.695150074031650112 2.4375912 0.00000004532 (-0.7622582638027) 0.6472730020845 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p663_8 : ‖exp (-((((((11663:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6369858060526:ℝ):ℂ) + ((0.7708755300874:ℝ):ℂ) * I)‖ ≤ 0.00000013722 := by
  have hl := lg_8
  refine (ecis_approx ((((11663:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.2525266915167 24.2525267090112 0.8802145 0.00000003721 0.6369858060526 0.7708755300874 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p663_9 : ‖exp (-((((((11663:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8806854778508:ℝ):ℂ) + (((-0.4737014767791):ℝ):ℂ) * I)‖ ≤ 0.00000012237 := by
  have hl := lg_9
  refine (ecis_approx ((((11663:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.626230239408833464 25.62623025107185679 (-0.493489) 0.00000002236 0.8806854778508 (-0.4737014767791) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p663_10 : ‖exp (-((((((11663:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.150933351885):ℝ):ℂ) + (((-0.9885439410002):ℝ):ℂ) * I)‖ ≤ 0.00000011929 := by
  have hl := lg_10
  refine (ecis_approx ((((11663:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.855049930494319567 26.85504994798883123 (-1.7223087) 0.00000001928 (-0.150933351885) (-0.9885439410002) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p899_2 : ‖exp (-((((((11899:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.383678774723):ℝ):ℂ) + (((-0.9234666197671):ℝ):ℂ) * I)‖ ≤ 0.0000001088 := by
  have hl := lg_2
  refine (ecis_approx ((((11899:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.2477582983897 8.2477583043392 (-1.964573) 0.00000000879 (-0.383678774723) (-0.9234666197671) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p899_3 : ‖exp (-((((((11899:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8746819897526:ℝ):ℂ) + (((-0.4846972424127):ℝ):ℂ) * I)‖ ≤ 0.00000011137 := by
  have hl := lg_3
  refine (ecis_approx ((((11899:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.072387619768743436 13.072387625718255335 (-0.506017) 0.00000001136 0.8746819897526 (-0.4846972424127) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p899_4 : ‖exp (-((((((11899:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7055811905631):ℝ):ℂ) + ((0.7086290873926:ℝ):ℂ) * I)‖ ≤ 0.00000012477 := by
  have hl := lg_4
  refine (ecis_approx ((((11899:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.4955165967794 16.4955166086784 2.3540393 0.00000002476 (-0.7055811905631) 0.7086290873926 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p899_5 : ‖exp (-((((((11899:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9549972550366:ℝ):ℂ) + (((-0.2966146369831):ℝ):ℂ) * I)‖ ≤ 0.00000010769 := by
  have hl := lg_5
  refine (ecis_approx ((((11899:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.150701713867172891 19.15070172576618479 (-0.3011458) 0.00000000768 0.9549972550366 (-0.2966146369831) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p899_6 : ‖exp (-((((((11899:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7831986381542):ℝ):ℂ) + (((-0.6217715763446):ℝ):ℂ) * I)‖ ≤ 0.00000010853 := by
  have hl := lg_6
  refine (ecis_approx ((((11899:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.320145918158443436 21.320145930057455335 (-2.47059) 0.00000000852 (-0.7831986381542) (-0.6217715763446) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p899_7 : ‖exp (-((((((11899:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3963704360266):ℝ):ℂ) + ((0.9180906695098:ℝ):ℂ) * I)‖ ≤ 0.00000014062 := by
  have hl := lg_7
  refine (ecis_approx ((((11899:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.154384857422986378 23.154384869322010176 1.9783564 0.00000004061 (-0.3963704360266) 0.9180906695098 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p899_8 : ‖exp (-((((((11899:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9251118346813:ℝ):ℂ) + ((0.3796947370357:ℝ):ℂ) * I)‖ ≤ 0.00000013356 := by
  have hl := lg_8
  refine (ecis_approx ((((11899:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.7432748951691 24.7432749130176 0.3894663 0.00000003355 0.9251118346813 0.3796947370357 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p899_9 : ‖exp (-((((((11899:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5301371663951:ℝ):ℂ) + (((-0.8479118968422):ℝ):ℂ) * I)‖ ≤ 0.00000012273 := by
  have hl := lg_9
  refine (ecis_approx ((((11899:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.144775239537486872 26.14477525143651067 (-1.012034) 0.00000002272 0.5301371663951 (-0.8479118968422) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p899_10 : ‖exp (-((((((11899:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6403258928634):ℝ):ℂ) + (((-0.7681033465055):ℝ):ℂ) * I)‖ ≤ 0.00000011648 := by
  have hl := lg_10
  refine (ecis_approx ((((11899:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.398460012256872891 27.39846003010538479 (-2.2657188) 0.00000001647 (-0.6403258928634) (-0.7681033465055) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p135_2 : ‖exp (-((((((12135:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5289470640167):ℝ):ℂ) + (((-0.8486548199713):ℝ):ℂ) * I)‖ ≤ 0.00000013184 := by
  have hl := lg_2
  refine (ecis_approx ((((12135:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.4113410329405 8.411341039008 (-2.1281557) 0.00000003183 (-0.5289470640167) (-0.8486548199713) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p135_3 : ‖exp (-((((((12135:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7211818377487:ℝ):ℂ) + (((-0.6927458097321):ℝ):ℂ) * I)‖ ≤ 0.00000011156 := by
  have hl := lg_3
  refine (ecis_approx ((((12135:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.33166011983307014 13.331660125900582275 (-0.7652895) 0.00000001155 0.7211818377487 (-0.6927458097321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p135_4 : ‖exp (-((((((12135:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4404299107111):ℝ):ℂ) + ((0.8977869979827:ℝ):ℂ) * I)‖ ≤ 0.00000015567 := by
  have hl := lg_4
  refine (ecis_approx ((((12135:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.822682065881 16.822682078016 2.0268738 0.00000005566 (-0.4404299107111) 0.8977869979827 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p135_5 : ‖exp (-((((((12135:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7769604722049:ℝ):ℂ) + (((-0.6295493822022):ℝ):ℂ) * I)‖ ≤ 0.00000015169 := by
  have hl := lg_5
  refine (ecis_approx ((((12135:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.530529061078926215 19.53052907321393835 (-0.6809731) 0.00000005168 0.7769604722049 (-0.6295493822022) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p135_6 : ‖exp (-((((((12135:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9693690860424):ℝ):ℂ) + (((-0.2456085803806):ℝ):ℂ) * I)‖ ≤ 0.00000014338 := by
  have hl := lg_6
  refine (ecis_approx ((((12135:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.74300115277357014 21.743001164908582275 (-2.8934452) 0.00000004337 (-0.9693690860424) (-0.2456085803806) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p135_7 : ‖exp (-((((((12135:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0516517322227:ℝ):ℂ) + ((0.998665158378:ℝ):ℂ) * I)‖ ≤ 0.00000013591 := by
  have hl := lg_7
  refine (ecis_approx ((((12135:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.61361965247734597 23.61361966461237024 1.5191216 0.0000000359 0.0516517322227 0.998665158378 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p135_8 : ‖exp (-((((((12135:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9948753713273:ℝ):ℂ) + (((-0.1011088301105):ℝ):ℂ) * I)‖ ≤ 0.00000012991 := by
  have hl := lg_8
  refine (ecis_approx ((((12135:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.2340230988215 25.234023117024 (-0.1012819) 0.0000000299 0.9948753713273 (-0.1011088301105) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p135_9 : ‖exp (-((((((12135:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0402064861972:ℝ):ℂ) + (((-0.9991913923106):ℝ):ℂ) * I)‖ ≤ 0.0000001231 := by
  have hl := lg_9
  refine (ecis_approx ((((12135:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.66332023966614028 26.66332025180116455 (-1.530579) 0.00000002309 0.0402064861972 (-0.9991913923106) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p135_10 : ‖exp (-((((((12135:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9452411108191):ℝ):ℂ) + (((-0.3263728576737):ℝ):ℂ) * I)‖ ≤ 0.00000013471 := by
  have hl := lg_10
  refine (ecis_approx ((((12135:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.941870094019426215 27.94187011222193835 (-2.8091289) 0.0000000347 (-0.9452411108191) (-0.3263728576737) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p312_2 : ‖exp (-((((((12312:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6288291596345):ℝ):ℂ) + (((-0.7775434958758):ℝ):ℂ) * I)‖ ≤ 0.00000012334 := by
  have hl := lg_2
  refine (ecis_approx ((((12312:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.5340280838536 8.5340280900096 (-2.2508428) 0.00000002333 (-0.6288291596345) (-0.7775434958758) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p312_3 : ‖exp (-((((((12312:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.573729762223:ℝ):ℂ) + (((-0.8190446629699):ℝ):ℂ) * I)‖ ≤ 0.00000011949 := by
  have hl := lg_3
  refine (ecis_approx ((((12312:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.526114494881315168 13.52611450103732748 (-0.9597439) 0.00000001948 0.573729762223 (-0.8190446629699) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p312_4 : ‖exp (-((((((12312:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2091477689626):ℝ):ℂ) + ((0.9778840476954:ℝ):ℂ) * I)‖ ≤ 0.00000015385 := by
  have hl := lg_4
  refine (ecis_approx ((((12312:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.0680561677072 17.0680561800192 1.7814997 0.00000005384 (-0.2091477689626) 0.9778840476954 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p312_5 : ‖exp (-((((((12312:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5687231110601:ℝ):ℂ) + (((-0.8225290407919):ℝ):ℂ) * I)‖ ≤ 0.00000015007 := by
  have hl := lg_5
  refine (ecis_approx ((((12312:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.815399571487741208 19.81539958379975352 (-0.9658437) 0.00000005006 0.5687231110601 (-0.8225290407919) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p312_6 : ‖exp (-((((((12312:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.997620854022):ℝ):ℂ) + ((0.0689393290235:ℝ):ℂ) * I)‖ ≤ 0.00000015 := by
  have hl := lg_6
  refine (ecis_approx ((((12312:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.060142578734915168 22.06014259104692748 3.0725986 0.00000004999 (-0.997620854022) 0.0689393290235 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p312_7 : ‖exp (-((((((12312:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3858240147936:ℝ):ℂ) + ((0.9225723980309:ℝ):ℂ) * I)‖ ≤ 0.00000013238 := by
  have hl := lg_7
  refine (ecis_approx ((((12312:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.958045748768115664 23.958045761080140288 1.1746955 0.00000003237 0.3858240147936 0.9225723980309 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p312_8 : ‖exp (-((((((12312:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8918656420411:ℝ):ℂ) + (((-0.4523004273119):ℝ):ℂ) * I)‖ ≤ 0.00000014133 := by
  have hl := lg_8
  refine (ecis_approx ((((12312:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.6020842515608 25.6020842700288 (-0.469343) 0.00000004132 0.8918656420411 (-0.4523004273119) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p312_9 : ‖exp (-((((((12312:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3416683198792):ℝ):ℂ) + (((-0.9398205994703):ℝ):ℂ) * I)‖ ≤ 0.00000013897 := by
  have hl := lg_9
  refine (ecis_approx ((((12312:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.052228989762630336 27.05222900207465496 (-1.9194878) 0.00000003896 (-0.3416683198792) (-0.9398205994703) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p312_10 : ‖exp (-((((((12312:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9971817885571):ℝ):ℂ) + ((0.0750231967324:ℝ):ℂ) * I)‖ ≤ 0.00000013793 := by
  have hl := lg_10
  refine (ecis_approx ((((12312:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.349427655341341208 28.34942767380935352 3.0664989 0.00000003792 (-0.9971817885571) 0.0750231967324 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p489_2 : ‖exp (-((((((12489:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7192578376496):ℝ):ℂ) + (((-0.6947432352693):ℝ):ℂ) * I)‖ ≤ 0.00000013385 := by
  have hl := lg_2
  refine (ecis_approx ((((12489:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.6567151347667 8.6567151410112 (-2.3735298) 0.00000003384 (-0.7192578376496) (-0.6947432352693) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p489_3 : ‖exp (-((((((12489:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4046517953529:ℝ):ℂ) + (((-0.9144708439954):ℝ):ℂ) * I)‖ ≤ 0.00000014444 := by
  have hl := lg_3
  refine (ecis_approx ((((12489:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.720568869929560196 13.720568876174072685 (-1.1541983) 0.00000004443 0.4046517953529 (-0.9144708439954) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p489_4 : ‖exp (-((((((12489:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0346637811674:ℝ):ℂ) + ((0.9993990305554:ℝ):ℂ) * I)‖ ≤ 0.00000015202 := by
  have hl := lg_4
  refine (ecis_approx ((((12489:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.3134302695334 17.3134302820224 1.5361256 0.00000005201 0.0346637811674 0.9993990305554 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p489_5 : ‖exp (-((((((12489:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3146445172177:ℝ):ℂ) + (((-0.9492095805379):ℝ):ℂ) * I)‖ ≤ 0.00000013966 := by
  have hl := lg_5
  refine (ecis_approx ((((12489:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.100270081896556201 20.10027009438556869 (-1.2507142) 0.00000003965 0.3146445172177 (-0.9492095805379) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p489_6 : ‖exp (-((((((12489:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9263714053055):ℝ):ℂ) + ((0.3766112309518:ℝ):ℂ) * I)‖ ≤ 0.00000012404 := by
  have hl := lg_6
  refine (ecis_approx ((((12489:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.377284004696260196 22.377284017185272685 2.7554572 0.00000002403 (-0.9263714053055) 0.3766112309518 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p489_7 : ‖exp (-((((((12489:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6746769368723:ℝ):ℂ) + ((0.7381131558593:ℝ):ℂ) * I)‖ ≤ 0.00000012884 := by
  have hl := lg_7
  refine (ecis_approx ((((12489:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.302471845058885358 24.302471857547910336 0.8302694 0.00000002883 0.6746769368723 0.7381131558593 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p489_8 : ‖exp (-((((((12489:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6693935195411:ℝ):ℂ) + (((-0.7429080131459):ℝ):ℂ) * I)‖ ≤ 0.00000012443 := by
  have hl := lg_8
  refine (ecis_approx ((((12489:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.9701454043001 25.9701454230336 (-0.8374042) 0.00000002442 0.6693935195411 (-0.7429080131459) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p489_9 : ‖exp (-((((((12489:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6725137750245):ℝ):ℂ) + (((-0.7400846048816):ℝ):ℂ) * I)‖ ≤ 0.00000012364 := by
  have hl := lg_9
  refine (ecis_approx ((((12489:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.441137739859120392 27.44113775234814537 (-2.3083965) 0.00000002363 (-0.6725137750245) (-0.7400846048816) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p489_10 : ‖exp (-((((((12489:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.885767466669):ℝ):ℂ) + ((0.4641292868256:ℝ):ℂ) * I)‖ ≤ 0.00000011925 := by
  have hl := lg_10
  refine (ecis_approx ((((12489:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.756985216663256201 28.75698523539676869 2.6589413 0.00000001924 (-0.885767466669) 0.4641292868256 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_2 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7988738080541):ℝ):ℂ) + (((-0.6014986606438):ℝ):ℂ) * I)‖ ≤ 0.00000012151 := by
  have hl := lg_2
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.7794021856798 8.7794021920128 (-2.4962169) 0.0000000215 (-0.7988738080541) (-0.6014986606438) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_3 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2203211775457:ℝ):ℂ) + (((-0.9754273825995):ℝ):ℂ) * I)‖ ≤ 0.00000013697 := by
  have hl := lg_3
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.915023244977805224 13.91502325131081789 (-1.3486526) 0.00000003696 0.2203211775457 (-0.9754273825995) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_4 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2763987293215:ℝ):ℂ) + ((0.9610430492072:ℝ):ℂ) * I)‖ ≤ 0.00000015019 := by
  have hl := lg_4
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.5588043713596 17.5588043840256 1.2907515 0.00000005018 0.2763987293215 0.9610430492072 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_5 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0352043510058:ℝ):ℂ) + (((-0.9993801347186):ℝ):ℂ) * I)‖ ≤ 0.00000012925 := by
  have hl := lg_5
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.385140592305371194 20.38514060497138386 (-1.5355847) 0.00000002924 0.0352043510058 (-0.9993801347186) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_6 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7627270776689):ℝ):ℂ) + ((0.6467204998711:ℝ):ℂ) * I)‖ ≤ 0.00000011462 := by
  have hl := lg_6
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.694425430657605224 22.69442544332361789 2.4383158 0.00000001461 (-0.7627270776689) 0.6467204998711 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_7 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8842814810752:ℝ):ℂ) + ((0.4669542399717:ℝ):ℂ) * I)‖ ≤ 0.00000012531 := by
  have hl := lg_7
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.646897941349655052 24.646897954015680384 0.4858433 0.0000000253 0.8842814810752 0.4669542399717 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_8 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3572584949089:ℝ):ℂ) + (((-0.9340055502059):ℝ):ℂ) * I)‖ ≤ 0.00000014734 := by
  have hl := lg_8
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.3382065570394 26.3382065760384 (-1.2054653) 0.00000004733 0.3572584949089 (-0.9340055502059) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_9 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9029172003956):ℝ):ℂ) + (((-0.4298145287331):ℝ):ℂ) * I)‖ ≤ 0.00000013878 := by
  have hl := lg_9
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.830046489955610448 27.83004650262163578 (-2.6973053) 0.00000003877 (-0.9029172003956) (-0.4298145287331) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_10 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6292496409018):ℝ):ℂ) + ((0.7772032484559:ℝ):ℂ) * I)‖ ≤ 0.00000015793 := by
  have hl := lg_10
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.164542777985171194 29.16454279698418386 2.2513837 0.00000005792 (-0.6292496409018) 0.7772032484559 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_11 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5026066730558:ℝ):ℂ) + ((0.864515200676:ℝ):ℂ) * I)‖ ≤ 0.00000012053 := by
  have hl := lg_11
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.371741515386738978 30.37174153438576431 1.044185 0.00000002052 0.5026066730558 0.864515200676 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_12 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9983241995699:ℝ):ℂ) + (((-0.0578687528224):ℝ):ℂ) * I)‖ ≤ 0.00000011958 := by
  have hl := lg_12
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.473827616337405224 31.47382763533641789 (-0.0579011) 0.00000001957 0.9983241995699 (-0.0578687528224) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_13 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4786129786545:ℝ):ℂ) + (((-0.8780259772145):ℝ):ℂ) * I)‖ ≤ 0.00000013485 := by
  have hl := lg_13
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.4876485517304122 32.487648570729437532 (-1.071722) 0.00000003484 0.4786129786545 (-0.8780259772145) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_14 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4255569642494):ℝ):ℂ) + (((-0.9049316383987):ℝ):ℂ) * I)‖ ≤ 0.00000011015 := by
  have hl := lg_14
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.426300127029455052 33.426300146028480384 (-2.0103736) 0.00000001014 (-0.4255569642494) (-0.9049316383987) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p666_15 : ‖exp (-((((((12666:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9670664848628):ℝ):ℂ) + (((-0.2545238959234):ℝ):ℂ) * I)‖ ≤ 0.0000001204 := by
  have hl := lg_15
  refine (ecis_approx ((((12666:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.300163837283176418 34.30016385628220175 (-2.8842373) 0.00000002039 (-0.9670664848628) (-0.2545238959234) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_2 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8664800561085):ℝ):ℂ) + (((-0.4992116908497):ℝ):ℂ) * I)‖ ≤ 0.00000013585 := by
  have hl := lg_2
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.9020892365929 8.9020892430144 (-2.6189039) 0.00000003584 (-0.8664800561085) (-0.4992116908497) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_3 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0276857887015:ℝ):ℂ) + (((-0.9996166750829):ℝ):ℂ) * I)‖ ≤ 0.0000001121 := by
  have hl := lg_3
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.109477620026050252 14.109477626447563095 (-1.543107) 0.00000001209 0.0276857887015 (-0.9996166750829) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_4 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5015754680673:ℝ):ℂ) + ((0.8651138941394:ℝ):ℂ) * I)‖ ≤ 0.00000014837 := by
  have hl := lg_4
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.8041784731858 17.8041784860288 1.0453774 0.00000004836 0.5015754680673 0.8651138941394 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_5 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2470734228772):ℝ):ℂ) + (((-0.9689967614531):ℝ):ℂ) * I)‖ ≤ 0.00000011884 := by
  have hl := lg_5
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.670011102714186187 20.67001111555719903 (-1.8204552) 0.00000001883 (-0.2470734228772) (-0.9689967614531) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_6 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5230095082449):ℝ):ℂ) + ((0.8523268470945:ℝ):ℂ) * I)‖ ≤ 0.00000014076 := by
  have hl := lg_6
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.011566856618950252 23.011566869461963095 2.1211744 0.00000004075 (-0.5230095082449) 0.8523268470945 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_7 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9900172413744:ℝ):ℂ) + ((0.1409463081512:ℝ):ℂ) * I)‖ ≤ 0.00000012178 := by
  have hl := lg_7
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.991324037640424746 24.991324050483450432 0.1414172 0.00000002177 0.9900172413744 0.1409463081512 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_8 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0027301698134):ℝ):ℂ) + (((-0.9999962730793):ℝ):ℂ) * I)‖ ≤ 0.00000011895 := by
  have hl := lg_8
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.7062677097787 26.7062677290432 (-1.5735265) 0.00000001894 (-0.0027301698134) (-0.9999962730793) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_9 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9984669939409):ℝ):ℂ) + (((-0.05535035184):ℝ):ℂ) * I)‖ ≤ 0.00000012419 := by
  have hl := lg_9
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.218955240052100504 28.21895525289512619 (-3.086214) 0.00000002418 (-0.9984669939409) (-0.05535035184) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_10 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.269650311522):ℝ):ℂ) + ((0.9629583114002:ℝ):ℂ) * I)‖ ≤ 0.00000012269 := by
  have hl := lg_10
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.572100339307086187 29.57210035857159903 1.8438262 0.00000002268 (-0.269650311522) 0.9629583114002 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_11 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.814019333757:ℝ):ℂ) + ((0.5808377779292:ℝ):ℂ) * I)‖ ≤ 0.00000015738 := by
  have hl := lg_11
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.796168978534019319 30.796168997798545005 0.6197575 0.00000005737 0.814019333757 0.5808377779292 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_12 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8786687868545:ℝ):ℂ) + (((-0.4774318412167):ℝ):ℂ) * I)‖ ≤ 0.0000001427 := by
  have hl := lg_12
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.913656093211850252 31.913656112476363095 (-0.4977296) 0.00000004269 0.8786687868545 (-0.4774318412167) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_13 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0450629615035:ℝ):ℂ) + (((-0.9989841487733):ℝ):ℂ) * I)‖ ≤ 0.00000014805 := by
  have hl := lg_13
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.9416445878630731 32.941644607127598786 (-1.5257181) 0.00000004804 0.0450629615035 (-0.9989841487733) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_14 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.78746815005):ℝ):ℂ) + (((-0.6163553460563):ℝ):ℂ) * I)‖ ≤ 0.00000015761 := by
  have hl := lg_14
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.893413274233324746 33.893413293497850432 (-2.4774867) 0.0000000576 (-0.78746815005) (-0.6163553460563) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p843_15 : ‖exp (-((((((12843:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9754657417303):ℝ):ℂ) + ((0.2201512807423:ℝ):ℂ) * I)‖ ≤ 0.00000012035 := by
  have hl := lg_15
  refine (ecis_approx ((((12843:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.779488722740236439 34.779488742004762125 2.9196231 0.00000002034 (-0.9754657417303) 0.2201512807423 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_2 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9210603500175):ℝ):ℂ) + (((-0.3894198652882):ℝ):ℂ) * I)‖ ≤ 0.00000011969 := by
  have hl := lg_2
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.024776287506 9.024776294016 (-2.741591) 0.00000001968 (-0.9210603500175) (-0.3894198652882) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_3 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1659931748319):ℝ):ℂ) + (((-0.9861269015236):ℝ):ℂ) * I)‖ ≤ 0.0000001193 := by
  have hl := lg_3
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.30393199507429528 14.3039320015843083 (-1.7375614) 0.00000001929 (-0.1659931748319) (-0.9861269015236) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_4 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6967043420683:ℝ):ℂ) + ((0.7173583900278:ℝ):ℂ) * I)‖ ≤ 0.00000014654 := by
  have hl := lg_4
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.049552575012 18.049552588032 0.8000033 0.00000004653 0.6967043420683 0.7173583900278 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_5 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5094361175135):ℝ):ℂ) + (((-0.8605084788462):ℝ):ℂ) * I)‖ ≤ 0.00000010843 := by
  have hl := lg_5
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.95488161312300118 20.9548816261430142 (-2.1053257) 0.00000000842 (-0.5094361175135) (-0.8605084788462) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_6 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2311276665206):ℝ):ℂ) + ((0.972923430578:ℝ):ℂ) * I)‖ ≤ 0.00000014615 := by
  have hl := lg_6
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.32870828258029528 23.3287082956003083 1.8040329 0.00000004614 (-0.2311276665206) 0.972923430578 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_7 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.979464366091:ℝ):ℂ) + (((-0.2016173493478):ℝ):ℂ) * I)‖ ≤ 0.00000011825 := by
  have hl := lg_7
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.33575013393119444 25.33575014695122048 (-0.2030089) 0.00000001824 0.979464366091 (-0.2016173493478) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_8 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3623530443289):ℝ):ℂ) + (((-0.9320409171614):ℝ):ℂ) * I)‖ ≤ 0.00000015334 := by
  have hl := lg_8
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.074328862518 27.074328882048 (-1.9415876) 0.00000005333 (-0.3623530443289) (-0.9320409171614) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_9 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9448925294016):ℝ):ℂ) + ((0.3273806770267:ℝ):ℂ) * I)‖ ≤ 0.00000014576 := by
  have hl := lg_9
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.60786399014859056 28.6078640031686166 2.8080625 0.00000004575 (-0.9448925294016) 0.3273806770267 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_10 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1341223198675:ℝ):ℂ) + ((0.9909647840934:ℝ):ℂ) * I)‖ ≤ 0.00000013528 := by
  have hl := lg_10
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.97965790062900118 29.9796579201590142 1.4362686 0.00000003527 0.1341223198675 0.9909647840934 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_11 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9809836537671:ℝ):ℂ) + ((0.1940903682353:ℝ):ℂ) * I)‖ ≤ 0.00000012533 := by
  have hl := lg_11
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.22059644168129966 31.2205964612113257 0.1953301 0.00000002532 0.9809836537671 0.1940903682353 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_12 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5917583213928:ℝ):ℂ) + (((-0.8061154315992):ℝ):ℂ) * I)‖ ≤ 0.00000015373 := by
  have hl := lg_12
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.35348457008629528 32.3534845896163083 (-0.937558) 0.00000005372 0.5917583213928 (-0.8061154315992) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_13 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3976165620211):ℝ):ℂ) + (((-0.9175516713533):ℝ):ℂ) * I)‖ ≤ 0.00000011192 := by
  have hl := lg_13
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.395640623995734 33.39564064352576004 (-1.9797141) 0.00000001191 (-0.3976165620211) (-0.9175516713533) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_14 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9806595928096):ℝ):ℂ) + (((-0.1957211350416):ℝ):ℂ) * I)‖ ≤ 0.00000011448 := by
  have hl := lg_14
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.36052642143719444 34.36052644096722048 (-2.9445999) 0.00000001447 (-0.9806595928096) (-0.1957211350416) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p02_15 : ‖exp (-((((((13020:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7640076368243):ℝ):ℂ) + ((0.6452071999263:ℝ):ℂ) * I)‖ ≤ 0.0000001349 := by
  have hl := lg_15
  refine (ecis_approx ((((13020:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.25881360819729646 35.2588136277273225 2.4402982 0.00000003489 (-0.7640076368243) 0.6452071999263 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_2 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9527881874229):ℝ):ℂ) + (((-0.3036357516768):ℝ):ℂ) * I)‖ ≤ 0.00000011472 := by
  have hl := lg_2
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.1162717153056 9.1162717218816 (-2.8330864) 0.00000001471 (-0.9527881874229) (-0.3036357516768) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_3 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3067550889246):ℝ):ℂ) + (((-0.9517884824986):ℝ):ℂ) * I)‖ ≤ 0.00000010938 := by
  have hl := lg_3
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.448948817144172928 14.44894882372018608 (-1.8825782) 0.00000000937 (-0.3067550889246) (-0.9517884824986) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_4 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.815610664629:ℝ):ℂ) + ((0.578601109352:ℝ):ℂ) * I)‖ ≤ 0.00000012224 := by
  have hl := lg_4
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.2325434306112 18.2325434437632 0.6170125 0.00000002223 0.815610664629 0.578601109352 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_5 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6794224129489):ℝ):ℂ) + (((-0.7337473575844):ℝ):ℂ) * I)‖ ≤ 0.00000010912 := by
  have hl := lg_5
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.167327417495676768 21.16732743064768992 (-2.3177715) 0.00000000911 (-0.6794224129489) (-0.7337473575844) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_6 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0032756209371:ℝ):ℂ) + ((0.9999946351392:ℝ):ℂ) * I)‖ ≤ 0.0000001169 := by
  have hl := lg_6
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.565220532449772928 23.56522054560178608 1.5675207 0.00000001689 0.0032756209371 0.9999946351392 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_7 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8961106026557:ℝ):ℂ) + (((-0.4438308098904):ℝ):ℂ) * I)‖ ≤ 0.0000001552 := by
  have hl := lg_7
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.592610273537870144 25.592610286689896448 (-0.4598691) 0.00000005519 0.8961106026557 (-0.4438308098904) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_8 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6014202240335):ℝ):ℂ) + (((-0.7989328595766):ℝ):ℂ) * I)‖ ≤ 0.00000013694 := by
  have hl := lg_8
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.3488151459168 27.3488151656448 (-2.2160739) 0.00000003693 (-0.6014202240335) (-0.7989328595766) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_9 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8118026266339):ℝ):ℂ) + ((0.5839319269712:ℝ):ℂ) * I)‖ ≤ 0.00000011156 := by
  have hl := lg_9
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.897897634288345856 28.89789764744037216 2.5180289 0.00000001155 (-0.8118026266339) 0.5839319269712 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_10 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.424553725338:ℝ):ℂ) + ((0.9054027470146:ℝ):ℂ) * I)‖ ≤ 0.00000011665 := by
  have hl := lg_10
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.283599132801276768 30.28359915252928992 1.1323274 0.00000001664 0.424553725338 0.9054027470146 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_11 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9926652215241:ℝ):ℂ) + (((-0.1208956491218):ℝ):ℂ) * I)‖ ≤ 0.00000011833 := by
  have hl := lg_11
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.537118617587746016 31.53711863731577232 (-0.1211921) 0.00000001832 0.9926652215241 (-0.1208956491218) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_12 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3005131498867:ℝ):ℂ) + (((-0.9537776715489):ℝ):ℂ) * I)‖ ≤ 0.0000001316 := by
  have hl := lg_12
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.681492247755372928 32.68149226748338608 (-1.2655657) 0.00000003159 0.3005131498867 (-0.9537776715489) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_13 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6798008627788):ℝ):ℂ) + (((-0.7333967459326):ℝ):ℂ) * I)‖ ≤ 0.00000012292 := by
  have hl := lg_13
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.7342139390777184 33.734213958805744704 (-2.3182874) 0.00000002291 (-0.6798008627788) (-0.7333967459326) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_14 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9885664972779):ℝ):ℂ) + ((0.1507855432992:ℝ):ℂ) * I)‖ ≤ 0.00000015425 := by
  have hl := lg_14
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.708881988843470144 34.708882008571496448 2.9902298 0.00000005424 (-0.9885664972779) 0.1507855432992 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p152_15 : ‖exp (-((((((13152:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4899559950634):ℝ):ℂ) + ((0.8717471668411:ℝ):ℂ) * I)‖ ≤ 0.00000011131 := by
  have hl := lg_15
  refine (ecis_approx ((((13152:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.616276234639849696 35.616276254367876 2.0828356 0.0000000113 (-0.4899559950634) 0.8717471668411 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_2 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9765454087146):ℝ):ℂ) + (((-0.2153115519763):ℝ):ℂ) * I)‖ ≤ 0.00000014258 := by
  have hl := lg_2
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.2077671431052 9.2077671497472 (-2.9245818) 0.00000004257 (-0.9765454087146) (-0.2153115519763) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_3 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4410772800977):ℝ):ℂ) + (((-0.8974691264759):ℝ):ℂ) * I)‖ ≤ 0.00000013151 := by
  have hl := lg_3
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.593965639214050576 14.59396564585606386 (-2.027595) 0.0000000315 (-0.4410772800977) (-0.8974691264759) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_4 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9072819161121:ℝ):ℂ) + ((0.4205229181578:ℝ):ℂ) * I)‖ ≤ 0.00000013534 := by
  have hl := lg_4
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.4155342862104 18.4155342994944 0.4340216 0.00000003533 0.9072819161121 0.4205229181578 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_5 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8188593475416):ℝ):ℂ) + (((-0.5739942237397):ℝ):ℂ) * I)‖ ≤ 0.00000011363 := by
  have hl := lg_5
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.379773221868352356 21.37977323515236564 (-2.5302173) 0.00000001362 (-0.8188593475416) (-0.5739942237397) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_6 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2374966263258:ℝ):ℂ) + ((0.9713883633665:ℝ):ℂ) * I)‖ ≤ 0.00000014641 := by
  have hl := lg_6
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.801732782319250576 23.80173279560326386 1.3310084 0.0000000464 0.2374966263258 0.9713883633665 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_7 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7539584192254:ℝ):ℂ) + (((-0.6569221430879):ℝ):ℂ) * I)‖ ≤ 0.00000011559 := by
  have hl := lg_7
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.849470413144545848 25.849470426428572416 (-0.7167292) 0.00000001558 0.7539584192254 (-0.6569221430879) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_8 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7954585474765):ℝ):ℂ) + (((-0.6060080025866):ℝ):ℂ) * I)‖ ≤ 0.00000012054 := by
  have hl := lg_8
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.6233014293156 27.6233014492416 (-2.4905602) 0.00000002053 (-0.7954585474765) (-0.6060080025866) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_9 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6109016602781):ℝ):ℂ) + ((0.7917064869359:ℝ):ℂ) * I)‖ ≤ 0.00000015583 := by
  have hl := lg_9
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.187931278428101152 29.18793129171212772 2.2279953 0.00000005582 (-0.6109016602781) 0.7917064869359 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_10 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6760657543948:ℝ):ℂ) + ((0.7368412961654:ℝ):ℂ) * I)‖ ≤ 0.00000014902 := by
  have hl := lg_10
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.587540364973552356 30.58754038489956564 0.8283862 0.00000004901 0.6760657543948 0.7368412961654 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_11 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9057228688052:ℝ):ℂ) + (((-0.4238703633463):ℝ):ℂ) * I)‖ ≤ 0.00000014242 := by
  have hl := lg_11
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.853640793494192372 31.85364081342021894 (-0.4377143) 0.00000004241 0.9057228688052 (-0.4238703633463) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_12 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0227751038174):ℝ):ℂ) + (((-0.9997406136823):ℝ):ℂ) * I)‖ ≤ 0.00000011049 := by
  have hl := lg_12
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.009499925424450576 33.00949994535046386 (-1.5935734) 0.00000001048 (-0.0227751038174) (-0.9997406136823) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_13 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8847998827747):ℝ):ℂ) + (((-0.4659712087042):ℝ):ℂ) * I)‖ ≤ 0.0000001382 := by
  have hl := lg_13
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.0727872541597028 34.072787274085729368 (-2.6568607) 0.00000003819 (-0.8847998827747) (-0.4659712087042) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_14 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8777175555379):ℝ):ℂ) + ((0.4791783515626:ℝ):ℂ) * I)‖ ≤ 0.00000013311 := by
  have hl := lg_14
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.057237556249745848 35.057237576175772416 2.6418743 0.0000000331 (-0.8777175555379) 0.4791783515626 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p284_15 : ‖exp (-((((((13284:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1539618337162):ℝ):ℂ) + ((0.988076795476:ℝ):ℂ) * I)‖ ≤ 0.00000013795 := by
  have hl := lg_15
  refine (ecis_approx ((((13284:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.973738861082402932 35.9737388810084295 1.725373 0.00000003794 (-0.1539618337162) 0.988076795476 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_2 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9921332837104):ℝ):ℂ) + (((-0.1251860492298):ℝ):ℂ) * I)‖ ≤ 0.00000013629 := by
  have hl := lg_2
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.2992625709048 9.2992625776128 (-3.0160773) 0.00000003628 (-0.9921332837104) (-0.1251860492298) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_3 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.566139999182):ℝ):ℂ) + (((-0.8243091054432):ℝ):ℂ) * I)‖ ≤ 0.00000015309 := by
  have hl := lg_3
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.738982461283928224 14.73898246799194164 (-2.1726119) 0.00000005308 (-0.566139999182) (-0.8243091054432) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_4 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9686568829964:ℝ):ℂ) + ((0.2484025825626:ℝ):ℂ) * I)‖ ≤ 0.0000001337 := by
  have hl := lg_4
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.5985251418096 18.5985251552256 0.2510308 0.00000003369 0.9686568829964 0.2484025825626 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_5 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9214773176423):ℝ):ℂ) + (((-0.3884321728765):ℝ):ℂ) * I)‖ ≤ 0.00000011813 := by
  have hl := lg_5
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.592219026241027944 21.59221903965704136 (-2.7426631) 0.00000001812 (-0.9214773176423) (-0.3884321728765) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_6 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4584942536228:ℝ):ℂ) + ((0.8886973722223:ℝ):ℂ) * I)‖ ≤ 0.0000001169 := by
  have hl := lg_6
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.038245032188728224 24.03824504560474164 1.0944962 0.00000001689 0.4584942536228 0.8886973722223 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_7 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5623351338327:ℝ):ℂ) + (((-0.8269094250626):ℝ):ℂ) * I)‖ ≤ 0.00000013746 := by
  have hl := lg_7
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.106330552751221552 26.106330566167248384 (-0.9735893) 0.00000003745 0.5623351338327 (-0.8269094250626) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_8 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9299401962685):ℝ):ℂ) + (((-0.3677107983246):ℝ):ℂ) * I)‖ ≤ 0.00000011602 := by
  have hl := lg_8
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.8977877127144 27.8977877328384 (-2.7650465) 0.00000001601 (-0.9299401962685) (-0.3677107983246) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_9 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3589710892852):ℝ):ℂ) + ((0.9333486792485:ℝ):ℂ) * I)‖ ≤ 0.00000011335 := by
  have hl := lg_9
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.477964922567856448 29.47796493598388328 1.9379616 0.00000001334 (-0.3589710892852) 0.9333486792485 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_10 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8656020316288:ℝ):ℂ) + ((0.5007325861576:ℝ):ℂ) * I)‖ ≤ 0.00000013877 := by
  have hl := lg_10
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.891481597145827944 30.89148161726984136 0.5244449 0.00000003876 0.8656020316288 0.5007325861576 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_11 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7287946172371:ℝ):ℂ) + (((-0.6847323607704):ℝ):ℂ) * I)‖ ≤ 0.00000015364 := by
  have hl := lg_11
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.170162969400638728 32.17016298952466556 (-0.7542364) 0.00000005363 0.7287946172371 (-0.6847323607704) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_12 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3436348963245):ℝ):ℂ) + (((-0.9391033265971):ℝ):ℂ) * I)‖ ≤ 0.00000013282 := by
  have hl := lg_12
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.337507603093528224 33.33750762321754164 (-1.9215811) 0.00000003281 (-0.3436348963245) (-0.9391033265971) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_13 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9893378248689):ℝ):ℂ) + (((-0.1456388268423):ℝ):ℂ) * I)‖ ≤ 0.00000015348 := by
  have hl := lg_13
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.4113605692416872 34.411360589365714032 (-2.995434) 0.00000005347 (-0.9893378248689) (-0.1456388268423) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_14 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6614289217613):ℝ):ℂ) + ((0.7500078542519:ℝ):ℂ) * I)‖ ≤ 0.00000011944 := by
  have hl := lg_14
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.405593123656021552 35.405593143780048384 2.2935187 0.00000001943 (-0.6614289217613) 0.7500078542519 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p416_15 : ‖exp (-((((((13416:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2014969979002:ℝ):ℂ) + ((0.9794891320669:ℝ):ℂ) * I)‖ ≤ 0.00000015557 := by
  have hl := lg_15
  refine (ecis_approx ((((13416:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.331201487524956168 36.331201507648983 1.3679103 0.00000005556 0.2014969979002 0.9794891320669 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
