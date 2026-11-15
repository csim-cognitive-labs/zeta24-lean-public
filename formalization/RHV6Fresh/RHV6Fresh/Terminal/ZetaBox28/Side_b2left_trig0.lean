/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
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
namespace H28

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

lemma cs_b2left_vm0p872_2 : ‖exp (-((((((-872:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8228293976405:ℝ):ℂ) + ((0.5682884675749:ℝ):ℂ) * I)‖ ≤ 0.00000014167 := by
  have hl := lg_2
  refine (ecis_approx ((((-872:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.6044243416576) (-0.6044243412216) 0.6044243 0.00000004166 0.8228293976405 0.5682884675749 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p872_3 : ‖exp (-((((((-872:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5751654832811:ℝ):ℂ) + ((0.8180370815813:ℝ):ℂ) * I)‖ ≤ 0.00000011594 := by
  have hl := lg_3
  refine (ecis_approx ((((-872:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.95798991592791988) (-0.957989915491919008) 0.9579899 0.00000001593 0.5751654832811 0.8180370815813 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p872_4 : ‖exp (-((((((-872:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3540963417218:ℝ):ℂ) + ((0.935208950331:ℝ):ℂ) * I)‖ ≤ 0.00000011757 := by
  have hl := lg_4
  refine (ecis_approx ((((-872:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-1.2088486833152) (-1.2088486824432) 1.2088487 0.00000001756 0.3540963417218 0.935208950331 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p872_5 : ‖exp (-((((((-872:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1665861557346:ℝ):ℂ) + ((0.9860269026338:ℝ):ℂ) * I)‖ ≤ 0.00000014083 := by
  have hl := lg_5
  refine (ecis_approx ((((-872:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-1.40342986006119112) (-1.403429859189190248) 1.4034299 0.00000004082 0.1665861557346 0.9860269026338 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p489_2 : ‖exp (-((((((-489:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9431046397138:ℝ):ℂ) + ((0.3324960729847:ℝ):ℂ) * I)‖ ≤ 0.00000012885 := by
  have hl := lg_2
  refine (ecis_approx ((((-489:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.3389489714112) (-0.3389489711667) 0.338949 0.00000002884 0.9431046397138 0.3324960729847 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p489_3 : ‖exp (-((((((-489:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8591339467736:ℝ):ℂ) + ((0.5117507806552:ℝ):ℂ) * I)‖ ≤ 0.00000010929 := by
  have hl := lg_3
  refine (ecis_approx ((((-489:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.537221409276092685) (-0.537221409031592196) 0.5372214 0.00000000928 0.8591339467736 0.5117507806552 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p489_4 : ‖exp (-((((((-489:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7788927856152:ℝ):ℂ) + ((0.6271571003477:ℝ):ℂ) * I)‖ ≤ 0.00000014284 := by
  have hl := lg_4
  refine (ecis_approx ((((-489:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.6778979428224) (-0.6778979423334) 0.6778979 0.00000004283 0.7788927856152 0.6271571003477 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p489_5 : ‖exp (-((((((-489:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7059625104889:ℝ):ℂ) + ((0.7082492031653:ℝ):ℂ) * I)‖ ≤ 0.00000013943 := by
  have hl := lg_5
  refine (ecis_approx ((((-489:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.78701513941504869) (-0.787015138926048201) 0.7870151 0.00000003942 0.7059625104889 0.7082492031653 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p254_2 : ‖exp (-((((((-254:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9845415361853:ℝ):ℂ) + ((0.1751512589905:ℝ):ℂ) * I)‖ ≤ 0.00000011622 := by
  have hl := lg_2
  refine (ecis_approx ((((-254:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.1760593839232) (-0.1760593837962) 0.1760594 0.00000001621 0.9845415361853 0.1751512589905 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p254_3 : ‖exp (-((((((-254:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9613182310645:ℝ):ℂ) + ((0.2754401180349:ℝ):ℂ) * I)‖ ≤ 0.0000001214 := by
  have hl := lg_3
  refine (ecis_approx ((((-254:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.27904752138267391) (-0.279047521255673656) 0.2790475 0.00000002139 0.9613182310645 0.2754401180349 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p254_4 : ‖exp (-((((((-254:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9386440729481:ℝ):ℂ) + ((0.3448873791826:ℝ):ℂ) * I)‖ ≤ 0.00000013242 := by
  have hl := lg_4
  refine (ecis_approx ((((-254:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.3521187678464) (-0.3521187675924) 0.3521188 0.00000003241 0.9386440729481 0.3448873791826 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p254_5 : ‖exp (-((((((-254:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9175996065887:ℝ):ℂ) + ((0.3975059269852:ℝ):ℂ) * I)‖ ≤ 0.0000001299 := by
  have hl := lg_5
  refine (ecis_approx ((((-254:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.40879722988020934) (-0.408797229626209086) 0.4087972 0.00000002989 0.9175996065887 0.3975059269852 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p095_2 : ‖exp (-((((((-95:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9978327378898:ℝ):ℂ) + ((0.0658014224423:ℝ):ℂ) * I)‖ ≤ 0.00000011789 := by
  have hl := lg_2
  refine (ecis_approx ((((-95:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.065848982176) (-0.0658489821285) 0.065849 0.00000001788 0.9978327378898 0.0658014224423 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p095_3 : ‖exp (-((((((-95:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.994558581427:ℝ):ℂ) + ((0.1041788275515:ℝ):ℂ) * I)‖ ≤ 0.00000013262 := by
  have hl := lg_3
  refine (ecis_approx ((((-95:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.104368167446275675) (-0.10436816739877558) 0.1043682 0.00000003261 0.994558581427 0.1041788275515 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p095_4 : ‖exp (-((((((-95:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9913403456091:ℝ):ℂ) + ((0.1313176270254:ℝ):ℂ) * I)‖ ≤ 0.00000013576 := by
  have hl := lg_4
  refine (ecis_approx ((((-95:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.131697964352) (-0.131697964257) 0.131698 0.00000003575 0.9913403456091 0.1313176270254 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p095_5 : ‖exp (-((((((-95:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9883340680109:ℝ):ℂ) + ((0.1523015758586:ℝ):ℂ) * I)‖ ≤ 0.00000010174 := by
  have hl := lg_5
  refine (ecis_approx ((((-95:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.15289660172684995) (-0.152896601631849855) 0.1528966 0.00000000173 0.9883340680109 0.1523015758586 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p141_2 : ‖exp (-((((((141:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9952278525715:ℝ):ℂ) + (((-0.0975782837823):ℝ):ℂ) * I)‖ ≤ 0.00000014759 := by
  have hl := lg_2
  refine (ecis_approx ((((141:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.0977337524223 0.0977337524928 (-0.0977338) 0.00000004758 0.9952278525715 (-0.0975782837823) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p141_3 : ‖exp (-((((((141:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9880263004254:ℝ):ℂ) + (((-0.1542855458808):ℝ):ℂ) * I)‖ ≤ 0.00000013275 := by
  have hl := lg_3
  refine (ecis_approx ((((141:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.154904332665551124 0.154904332736051265 (-0.1549043) 0.00000003274 0.9880263004254 (-0.1542855458808) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p141_4 : ‖exp (-((((((141:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9809569764907:ℝ):ℂ) + (((-0.1942251535568):ℝ):ℂ) * I)‖ ≤ 0.000000105 := by
  have hl := lg_4
  refine (ecis_approx ((((141:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.1954675048446 0.1954675049856 (-0.1954675) 0.00000000499 0.9809569764907 (-0.1942251535568) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p141_5 : ‖exp (-((((((141:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9743615390613:ℝ):ℂ) + (((-0.2249879801192):ℝ):ℂ) * I)‖ ≤ 0.00000014574 := by
  have hl := lg_5
  refine (ecis_approx ((((141:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 0.226930745579903469 0.22693074572090361 (-0.2269307) 0.00000004573 0.9743615390613 (-0.2249879801192) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p318_2 : ‖exp (-((((((318:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9758055319056:ℝ):ℂ) + (((-0.2186402613942):ℝ):ℂ) * I)‖ ≤ 0.00000010351 := by
  have hl := lg_2
  refine (ecis_approx ((((318:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.2204208033354 0.2204208034944 (-0.2204208) 0.0000000035 0.9758055319056 (-0.2186402613942) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p318_3 : ‖exp (-((((((318:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9395924200304:ℝ):ℂ) + (((-0.3422953172649):ℝ):ℂ) * I)‖ ≤ 0.00000010789 := by
  have hl := lg_3
  refine (ecis_approx ((((318:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.349358707713796152 0.34935870787279647 (-0.3493587) 0.00000000788 0.9395924200304 (-0.3422953172649) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p318_4 : ‖exp (-((((((318:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.904392872195:ℝ):ℂ) + (((-0.4267007531314):ℝ):ℂ) * I)‖ ≤ 0.000000107 := by
  have hl := lg_4
  refine (ecis_approx ((((318:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.4408416066708 0.4408416069888 (-0.4408416) 0.00000000699 0.904392872195 (-0.4267007531314) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p318_5 : ‖exp (-((((((318:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8718637385578:ℝ):ℂ) + (((-0.4897485287247):ℝ):ℂ) * I)‖ ≤ 0.00000014403 := by
  have hl := lg_5
  refine (ecis_approx ((((318:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 0.511801255988718462 0.51180125630671878 (-0.5118013) 0.00000004402 0.8718637385578 (-0.4897485287247) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p633_2 : ‖exp (-((((((633:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9052781978482:ℝ):ℂ) + (((-0.424819237442):ℝ):ℂ) * I)‖ ≤ 0.00000013489 := by
  have hl := lg_2
  refine (ecis_approx ((((633:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.4387621651299 0.4387621654464 (-0.4387622) 0.00000003488 0.9052781978482 (-0.424819237442) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p633_3 : ‖exp (-((((((633:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7677836470393:ℝ):ℂ) + (((-0.6407091940491):ℝ):ℂ) * I)‖ ≤ 0.00000012145 := by
  have hl := lg_3
  refine (ecis_approx ((((633:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.695421578562367812 0.695421578878868445 (-0.6954216) 0.00000002144 0.7677836470393 (-0.6407091940491) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p633_4 : ‖exp (-((((((633:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6390573079144:ℝ):ℂ) + (((-0.7691591234596):ℝ):ℂ) * I)‖ ≤ 0.00000013091 := by
  have hl := lg_4
  refine (ecis_approx ((((633:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.8775243302598 0.8775243308928 (-0.8775243) 0.0000000309 0.6390573079144 (-0.7691591234596) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p633_5 : ‖exp (-((((((633:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5244100718023:ℝ):ℂ) + (((-0.8514658399444):ℝ):ℂ) * I)‖ ≤ 0.00000010177 := by
  have hl := lg_5
  refine (ecis_approx ((((633:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 1.018774198241694297 1.01877419887469493 (-1.0187742) 0.00000000176 0.5244100718023 (-0.8514658399444) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p948_2 : ‖exp (-((((((948:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7917648080745:ℝ):ℂ) + (((-0.6108260707393):ℝ):ℂ) * I)‖ ≤ 0.00000012741 := by
  have hl := lg_2
  refine (ecis_approx ((((948:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.6571035269244 0.6571035273984 (-0.6571035) 0.0000000274 0.7917648080745 (-0.6108260707393) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p948_3 : ‖exp (-((((((948:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5049395471543:ℝ):ℂ) + (((-0.863154710188):ℝ):ℂ) * I)‖ ≤ 0.0000001499 := by
  have hl := lg_3
  refine (ecis_approx ((((948:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.041484449410939472 1.04148444988494042 (-1.0414844) 0.00000004989 0.5049395471543 (-0.863154710188) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p948_4 : ‖exp (-((((((948:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2537829258843:ℝ):ℂ) + (((-0.9672611987098):ℝ):ℂ) * I)‖ ≤ 0.00000014617 := by
  have hl := lg_4
  refine (ecis_approx ((((948:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 1.3142070538488 1.3142070547968 (-1.3142071) 0.00000004616 0.2537829258843 (-0.9672611987098) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p948_5 : ‖exp (-((((((948:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0450339909443:ℝ):ℂ) + (((-0.9989854551791):ℝ):ℂ) * I)‖ ≤ 0.00000014146 := by
  have hl := lg_5
  refine (ecis_approx ((((948:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 1.525747140494670132 1.52574714144267108 (-1.5257471) 0.00000004145 0.0450339909443 (-0.9989854551791) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p369_2 : ‖exp (-((((((1369:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5825624579803:ℝ):ℂ) + (((-0.8127859389482):ℝ):ℂ) * I)‖ ≤ 0.00000011018 := by
  have hl := lg_2
  refine (ecis_approx ((((1369:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.9489184898307 0.9489184905152 (-0.9489185) 0.00000001017 0.5825624579803 (-0.8127859389482) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p369_3 : ‖exp (-((((((1369:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0667464669103:ℝ):ℂ) + (((-0.9977699680562):ℝ):ℂ) * I)‖ ≤ 0.00000012353 := by
  have hl := lg_3
  refine (ecis_approx ((((1369:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.504000222830776516 1.504000223515277885 (-1.5040002) 0.00000002352 0.0667464669103 (-0.9977699680562) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p369_4 : ‖exp (-((((((1369:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.321241965104):ℝ):ℂ) + (((-0.9469971488099):ℝ):ℂ) * I)‖ ≤ 0.00000012035 := by
  have hl := lg_4
  refine (ecis_approx ((((1369:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 1.8978369796614 1.8978369810304 (-1.897837) 0.00000002034 (-0.321241965104) (-0.9469971488099) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p369_5 : ‖exp (-((((((1369:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5911824803088):ℝ):ℂ) + (((-0.8065378323207):ℝ):ℂ) * I)‖ ≤ 0.00000010279 := by
  have hl := lg_5
  refine (ecis_approx ((((1369:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 2.203320501410552121 2.20332050277955349 (-2.2033205) 0.00000000278 (-0.5911824803088) (-0.8065378323207) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p79_2 : ‖exp (-((((((1790:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3241024645636:ℝ):ℂ) + (((-0.9460219830764):ℝ):ℂ) * I)‖ ≤ 0.00000014728 := by
  have hl := lg_2
  refine (ecis_approx ((((1790:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.240733452737 1.240733453632 (-1.2407335) 0.00000004727 0.3241024645636 (-0.9460219830764) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p79_3 : ‖exp (-((((((1790:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.385472344995):ℝ):ℂ) + (((-0.9227193892192):ℝ):ℂ) * I)‖ ≤ 0.00000010376 := by
  have hl := lg_3
  refine (ecis_approx ((((1790:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.96651599625061356 1.96651599714561535 (-1.966516) 0.00000000375 (-0.385472344995) (-0.9227193892192) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p79_4 : ‖exp (-((((((1790:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.789915123597):ℝ):ℂ) + (((-0.6132161914587):ℝ):ℂ) * I)‖ ≤ 0.00000010728 := by
  have hl := lg_4
  refine (ecis_approx ((((1790:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 2.481466905474 2.481466907264 (-2.4814669) 0.00000000727 (-0.789915123597) (-0.6132161914587) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p79_5 : ‖exp (-((((((1790:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9662101061698):ℝ):ℂ) + (((-0.2577557574131):ℝ):ℂ) * I)‖ ≤ 0.00000013769 := by
  have hl := lg_5
  refine (ecis_approx ((((1790:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 2.88089386232643411 2.8808938641164359 (-2.8808939) 0.00000003768 (-0.9662101061698) (-0.2577557574131) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p352_2 : ‖exp (-((((((2352:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0594507969328):ℝ):ℂ) + (((-0.9982312371108):ℝ):ℂ) * I)‖ ≤ 0.00000013195 := by
  have hl := lg_2
  refine (ecis_approx ((((2352:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.6302821680656 1.6302821692416 (-1.6302822) 0.00000003194 (-0.0594507969328) (-0.9982312371108) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p352_3 : ‖exp (-((((((2352:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8484975897931):ℝ):ℂ) + (((-0.5291992441816):ℝ):ℂ) * I)‖ ≤ 0.00000010353 := by
  have hl := lg_3
  refine (ecis_approx ((((2352:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 2.583936102336001728 2.58393610351200408 (-2.5839361) 0.00000000352 (-0.8484975897931) (-0.5291992441816) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p352_4 : ‖exp (-((((((2352:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9929312163072):ℝ):ℂ) + ((0.1186911927639:ℝ):ℂ) * I)‖ ≤ 0.00000013132 := by
  have hl := lg_4
  refine (ecis_approx ((((2352:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.2605643361312 3.2605643384832 3.022621 0.00000003131 (-0.9929312163072) 0.1186911927639 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p352_5 : ‖exp (-((((((2352:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7998174160889):ℝ):ℂ) + ((0.6002433680364:ℝ):ℂ) * I)‖ ≤ 0.00000013837 := by
  have hl := lg_5
  refine (ecis_approx ((((2352:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.785397968822219568 3.78539797117422192 2.4977873 0.00000003836 (-0.7998174160889) 0.6002433680364 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p914_2 : ‖exp (-((((((2914:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4340960157818):ℝ):ℂ) + (((-0.9008666100363):ℝ):ℂ) * I)‖ ≤ 0.00000011662 := by
  have hl := lg_2
  refine (ecis_approx ((((2914:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.0198308833942 2.0198308848512 (-2.0198309) 0.00000001661 (-0.4340960157818) (-0.9008666100363) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p914_3 : ‖exp (-((((((2914:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9982146900444):ℝ):ℂ) + ((0.0597279836169:ℝ):ℂ) * I)‖ ≤ 0.00000010271 := by
  have hl := lg_3
  refine (ecis_approx ((((2914:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.201356208421389896 3.20135620987839281 3.0818291 0.0000000027 (-0.9982146900444) 0.0597279836169 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p914_4 : ‖exp (-((((((2914:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6231212925483):ℝ):ℂ) + ((0.7821252168028:ℝ):ℂ) * I)‖ ≤ 0.00000014041 := by
  have hl := lg_4
  refine (ecis_approx ((((2914:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.0396617667884 4.0396617697024 2.2435235 0.0000000404 (-0.6231212925483) 0.7821252168028 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p914_5 : ‖exp (-((((((2914:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0224849781363):ℝ):ℂ) + ((0.9997471809202:ℝ):ℂ) * I)‖ ≤ 0.00000013188 := by
  have hl := lg_5
  refine (ecis_approx ((((2914:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.689902075318005026 4.68990207823200794 1.5932832 0.00000003187 (-0.0224849781363) 0.9997471809202 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v3p476_2 : ‖exp (-((((((3476:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7436967605199):ℝ):ℂ) + (((-0.6685171114937):ℝ):ℂ) * I)‖ ≤ 0.00000010129 := by
  have hl := lg_2
  refine (ecis_approx ((((3476:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.4093795987228 2.4093796004608 (-2.4093796) 0.00000000128 (-0.7436967605199) (-0.6685171114937) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v3p476_3 : ‖exp (-((((((3476:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7793405316015):ℝ):ℂ) + ((0.6266006190238:ℝ):ℂ) * I)‖ ≤ 0.00000010908 := by
  have hl := lg_3
  refine (ecis_approx ((((3476:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.818776314506778064 3.81877631624478154 2.464409 0.00000000907 (-0.7793405316015) 0.6266006190238 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v3p476_4 : ‖exp (-((((((3476:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1061697503704:ℝ):ℂ) + ((0.9943480196119:ℝ):ℂ) * I)‖ ≤ 0.00000010975 := by
  have hl := lg_4
  refine (ecis_approx ((((3476:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.8187591974456 4.8187592009216 1.4644261 0.00000000974 0.1061697503704 0.9943480196119 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v3p476_5 : ‖exp (-((((((3476:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7720225882415:ℝ):ℂ) + ((0.6355950937861:ℝ):ℂ) * I)‖ ≤ 0.00000012538 := by
  have hl := lg_5
  refine (ecis_approx ((((3476:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.594406181813790484 5.59440618528979396 0.6887791 0.00000002537 0.7720225882415 0.6355950937861 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p038_2 : ‖exp (-((((((4038:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9418627927833):ℝ):ℂ) + (((-0.3359977371753):ℝ):ℂ) * I)‖ ≤ 0.00000011609 := by
  have hl := lg_2
  refine (ecis_approx ((((4038:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.7989283140514 2.7989283160704 (-2.7989283) 0.00000001608 (-0.9418627927833) (-0.3359977371753) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p038_3 : ‖exp (-((((((4038:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2726945060856):ℝ):ℂ) + ((0.962100673708:ℝ):ℂ) * I)‖ ≤ 0.00000011545 := by
  have hl := lg_3
  refine (ecis_approx ((((4038:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.436196420592166232 4.43619642261117027 1.8469889 0.00000001544 (-0.2726945060856) 0.962100673708 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p038_4 : ‖exp (-((((((4038:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7742110456413:ℝ):ℂ) + ((0.6329275288744:ℝ):ℂ) * I)‖ ≤ 0.00000012498 := by
  have hl := lg_4
  refine (ecis_approx ((((4038:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.5978566281028 5.5978566321408 0.6853287 0.00000002497 0.7742110456413 0.6329275288744 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p038_5 : ‖exp (-((((((4038:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9768214605733:ℝ):ℂ) + (((-0.2140556800542):ℝ):ℂ) * I)‖ ≤ 0.00000011889 := by
  have hl := lg_5
  refine (ecis_approx ((((4038:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.498910288309575942 6.49891029234757998 (-0.215725) 0.00000001888 0.9768214605733 (-0.2140556800542) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p6_2 : ‖exp (-((((((4600:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9989011297281):ℝ):ℂ) + ((0.0468671787971:ℝ):ℂ) * I)‖ ≤ 0.00000012452 := by
  have hl := lg_2
  refine (ecis_approx ((((4600:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.18847702938 3.18847703168 3.0947083 0.00000002451 (-0.9989011297281) 0.0468671787971 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p6_3 : ‖exp (-((((((4600:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3346440972103:ℝ):ℂ) + ((0.9423445910081:ℝ):ℂ) * I)‖ ≤ 0.00000012181 := by
  have hl := lg_3
  refine (ecis_approx ((((4600:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.0536165266775544 5.053616528977559 1.2295688 0.0000000218 0.3346440972103 0.9423445910081 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p6_4 : ‖exp (-((((((4600:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9956069263627:ℝ):ℂ) + (((-0.0936314486623):ℝ):ℂ) * I)‖ ≤ 0.00000014843 := by
  have hl := lg_4
  refine (ecis_approx ((((4600:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.37695405876 6.37695406336 (-0.0937688) 0.00000004842 0.9956069263627 (-0.0936314486623) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p6_5 : ‖exp (-((((((4600:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4354762218334:ℝ):ℂ) + (((-0.9002002334024):ℝ):ℂ) * I)‖ ≤ 0.00000011239 := by
  have hl := lg_5
  refine (ecis_approx ((((4600:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.4034143948053614 7.403414399405366 (-1.1202291) 0.00000001238 0.4354762218334 (-0.9002002334024) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p162_2 : ‖exp (-((((((5162:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.906265207587):ℝ):ℂ) + ((0.4227095615117:ℝ):ℂ) * I)‖ ≤ 0.00000014013 := by
  have hl := lg_2
  refine (ecis_approx ((((5162:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.5780257447086 3.5780257472896 2.7051596 0.00000004012 (-0.906265207587) 0.4227095615117 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p162_3 : ‖exp (-((((((5162:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8184152063606:ℝ):ℂ) + ((0.5746273140025:ℝ):ℂ) * I)‖ ≤ 0.00000012818 := by
  have hl := lg_3
  refine (ecis_approx ((((5162:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.671036632762942568 5.67103663534394773 0.6121487 0.00000002817 0.8184152063606 0.5746273140025 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p162_4 : ‖exp (-((((((5162:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6426331819839:ℝ):ℂ) + (((-0.7661739968266):ℝ):ℂ) * I)‖ ≤ 0.00000011778 := by
  have hl := lg_4
  refine (ecis_approx ((((5162:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.1560514894172 7.1560514945792 (-0.8728662) 0.00000001777 0.6426331819839 (-0.7661739968266) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p162_5 : ‖exp (-((((((5162:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4385071002693):ℝ):ℂ) + (((-0.8987277246248):ℝ):ℂ) * I)‖ ≤ 0.00000010589 := by
  have hl := lg_5
  refine (ecis_approx ((((5162:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.307918501301146858 8.30791850646315202 (-2.0247332) 0.00000000588 (-0.4385071002693) (-0.8987277246248) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p724_2 : ‖exp (-((((((5724:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6778354202836):ℝ):ℂ) + ((0.7352136716552:ℝ):ℂ) * I)‖ ≤ 0.00000014716 := by
  have hl := lg_2
  refine (ecis_approx ((((5724:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.9675744600372 3.9675744628992 2.3156108 0.00000004715 (-0.6778354202836) 0.7352136716552 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p724_3 : ‖exp (-((((((5724:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999861062032:ℝ):ℂ) + (((-0.0052713755867):ℝ):ℂ) * I)‖ ≤ 0.00000013455 := by
  have hl := lg_3
  refine (ecis_approx ((((5724:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.288456738848330736 6.28845674171033646 (-0.0052714) 0.00000003454 0.9999861062032 (-0.0052713755867) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p724_4 : ‖exp (-((((((5724:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0810781791846):ℝ):ℂ) + (((-0.9967077449582):ℝ):ℂ) * I)‖ ≤ 0.00000011863 := by
  have hl := lg_4
  refine (ecis_approx ((((5724:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.9351489200744 7.9351489257984 (-1.6519636) 0.00000001862 (-0.0810781791846) (-0.9967077449582) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p724_5 : ‖exp (-((((((5724:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9775372053744):ℝ):ℂ) + (((-0.2107629279529):ℝ):ℂ) * I)‖ ≤ 0.00000010636 := by
  have hl := lg_5
  refine (ecis_approx ((((5724:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.212422607796932316 9.21242261352093804 (-2.9292373) 0.00000000635 (-0.9775372053744) (-0.2107629279529) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p286_2 : ‖exp (-((((((6286:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3478395542695):ℝ):ℂ) + ((0.9375540754982:ℝ):ℂ) * I)‖ ≤ 0.00000013183 := by
  have hl := lg_2
  refine (ecis_approx ((((6286:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.3571231753658 4.3571231785088 1.9260621 0.00000003182 (-0.3478395542695) 0.9375540754982 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p286_3 : ‖exp (-((((((6286:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.81231165448:ℝ):ℂ) + (((-0.5832236072005):ℝ):ℂ) * I)‖ ≤ 0.00000014091 := by
  have hl := lg_3
  refine (ecis_approx ((((6286:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.905876844933718904 6.90587684807672519 (-0.6226915) 0.0000000409 0.81231165448 (-0.5832236072005) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p286_4 : ‖exp (-((((((6286:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7580152190587):ℝ):ℂ) + (((-0.6522368646738):ℝ):ℂ) * I)‖ ≤ 0.00000014985 := by
  have hl := lg_4
  refine (ecis_approx ((((6286:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.7142463507316 8.7142463570176 (-2.431061) 0.00000004984 (-0.7580152190587) (-0.6522368646738) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p286_5 : ‖exp (-((((((6286:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7698764740116):ℝ):ℂ) + ((0.6381929290773:ℝ):ℂ) * I)‖ ≤ 0.00000010623 := by
  have hl := lg_5
  refine (ecis_approx ((((6286:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.116926714292717774 10.11692672057872406 2.4494439 0.00000000622 (-0.7698764740116) 0.6381929290773 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p848_2 : ‖exp (-((((((6848:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0342762116266:ℝ):ℂ) + ((0.9994123980201:ℝ):ℂ) * I)‖ ≤ 0.0000001165 := by
  have hl := lg_2
  refine (ecis_approx ((((6848:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.7466718906944 4.7466718941184 1.5365134 0.00000001649 0.0342762116266 0.9994123980201 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p848_3 : ‖exp (-((((((6848:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3246907329221:ℝ):ℂ) + (((-0.9458202408251):ℝ):ℂ) * I)‖ ≤ 0.00000014728 := by
  have hl := lg_3
  refine (ecis_approx ((((6848:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.523296951019107072 7.52329695444311392 (-1.2401116) 0.00000004727 0.3246907329221 (-0.9458202408251) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p848_4 : ‖exp (-((((((6848:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9976502823819):ℝ):ℂ) + ((0.0685121414662:ℝ):ℂ) * I)‖ ≤ 0.00000013299 := by
  have hl := lg_4
  refine (ecis_approx ((((6848:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.4933437813888 9.4933437882368 3.0730268 0.00000003298 (-0.9976502823819) 0.0685121414662 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p848_5 : ‖exp (-((((((6848:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0258536457847:ℝ):ℂ) + ((0.9996657386344:ℝ):ℂ) * I)‖ ≤ 0.00000011329 := by
  have hl := lg_5
  refine (ecis_approx ((((6848:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.021430820788503232 11.02143082763651008 1.5449398 0.00000001328 0.0258536457847 0.9996657386344 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p41_2 : ‖exp (-((((((7410:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4112560673125:ℝ):ℂ) + ((0.9115198555702:ℝ):ℂ) * I)‖ ≤ 0.00000010256 := by
  have hl := lg_2
  refine (ecis_approx ((((7410:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.136220606023 5.136220609728 1.1469647 0.00000000255 0.4112560673125 0.9115198555702 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p41_3 : ‖exp (-((((((7410:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2828224941392):ℝ):ℂ) + (((-0.959172266492):ℝ):ℂ) * I)‖ ≤ 0.00000015009 := by
  have hl := lg_3
  refine (ecis_approx ((((7410:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.14071705710449524 8.14071706080950265 (-1.8575318) 0.00000005008 (-0.2828224941392) (-0.959172266492) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p41_4 : ‖exp (-((((((7410:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6617368941952):ℝ):ℂ) + ((0.7497361421478:ℝ):ℂ) * I)‖ ≤ 0.00000010511 := by
  have hl := lg_4
  refine (ecis_approx ((((7410:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.272441212046 10.272441219456 2.2939294 0.0000000051 (-0.6617368941952) 0.7497361421478 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p41_5 : ‖exp (-((((((7410:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.801835483706:ℝ):ℂ) + ((0.5975448577889:ℝ):ℂ) * I)‖ ≤ 0.00000012035 := by
  have hl := lg_5
  refine (ecis_approx ((((7410:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.92593492728428869 11.9259349346942961 0.6404357 0.00000002034 0.801835483706 0.5975448577889 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p972_2 : ‖exp (-((((((7972:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.72661376189:ℝ):ℂ) + ((0.6870461709609:ℝ):ℂ) * I)‖ ≤ 0.00000011817 := by
  have hl := lg_2
  refine (ecis_approx ((((7972:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.5257693213516 5.5257693253376 0.757416 0.00000001816 0.72661376189 0.6870461709609 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p972_3 : ‖exp (-((((((7972:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7859032843687):ℝ):ℂ) + (((-0.6183494380803):ℝ):ℂ) * I)‖ ≤ 0.000000144 := by
  have hl := lg_3
  refine (ecis_approx ((((7972:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.758137163189883408 8.75813716717589138 (-2.4749519) 0.00000004399 (-0.7859032843687) (-0.6183494380803) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p972_4 : ‖exp (-((((((7972:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.055935117936:ℝ):ℂ) + ((0.998434405748:ℝ):ℂ) * I)‖ ≤ 0.00000013633 := by
  have hl := lg_4
  refine (ecis_approx ((((7972:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.0515386427032 11.0515386506752 1.514832 0.00000003632 0.055935117936 0.998434405748 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p972_5 : ‖exp (-((((((7972:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9653360767287:ℝ):ℂ) + (((-0.261010074453):ℝ):ℂ) * I)‖ ≤ 0.00000012741 := by
  have hl := lg_5
  refine (ecis_approx ((((7972:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.830439033780074148 12.83043904175208212 (-0.2640684) 0.0000000274 0.9653360767287 (-0.261010074453) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p534_2 : ‖exp (-((((((8534:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9330964419508:ℝ):ℂ) + ((0.3596262365551:ℝ):ℂ) * I)‖ ≤ 0.00000013378 := by
  have hl := lg_2
  refine (ecis_approx ((((8534:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.9153180366802 5.9153180409472 0.3678673 0.00000003377 0.9330964419508 0.3596262365551 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p534_3 : ‖exp (-((((((8534:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9987889078916):ℝ):ℂ) + (((-0.0492007814785):ℝ):ℂ) * I)‖ ≤ 0.00000013792 := by
  have hl := lg_3
  refine (ecis_approx ((((8534:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.375557269275271576 9.37555727354228011 (-3.092372) 0.00000003791 (-0.9987889078916) (-0.0492007814785) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p534_4 : ‖exp (-((((((8534:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7413380070756:ℝ):ℂ) + ((0.6711318493897:ℝ):ℂ) * I)‖ ≤ 0.00000014101 := by
  have hl := lg_4
  refine (ecis_approx ((((8534:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.8306360733604 11.8306360818944 0.7357345 0.000000041 0.7413380070756 0.6711318493897 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p534_5 : ‖exp (-((((((8534:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3914656578232:ℝ):ℂ) + (((-0.9201927182635):ℝ):ℂ) * I)‖ ≤ 0.00000013447 := by
  have hl := lg_5
  refine (ecis_approx ((((8534:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.734943140275859606 13.73494314880986814 (-1.1685725) 0.00000003446 0.3914656578232 (-0.9201927182635) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p096_2 : ‖exp (-((((((9096:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997649676543:ℝ):ℂ) + (((-0.0216797013633):ℝ):ℂ) * I)‖ ≤ 0.00000014939 := by
  have hl := lg_2
  refine (ecis_approx ((((9096:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.3048667520088 6.3048667565568 (-0.0216814) 0.00000004938 0.9997649676543 (-0.0216797013633) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p096_3 : ‖exp (-((((((9096:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8428712424614):ℝ):ℂ) + ((0.5381152930015:ℝ):ℂ) * I)‖ ≤ 0.00000013901 := by
  have hl := lg_3
  refine (ecis_approx ((((9096:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.992977375360659744 9.99297737990866884 2.5733932 0.000000039 (-0.8428712424614) 0.5381152930015 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p096_4 : ‖exp (-((((((9096:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9990599767627:ℝ):ℂ) + (((-0.0433493117704):ℝ):ℂ) * I)‖ ≤ 0.00000011036 := by
  have hl := lg_4
  refine (ecis_approx ((((9096:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.6097335040176 12.6097335131136 (-0.0433629) 0.00000001035 0.9990599767627 (-0.0433493117704) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p096_5 : ‖exp (-((((((9096:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4814254184501):ℝ):ℂ) + (((-0.8764870600668):ℝ):ℂ) * I)‖ ≤ 0.00000014152 := by
  have hl := lg_5
  refine (ecis_approx ((((9096:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.639447246771645064 14.63944725586765416 (-2.0730766) 0.00000004151 (-0.4814254184501) (-0.8764870600668) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p658_2 : ‖exp (-((((((9658:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9166297597634:ℝ):ℂ) + (((-0.39973726811):ℝ):ℂ) * I)‖ ≤ 0.00000013986 := by
  have hl := lg_2
  refine (ecis_approx ((((9658:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.6944154673374 6.6944154721664 (-0.4112302) 0.00000003985 0.9166297597634 (-0.39973726811) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p658_3 : ‖exp (-((((((9658:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3757229640083):ℝ):ℂ) + ((0.926732029399:ℝ):ℂ) * I)‖ ≤ 0.00000013293 := by
  have hl := lg_3
  refine (ecis_approx ((((9658:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.610397481446047912 10.61039748627505757 1.9559731 0.00000003292 (-0.3757229640083) 0.926732029399 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p658_4 : ‖exp (-((((((9658:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6804203062501:ℝ):ℂ) + (((-0.7328220840303):ℝ):ℂ) * I)‖ ≤ 0.00000012999 := by
  have hl := lg_4
  refine (ecis_approx ((((9658:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.3888309346748 13.3888309443328 (-0.8224603) 0.00000002998 0.6804203062501 (-0.7328220840303) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p658_5 : ‖exp (-((((((9658:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9865801625985):ℝ):ℂ) + (((-0.1632776236781):ℝ):ℂ) * I)‖ ≤ 0.00000014858 := by
  have hl := lg_5
  refine (ecis_approx ((((9658:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.543951353267430522 15.54395136292544018 (-2.9775807) 0.00000004857 (-0.9865801625985) (-0.1632776236781) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p22_2 : ‖exp (-((((((10220:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6961477494036:ℝ):ℂ) + (((-0.7178985380959):ℝ):ℂ) * I)‖ ≤ 0.00000012453 := by
  have hl := lg_2
  refine (ecis_approx ((((10220:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.083964182666 7.083964187776 (-0.8007789) 0.00000002452 0.6961477494036 (-0.7178985380959) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p22_3 : ‖exp (-((((((10220:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2301611999664:ℝ):ℂ) + ((0.9731525173527:ℝ):ℂ) * I)‖ ≤ 0.00000012684 := by
  have hl := lg_3
  refine (ecis_approx ((((10220:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.22781758753143608 11.2278175926414463 1.338553 0.00000002683 0.2301611999664 0.9731525173527 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p22_4 : ‖exp (-((((((10220:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0307566220005):ℝ):ℂ) + (((-0.9995269031911):ℝ):ℂ) * I)‖ ≤ 0.00000014904 := by
  have hl := lg_4
  refine (ecis_approx ((((10220:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.167928365332 14.167928375552 (-1.6015578) 0.00000004903 (-0.0307566220005) (-0.9995269031911) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p22_5 : ‖exp (-((((((10220:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7381366160876):ℝ):ℂ) + ((0.6746512698867:ℝ):ℂ) * I)‖ ≤ 0.00000014846 := by
  have hl := lg_5
  refine (ecis_approx ((((10220:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.44845545976321598 16.4484554699832262 2.4011005 0.00000004845 (-0.7381366160876) 0.6746512698867 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p782_2 : ‖exp (-((((((10782:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3713557186487:ℝ):ℂ) + (((-0.928490673204):ℝ):ℂ) * I)‖ ≤ 0.0000001092 := by
  have hl := lg_2
  refine (ecis_approx ((((10782:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.4735128979946 7.4735129033856 (-1.1903276) 0.00000000919 0.3713557186487 (-0.928490673204) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p782_3 : ‖exp (-((((((10782:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7510582299487:ℝ):ℂ) + ((0.6602359693522:ℝ):ℂ) * I)‖ ≤ 0.00000012076 := by
  have hl := lg_3
  refine (ecis_approx ((((10782:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.845237693616824248 11.84523769900783503 0.7211329 0.00000002075 0.7510582299487 0.6602359693522 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p782_4 : ‖exp (-((((((10782:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7241898604496):ℝ):ℂ) + (((-0.6896006423967):ℝ):ℂ) * I)‖ ≤ 0.00000011838 := by
  have hl := lg_4
  refine (ecis_approx ((((10782:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.9470257959892 14.9470258067712 (-2.3806552) 0.00000001837 (-0.7241898604496) (-0.6896006423967) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p782_5 : ‖exp (-((((((10782:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.074131959047:ℝ):ℂ) + ((0.9972484407848:ℝ):ℂ) * I)‖ ≤ 0.00000015529 := by
  have hl := lg_5
  refine (ecis_approx ((((10782:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.352959566259001438 17.35295957704101222 1.4965963 0.00000005528 0.074131959047 0.9972484407848 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p344_2 : ‖exp (-((((((11344:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0090798484379):ℝ):ℂ) + (((-0.9999587773264):ℝ):ℂ) * I)‖ ≤ 0.00000011183 := by
  have hl := lg_2
  refine (ecis_approx ((((11344:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.8630616133232 7.8630616189952 (-1.5798763) 0.00000001182 (-0.0090798484379) (-0.9999587773264) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p344_3 : ‖exp (-((((((11344:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9946266466197:ℝ):ℂ) + ((0.103526971529:ℝ):ℂ) * I)‖ ≤ 0.00000011467 := by
  have hl := lg_3
  refine (ecis_approx ((((11344:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.462657799702212416 12.46265780537422376 0.1037128 0.00000001466 0.9946266466197 0.103526971529 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p344_4 : ‖exp (-((((((11344:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998351122576):ℝ):ℂ) + ((0.0181589551742:ℝ):ℂ) * I)‖ ≤ 0.00000011647 := by
  have hl := lg_4
  refine (ecis_approx ((((11344:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.7261232266464 15.7261232379904 3.1234327 0.00000001646 (-0.9998351122576) 0.0181589551742 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p344_5 : ‖exp (-((((((11344:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8297748427792:ℝ):ℂ) + ((0.5580982980539:ℝ):ℂ) * I)‖ ≤ 0.0000001488 := by
  have hl := lg_5
  refine (ecis_approx ((((11344:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.257463672754786896 18.25746368409879824 0.5920922 0.00000004879 0.8297748427792 0.5580982980539 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p906_2 : ‖exp (-((((((11906:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.388154900926):ℝ):ℂ) + (((-0.9215941475965):ℝ):ℂ) * I)‖ ≤ 0.00000012744 := by
  have hl := lg_2
  refine (ecis_approx ((((11906:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.2526103286518 8.2526103346048 (-1.969425) 0.00000002743 (-0.388154900926) (-0.9215941475965) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p906_3 : ‖exp (-((((((11906:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8709286947587:ℝ):ℂ) + (((-0.4914094104165):ℝ):ℂ) * I)‖ ≤ 0.00000010859 := by
  have hl := lg_3
  refine (ecis_approx ((((11906:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.080077905787600584 13.08007791174061249 (-0.5137073) 0.00000000858 0.8709286947587 (-0.4914094104165) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p906_4 : ‖exp (-((((((11906:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6986715406346):ℝ):ℂ) + ((0.7154425751126:ℝ):ℂ) * I)‖ ≤ 0.00000014769 := by
  have hl := lg_4
  refine (ecis_approx ((((11906:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.5052206573036 16.5052206692096 2.3443353 0.00000004768 (-0.6986715406346) 0.7154425751126 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p906_5 : ‖exp (-((((((11906:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9515950296884:ℝ):ℂ) + (((-0.3073546802512):ℝ):ℂ) * I)‖ ≤ 0.0000001423 := by
  have hl := lg_5
  refine (ecis_approx ((((11906:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.161967779250572354 19.16196779115658426 (-0.3124119) 0.00000004229 0.9515950296884 (-0.3073546802512) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p327_2 : ‖exp (-((((((12327:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6368793007508):ℝ):ℂ) + (((-0.7709635245975):ℝ):ℂ) * I)‖ ≤ 0.00000011564 := by
  have hl := lg_2
  refine (ecis_approx ((((12327:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.5444252915581 8.5444252977216 (-2.26124) 0.00000001563 (-0.6368793007508) (-0.7709635245975) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p327_3 : ‖exp (-((((((12327:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5601552718761:ℝ):ℂ) + (((-0.8283876335324):ℝ):ℂ) * I)‖ ≤ 0.00000013517 := by
  have hl := lg_3
  refine (ecis_approx ((((12327:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.542593679207437628 13.542593685370949955 (-0.9762231) 0.00000003516 0.5601552718761 (-0.8283876335324) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p327_4 : ‖exp (-((((((12327:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1887695054962):ℝ):ℂ) + ((0.9820214222683:ℝ):ℂ) * I)‖ ≤ 0.00000013844 := by
  have hl := lg_4
  refine (ecis_approx ((((12327:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.0888505831162 17.0888505954432 1.7607053 0.00000003843 (-0.1887695054962) 0.9820214222683 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p327_5 : ‖exp (-((((((12327:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.548702233706:ℝ):ℂ) + (((-0.836017857899):ℝ):ℂ) * I)‖ ≤ 0.00000013097 := by
  have hl := lg_5
  refine (ecis_approx ((((12327:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.839541140166454343 19.83954115249346667 (-0.9899852) 0.00000003096 0.548702233706 (-0.836017857899) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p327_6 : ‖exp (-((((((12327:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9954079562177):ℝ):ℂ) + ((0.0957235614425:ℝ):ℂ) * I)‖ ≤ 0.00000015439 := by
  have hl := lg_6
  refine (ecis_approx ((((12327:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.087018970765537628 22.087018983092549955 3.0457223 0.00000005438 (-0.9954079562177) 0.0957235614425 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p327_7 : ‖exp (-((((((12327:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4125845345826:ℝ):ℂ) + ((0.910919316857:ℝ):ℂ) * I)‖ ≤ 0.00000012774 := by
  have hl := lg_7
  refine (ecis_approx ((((12327:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.987234400996146994 23.987234413323171648 1.1455068 0.00000002773 0.4125845345826 0.910919316857 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p327_8 : ‖exp (-((((((12327:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8773260876149:ℝ):ℂ) + (((-0.4798947134428):ℝ):ℂ) * I)‖ ≤ 0.00000015406 := by
  have hl := lg_8
  refine (ecis_approx ((((12327:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.6332758746743 25.6332758931648 (-0.5005347) 0.00000005405 0.8773260876149 (-0.4798947134428) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p327_9 : ‖exp (-((((((12327:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3724520499738):ℝ):ℂ) + (((-0.928051437404):ℝ):ℂ) * I)‖ ≤ 0.00000014204 := by
  have hl := lg_9
  refine (ecis_approx ((((12327:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.085187358414875256 27.08518737074189991 (-1.9524461) 0.00000004203 (-0.3724520499738) (-0.928051437404) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p327_10 : ‖exp (-((((((12327:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.993996368291):ℝ):ℂ) + ((0.1094130676172:ℝ):ℂ) * I)‖ ≤ 0.00000011433 := by
  have hl := lg_10
  refine (ecis_approx ((((12327:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.383966431724554343 28.38396645021506667 3.0319601 0.00000001432 (-0.993996368291) 0.1094130676172 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p748_2 : ‖exp (-((((((12748:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8317533828749):ℝ):ℂ) + (((-0.5551453053145):ℝ):ℂ) * I)‖ ≤ 0.00000015273 := by
  have hl := lg_2
  refine (ecis_approx ((((12748:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.8362402544644 8.8362402608384 (-2.553055) 0.00000005272 (-0.8317533828749) (-0.5551453053145) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p748_3 : ‖exp (-((((((12748:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1316740319478:ℝ):ℂ) + (((-0.9912930693345):ℝ):ℂ) * I)‖ ≤ 0.00000014466 := by
  have hl := lg_3
  refine (ecis_approx ((((12748:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.005109452627274672 14.00510945900128742 (-1.4387388) 0.00000004465 0.1316740319478 (-0.9912930693345) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p748_4 : ‖exp (-((((((12748:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3836272941778:ℝ):ℂ) + ((0.9234880070482:ℝ):ℂ) * I)‖ ≤ 0.00000011262 := by
  have hl := lg_4
  refine (ecis_approx ((((12748:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.6724805089288 17.6724805216768 1.1770754 0.00000001261 0.3836272941778 0.9234880070482 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p748_5 : ‖exp (-((((((12748:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0966113473583):ℝ):ℂ) + (((-0.9953221827937):ℝ):ℂ) * I)‖ ≤ 0.00000012047 := by
  have hl := lg_5
  refine (ecis_approx ((((12748:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.517114501082336332 20.51711451383034908 (-1.6675586) 0.00000002046 (-0.0966113473583) (-0.9953221827937) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p748_6 : ‖exp (-((((((12748:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6598320097812):ℝ):ℂ) + ((0.7514131479087:ℝ):ℂ) * I)‖ ≤ 0.00000012164 := by
  have hl := lg_6
  refine (ecis_approx ((((12748:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.841349707091674672 22.84134971983968742 2.2913915 0.00000002163 (-0.6598320097812) 0.7514131479087 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p748_7 : ‖exp (-((((((12748:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9472416836944:ℝ):ℂ) + ((0.3205201907398:ℝ):ℂ) * I)‖ ≤ 0.0000001552 := by
  have hl := lg_7
  refine (ecis_approx ((((12748:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.806462573529559656 24.806462586277585152 0.3262786 0.00000005519 0.9472416836944 0.3205201907398 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p748_8 : ‖exp (-((((((12748:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1935868300668:ℝ):ℂ) + (((-0.9810831459283):ℝ):ℂ) * I)‖ ≤ 0.00000015381 := by
  have hl := lg_8
  refine (ecis_approx ((((12748:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.5087207633932 26.5087207825152 (-1.3759795) 0.0000000538 0.1935868300668 (-0.9810831459283) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p748_9 : ‖exp (-((((((12748:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9653239246308):ℝ):ℂ) + (((-0.2610550139017):ℝ):ℂ) * I)‖ ≤ 0.00000012348 := by
  have hl := lg_9
  refine (ecis_approx ((((12748:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.010218905254549344 28.01021891800257484 (-2.8774777) 0.00000002347 (-0.9653239246308) (-0.2610550139017) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p748_10 : ‖exp (-((((((12748:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4721917039185):ℝ):ℂ) + ((0.8814958847013:ℝ):ℂ) * I)‖ ≤ 0.00000013879 := by
  have hl := lg_10
  refine (ecis_approx ((((12748:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.353354755546736332 29.35335477466874908 2.0625718 0.00000003878 (-0.4721917039185) 0.8814958847013 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p063_2 : ‖exp (-((((((13063:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9322563230912):ℝ):ℂ) + (((-0.3617984907275):ℝ):ℂ) * I)‖ ≤ 0.00000011563 := by
  have hl := lg_2
  refine (ecis_approx ((((13063:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.0545816162589 9.0545816227904 (-2.7713963) 0.00000001562 (-0.9322563230912) (-0.3617984907275) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p063_3 : ‖exp (-((((((13063:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.212375596031):ℝ):ℂ) + (((-0.9771881119874):ℝ):ℂ) * I)‖ ≤ 0.00000011566 := by
  have hl := lg_3
  refine (ecis_approx ((((13063:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.351172323475846332 14.351172330007359395 (-1.7848017) 0.00000001565 (-0.212375596031) (-0.9771881119874) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p063_4 : ‖exp (-((((((13063:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7382037089327:ℝ):ℂ) + ((0.6745778562316:ℝ):ℂ) * I)‖ ≤ 0.00000012406 := by
  have hl := lg_4
  refine (ecis_approx ((((13063:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.1091632325178 18.1091632455808 0.7403927 0.00000002405 0.7382037089327 0.6745778562316 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p063_5 : ‖exp (-((((((13063:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5677212988948):ℝ):ℂ) + (((-0.8232208250351):ℝ):ℂ) * I)‖ ≤ 0.00000013487 := by
  have hl := lg_5
  refine (ecis_approx ((((13063:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.024087443335312167 21.02408745639832523 (-2.1745315) 0.00000003486 (-0.5677212988948) (-0.8232208250351) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p063_6 : ‖exp (-((((((13063:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1555566847849):ℝ):ℂ) + ((0.9878269675495:ℝ):ℂ) * I)‖ ≤ 0.00000012409 := by
  have hl := lg_6
  refine (ecis_approx ((((13063:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.405753939734746332 23.405753952797759395 1.7269873 0.00000002408 (-0.1555566847849) 0.9878269675495 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p063_7 : ‖exp (-((((((13063:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.959187105775:ℝ):ℂ) + (((-0.2827721629067):ℝ):ℂ) * I)‖ ≤ 0.00000015468 := by
  have hl := lg_7
  refine (ecis_approx ((((13063:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.419424270318217586 25.419424283381243712 (-0.286683) 0.00000005467 0.959187105775 (-0.2827721629067) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p063_8 : ‖exp (-((((((13063:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4441338251008):ℝ):ℂ) + (((-0.8959604597285):ℝ):ℂ) * I)‖ ≤ 0.00000013967 := by
  have hl := lg_8
  refine (ecis_approx ((((13063:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.1637448487767 27.1637448683712 (-2.0310036) 0.00000003966 (-0.4441338251008) (-0.8959604597285) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p063_9 : ‖exp (-((((((13063:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9097932094019):ℝ):ℂ) + ((0.4150618218985:ℝ):ℂ) * I)‖ ≤ 0.00000012413 := by
  have hl := lg_9
  refine (ecis_approx ((((13063:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.702344646951692664 28.70234466001471879 2.7135819 0.00000002412 (-0.9097932094019) 0.4150618218985 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p063_10 : ‖exp (-((((((13063:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2314217255579:ℝ):ℂ) + ((0.9728535269709:ℝ):ℂ) * I)‖ ≤ 0.00000014331 := by
  have hl := lg_10
  refine (ecis_approx ((((13063:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.078669059594212167 30.07866907918872523 1.3372575 0.0000000433 0.2314217255579 0.9728535269709 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p378_2 : ‖exp (-((((((13378:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9884921760185):ℝ):ℂ) + (((-0.151271998596):ℝ):ℂ) * I)‖ ≤ 0.00000012914 := by
  have hl := lg_2
  refine (ecis_approx ((((13378:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.2729229780534 9.2729229847424 (-2.9897377) 0.00000002913 (-0.9884921760185) (-0.151271998596) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p378_3 : ‖exp (-((((((13378:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5312440415045):ℝ):ℂ) + (((-0.8472188432502):ℝ):ℂ) * I)‖ ≤ 0.00000012005 := by
  have hl := lg_3
  refine (ecis_approx ((((13378:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.697235194324417992 14.69723520101343137 (-2.1308646) 0.00000002004 (-0.5312440415045) (-0.8472188432502) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p378_4 : ‖exp (-((((((13378:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9542335370081:ℝ):ℂ) + ((0.2990624631228:ℝ):ℂ) * I)‖ ≤ 0.00000014796 := by
  have hl := lg_4
  refine (ecis_approx ((((13378:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.5458459561068 18.5458459694848 0.30371 0.00000004795 0.9542335370081 0.2990624631228 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p378_5 : ‖exp (-((((((13378:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8960133583922):ℝ):ℂ) + (((-0.4440270954242):ℝ):ℂ) * I)‖ ≤ 0.00000013597 := by
  have hl := lg_5
  refine (ecis_approx ((((13378:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.531060385588288002 21.53106039896630138 (-2.6815045) 0.00000003596 (-0.8960133583922) (-0.4440270954242) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p378_6 : ‖exp (-((((((13378:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3969700974358:ℝ):ℂ) + ((0.9178315432266:ℝ):ℂ) * I)‖ ≤ 0.00000015636 := by
  have hl := lg_6
  refine (ecis_approx ((((13378:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.970158172377817992 23.97015818575583137 1.162583 0.00000005635 0.3969700974358 0.9178315432266 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p378_7 : ‖exp (-((((((13378:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6218882450804:ℝ):ℂ) + (((-0.7831060021676):ℝ):ℂ) * I)‖ ≤ 0.00000015178 := by
  have hl := lg_7
  refine (ecis_approx ((((13378:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.032385967106875516 26.032385980484902272 (-0.8996447) 0.00000005177 0.6218882450804 (-0.7831060021676) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p378_8 : ‖exp (-((((((13378:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8980126089965):ℝ):ℂ) + (((-0.4399697193775):ℝ):ℂ) * I)‖ ≤ 0.00000012552 := by
  have hl := lg_8
  refine (ecis_approx ((((13378:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.8187689341602 27.8187689542272 (-2.6860277) 0.00000002551 (-0.8980126089965) (-0.4399697193775) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p378_9 : ‖exp (-((((((13378:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4355595302685):ℝ):ℂ) + ((0.900159927784:ℝ):ℂ) * I)‖ ≤ 0.00000014726 := by
  have hl := lg_9
  refine (ecis_approx ((((13378:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.394470388648835984 29.39447040202686274 2.0214561 0.00000004725 (-0.4355595302685) 0.900159927784 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p378_10 : ‖exp (-((((((13378:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8185332749919:ℝ):ℂ) + ((0.5744591175454:ℝ):ℂ) * I)‖ ≤ 0.00000014783 := by
  have hl := lg_10
  refine (ecis_approx ((((13378:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.803983363641688002 30.80398338370870138 0.6119432 0.00000004782 0.8185332749919 0.5744591175454 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_2 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.99993123036):ℝ):ℂ) + ((0.0117274844578:ℝ):ℂ) * I)‖ ≤ 0.00000010507 := by
  have hl := lg_2
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.4365057126042 9.4365057194112 3.1298649 0.00000000506 (-0.99993123036) 0.0117274844578 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_3 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7306959323843):ℝ):ℂ) + (((-0.6827030499181):ℝ):ℂ) * I)‖ ≤ 0.00000011999 := by
  have hl := lg_3
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.956507694388744696 14.95650770119575831 (-2.3901371) 0.00000001998 (-0.7306959323843) (-0.6827030499181) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_4 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997249323712:ℝ):ℂ) + (((-0.0234533493443):ℝ):ℂ) * I)‖ ≤ 0.0000001173 := by
  have hl := lg_4
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.8730114252084 18.8730114388224 (-0.0234555) 0.00000001729 0.9997249323712 (-0.0234533493443) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_5 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9967808261168):ℝ):ℂ) + (((-0.0801747103123):ℝ):ℂ) * I)‖ ≤ 0.00000012489 := by
  have hl := lg_5
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.910887732800041326 21.91088774641405494 (-3.0613318) 0.00000002488 (-0.9967808261168) (-0.0801747103123) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_6 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7386520725393:ℝ):ℂ) + ((0.674086875509:ℝ):ℂ) * I)‖ ≤ 0.00000012174 := by
  have hl := lg_6
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.393013406992944696 24.39301342060695831 0.7397278 0.00000002173 0.7386520725393 0.674086875509 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_7 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2103342315975:ℝ):ℂ) + (((-0.9776295366949):ℝ):ℂ) * I)‖ ≤ 0.00000014707 := by
  have hl := lg_7
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.491620762161235108 26.491620775775262336 (-1.3588795) 0.00000004706 0.2103342315975 (-0.9776295366949) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_8 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993811328836):ℝ):ℂ) + ((0.0351759951:ℝ):ℂ) * I)‖ ≤ 0.00000012235 := by
  have hl := lg_8
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.3095171378126 28.3095171582336 3.1064094 0.00000002234 (-0.9993811328836) 0.0351759951 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_9 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0678330983824:ℝ):ℂ) + ((0.9976966827467:ℝ):ℂ) * I)‖ ≤ 0.00000014714 := by
  have hl := lg_9
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.913015388777489392 29.91301540239151662 1.5029111 0.00000004713 0.0678330983824 0.9976966827467 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_10 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9976525261165:ℝ):ℂ) + ((0.0684794650487:ℝ):ℂ) * I)‖ ≤ 0.00000012994 := by
  have hl := lg_10
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.347393445404241326 31.34739346582525494 0.0685331 0.00000002993 0.9976525261165 0.0684794650487 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_11 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3351614881498:ℝ):ℂ) + (((-0.9421606958801):ℝ):ℂ) * I)‖ ≤ 0.0000001178 := by
  have hl := lg_11
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.644946233260308262 32.64494625368133549 (-1.2290197) 0.00000001779 0.3351614881498 (-0.9421606958801) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_12 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7465066147145):ℝ):ℂ) + (((-0.6653779934402):ℝ):ℂ) * I)‖ ≤ 0.00000011632 := by
  have hl := lg_12
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.829519119597144696 33.82951914001815831 (-2.4135926) 0.00000001631 (-0.7465066147145) (-0.6653779934402) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_13 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9352961263538):ℝ):ℂ) + ((0.3538660139912:ℝ):ℂ) * I)‖ ≤ 0.00000011922 := by
  have hl := lg_13
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.9192205418646638 34.919220562285691028 2.7798913 0.00000001921 (-0.9352961263538) 0.3538660139912 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_14 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1988546315721):ℝ):ℂ) + ((0.9800289972758:ℝ):ℂ) * I)‖ ≤ 0.00000015212 := by
  have hl := lg_14
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.928126474765435108 35.928126495186462336 1.7709854 0.00000005211 (-0.1988546315721) 0.9800289972758 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p614_15 : ‖exp (-((((((13614:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6736081811863:ℝ):ℂ) + ((0.7390886403125:ℝ):ℂ) * I)‖ ≤ 0.0000001159 := by
  have hl := lg_15
  refine (ecis_approx ((((13614:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.867395427188786022 36.86739544760981325 0.8317164 0.00000001589 0.6736081811863 0.7390886403125 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_2 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9909799164131):ℝ):ℂ) + ((0.1340104654417:ℝ):ℂ) * I)‖ ≤ 0.00000015086 := by
  have hl := lg_2
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.5591927635173 9.5591927704128 3.0071778 0.00000005085 (-0.9909799164131) 0.1340104654417 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_3 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8488442447172):ℝ):ℂ) + (((-0.5286430252424):ℝ):ℂ) * I)‖ ≤ 0.00000014494 := by
  have hl := lg_3
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.150962069436989724 15.150962076332503515 (-2.5845915) 0.00000004493 (-0.8488442447172) (-0.5286430252424) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_4 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9640824186641:ℝ):ℂ) + (((-0.2656032568001):ℝ):ℂ) * I)‖ ≤ 0.0000001193 := by
  have hl := lg_4
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.1183855270346 19.1183855408256 (-0.2688296) 0.00000001929 0.9640824186641 (-0.2656032568001) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_5 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9791403715076):ℝ):ℂ) + ((0.2031849713069:ℝ):ℂ) * I)‖ ≤ 0.0000001283 := by
  have hl := lg_5
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.195758243208856319 22.19575825699987011 2.936983 0.00000002829 (-0.9791403715076) 0.2031849713069 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_6 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9120312558158:ℝ):ℂ) + ((0.4101206998129:ℝ):ℂ) * I)‖ ≤ 0.00000011804 := by
  have hl := lg_6
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.710154832954289724 24.710154846745303515 0.4225864 0.00000001803 0.9120312558158 0.4101206998129 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_7 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1321218315825):ℝ):ℂ) + (((-0.991233484916):ℝ):ℂ) * I)‖ ≤ 0.00000014354 := by
  have hl := lg_7
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.836046858452004802 26.836046872243032384 (-1.7033056) 0.00000004353 (-0.1321218315825) (-0.991233484916) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_8 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9197926986754):ℝ):ℂ) + ((0.3924046270381:ℝ):ℂ) * I)‖ ≤ 0.00000014536 := by
  have hl := lg_8
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.6775782905519 28.6775783112384 2.7383482 0.00000004535 (-0.9197926986754) 0.3924046270381 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_9 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.441073020336:ℝ):ℂ) + ((0.8974712200019:ℝ):ℂ) * I)‖ ≤ 0.00000011678 := by
  have hl := lg_9
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.301924138873979448 30.30192415266500703 1.1140024 0.00000001677 0.441073020336 0.8974712200019 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_10 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9430795335724:ℝ):ℂ) + (((-0.3325672764373):ℝ):ℂ) * I)‖ ≤ 0.00000012919 := by
  have hl := lg_10
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.754951006726156319 31.75495102741267011 (-0.3390245) 0.00000002918 0.9430795335724 (-0.3325672764373) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_11 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0825568050233):ℝ):ℂ) + (((-0.9965863605047):ℝ):ℂ) * I)‖ ≤ 0.00000013951 := by
  have hl := lg_11
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.069373696407588603 33.069373717094116185 (-1.6534472) 0.0000000395 (-0.0825568050233) (-0.9965863605047) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_12 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9587651216484):ℝ):ℂ) + (((-0.2841996503894):ℝ):ℂ) * I)‖ ≤ 0.00000013944 := by
  have hl := lg_12
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.269347596471589724 34.269347617158103515 (-2.8534211) 0.00000003943 (-0.9587651216484) (-0.2841996503894) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_13 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.685360744667):ℝ):ℂ) + ((0.7282037143877:ℝ):ℂ) * I)‖ ≤ 0.00000015562 := by
  have hl := lg_13
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.3732165779973247 35.373216598683852282 2.3258953 0.00000005561 (-0.685360744667) 0.7282037143877 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_14 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2637657425157:ℝ):ℂ) + ((0.9645867680386:ℝ):ℂ) * I)‖ ≤ 0.00000012112 := by
  have hl := lg_14
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.395239621969304802 36.395239642655832384 1.3038722 0.00000002111 0.2637657425157 0.9645867680386 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p791_15 : ‖exp (-((((((13791:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9385499872597:ℝ):ℂ) + ((0.3451433345943:ℝ):ℂ) * I)‖ ≤ 0.00000013045 := by
  have hl := lg_15
  refine (ecis_approx ((((13791:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.346720312645846043 37.346720333332373625 0.3523915 0.00000003044 0.9385499872597 0.3451433345943 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_2 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9671309755966):ℝ):ℂ) + ((0.2542787363939:ℝ):ℂ) * I)‖ ≤ 0.00000010707 := by
  have hl := lg_2
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.6818798144304 9.6818798214144 2.8844908 0.00000000706 (-0.9671309755966) 0.2542787363939 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_3 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9349965983671):ℝ):ℂ) + (((-0.354656680288):ℝ):ℂ) * I)‖ ≤ 0.00000013713 := by
  have hl := lg_3
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.345416444485234752 15.34541645146924872 (-2.7790458) 0.00000003712 (-0.9349965983671) (-0.354656680288) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_4 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8706846518334:ℝ):ℂ) + (((-0.491841678858):ℝ):ℂ) * I)‖ ≤ 0.00000012131 := by
  have hl := lg_4
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.3637596288608 19.3637596428288 (-0.5142037) 0.0000000213 0.8706846518334 (-0.491841678858) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_5 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8825773925295):ℝ):ℂ) + ((0.4701671469779:ℝ):ℂ) * I)‖ ≤ 0.00000013888 := by
  have hl := lg_5
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.480628753617671312 22.48062876758568528 2.6521125 0.00000003887 (-0.8825773925295) 0.4701671469779 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_6 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9944458250927:ℝ):ℂ) + ((0.1052497076275:ℝ):ℂ) * I)‖ ≤ 0.00000014418 := by
  have hl := lg_6
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.027296258915634752 25.02729627288364872 0.105445 0.00000004417 0.9944458250927 0.1052497076275 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_7 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4590587028904):ℝ):ℂ) + (((-0.8884059360989):ℝ):ℂ) * I)‖ ≤ 0.00000014001 := by
  have hl := lg_7
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.180472954742774496 27.180472968710802432 (-2.0477317) 0.00000004 (-0.4590587028904) (-0.8884059360989) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_8 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7170012161769):ℝ):ℂ) + ((0.697071915927:ℝ):ℂ) * I)‖ ≤ 0.00000012836 := by
  have hl := lg_8
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.0456394432912 29.0456394642432 2.3702871 0.00000002835 (-0.7170012161769) 0.697071915927 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_9 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.74843734921:ℝ):ℂ) + ((0.6632054993043:ℝ):ℂ) * I)‖ ≤ 0.00000014694 := by
  have hl := lg_9
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.690832888970469504 30.69083290293849744 0.7250936 0.00000004693 0.74843734921 0.6632054993043 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_10 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7340144315637:ℝ):ℂ) + (((-0.6791338706442):ℝ):ℂ) * I)‖ ≤ 0.00000015312 := by
  have hl := lg_10
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.162508568048071312 32.16250858900008528 (-0.746582) 0.00000005311 0.7340144315637 (-0.6791338706442) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_11 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4856252458396):ℝ):ℂ) + (((-0.8741671010725):ℝ):ℂ) * I)‖ ≤ 0.00000014462 := by
  have hl := lg_11
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.493801159554868944 33.49380118050689688 (-2.0778746) 0.00000004461 (-0.4856252458396) (-0.8741671010725) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_12 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9885221236051):ℝ):ℂ) + ((0.1510761753288:ℝ):ℂ) * I)‖ ≤ 0.00000015124 := by
  have hl := lg_12
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.709176073346034752 34.70917609429804872 2.9899358 0.00000005123 (-0.9885221236051) 0.1510761753288 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_13 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2965736417387):ℝ):ℂ) + ((0.9550099868714:ℝ):ℂ) * I)‖ ≤ 0.00000012896 := by
  have hl := lg_13
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.8272126141299856 35.827212635082013536 1.8718992 0.00000002895 (-0.2965736417387) 0.9550099868714 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_14 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6698726301817:ℝ):ℂ) + ((0.7424760328343:ℝ):ℂ) * I)‖ ≤ 0.00000014706 := by
  have hl := lg_14
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.862352769173174496 36.862352790125202432 0.8367591 0.00000004705 0.6698726301817 0.7424760328343 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p968_15 : ‖exp (-((((((13968:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9919547668155:ℝ):ℂ) + (((-0.1265928141407):ℝ):ℂ) * I)‖ ≤ 0.00000014499 := by
  have hl := lg_15
  refine (ecis_approx ((((13968:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.826045198102906064 37.826045219054934 (-0.1269334) 0.00000004498 0.9919547668155 (-0.1265928141407) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_2 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9398527870964):ℝ):ℂ) + ((0.3415797687334:ℝ):ℂ) * I)‖ ≤ 0.00000013494 := by
  have hl := lg_2
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.77337524223 9.77337524928 2.7929954 0.00000003493 (-0.9398527870964) 0.3415797687334 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_3 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.976433508921):ℝ):ℂ) + (((-0.2158184476661):ℝ):ℂ) * I)‖ ≤ 0.00000014782 := by
  have hl := lg_3
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.4904332665551124 15.4904332736051265 (-2.9240627) 0.00000004781 (-0.976433508921) (-0.2158184476661) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_4 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7666464634587:ℝ):ℂ) + (((-0.6420694666984):ℝ):ℂ) * I)‖ ≤ 0.00000013709 := by
  have hl := lg_4
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.54675048446 19.54675049856 (-0.6971946) 0.00000003708 0.7666464634587 (-0.6420694666984) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_5 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7636000361645):ℝ):ℂ) + ((0.6456895420651:ℝ):ℂ) * I)‖ ≤ 0.00000014339 := by
  have hl := lg_5
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.6930745579903469 22.693074572090361 2.4396667 0.00000004338 (-0.7636000361645) 0.6456895420651 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_6 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9914229704621:ℝ):ℂ) + (((-0.1306923625929):ℝ):ℂ) * I)‖ ≤ 0.00000011995 := by
  have hl := lg_6
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.2638085087851124 25.2638085228851265 (-0.1310673) 0.00000001994 0.9914229704621 (-0.1306923625929) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_7 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6696931886235):ℝ):ℂ) + (((-0.7426378882686):ℝ):ℂ) * I)‖ ≤ 0.00000013438 := by
  have hl := lg_7
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.4373330943494502 27.4373331084494784 (-2.3045919) 0.00000003437 (-0.6696931886235) (-0.7426378882686) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_8 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5012168754401):ℝ):ℂ) + ((0.8653216995821:ℝ):ℂ) * I)‖ ≤ 0.00000011196 := by
  have hl := lg_8
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.32012572669 29.32012574784 2.0958008 0.00000001195 (-0.5012168754401) 0.8653216995821 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_9 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9068447560429:ℝ):ℂ) + ((0.4214648128106:ℝ):ℂ) * I)‖ ≤ 0.00000011133 := by
  have hl := lg_9
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.9808665331102248 30.980866547210253 0.43506 0.00000001132 0.9068447560429 0.4214648128106 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_10 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4971170572103:ℝ):ℂ) + (((-0.8676834857427):ℝ):ℂ) * I)‖ ≤ 0.00000013569 := by
  have hl := lg_10
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.4664498002203469 32.466449821370361 (-1.0505233) 0.00000003568 0.4971170572103 (-0.8676834857427) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_11 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7335974045264):ℝ):ℂ) + (((-0.6795843200384):ℝ):ℂ) * I)‖ ≤ 0.00000012073 := by
  have hl := lg_11
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.8103233354613153 33.8103233566113435 (-2.3943968) 0.00000002072 (-0.7335974045264) (-0.6795843200384) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_12 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.88714977501):ℝ):ℂ) + ((0.4614816102477:ℝ):ℂ) * I)‖ ≤ 0.0000001291 := by
  have hl := lg_12
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.0371837510151124 35.0371837721651265 2.6619281 0.00000002909 (-0.88714977501) 0.4614816102477 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_13 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0374616591252:ℝ):ℂ) + ((0.9992980656918:ℝ):ℂ) * I)‖ ≤ 0.00000011388 := by
  have hl := lg_13
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.16578592921197 36.1657859503619982 1.5333259 0.00000001387 0.0374616591252 0.9992980656918 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_14 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8830830880712:ℝ):ℂ) + ((0.4692166445924:ℝ):ℂ) * I)‖ ≤ 0.00000011467 := by
  have hl := lg_14
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.2107083365794502 37.2107083577294784 0.4884035 0.00000001466 0.8830830880712 0.4692166445924 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p1_15 : ‖exp (-((((((14100:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8849563775687:ℝ):ℂ) + (((-0.4656739307718):ℝ):ℂ) * I)‖ ≤ 0.00000011855 := by
  have hl := lg_15
  refine (ecis_approx ((((14100:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.1835078245454593 38.1835078456954875 (-0.484396) 0.00000001854 0.8849563775687 (-0.4656739307718) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_2 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9047121518772):ℝ):ℂ) + ((0.4260233821326:ℝ):ℂ) * I)‖ ≤ 0.00000014434 := by
  have hl := lg_2
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.8648706700296 9.8648706771456 2.7014999 0.00000004433 (-0.9047121518772) 0.4260233821326 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_3 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9973720728389):ℝ):ℂ) + (((-0.0724496224542):ℝ):ℂ) * I)‖ ≤ 0.00000012575 := by
  have hl := lg_3
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.635450088624990048 15.63545009574100428 (-3.0690795) 0.00000002574 (-0.9973720728389) (-0.0724496224542) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_4 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6370082382608:ℝ):ℂ) + (((-0.7708569934741):ℝ):ℂ) * I)‖ ≤ 0.00000013277 := by
  have hl := lg_4
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.7297413400592 19.7297413542912 (-0.8801854) 0.00000003276 0.6370082382608 (-0.7708569934741) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_5 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6102883796585):ℝ):ℂ) + ((0.7921793317431:ℝ):ℂ) * I)‖ ≤ 0.00000014789 := by
  have hl := lg_5
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.905520362363022488 22.90552037659503672 2.2272209 0.00000004788 (-0.6102883796585) 0.7921793317431 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_6 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9331999037366:ℝ):ℂ) + (((-0.3593576765091):ℝ):ℂ) * I)‖ ≤ 0.00000014418 := by
  have hl := lg_6
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.500320758654590048 25.50032077288660428 (-0.3675795) 0.00000004417 0.9331999037366 (-0.3593576765091) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_7 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.836385560092):ℝ):ℂ) + (((-0.5481415828085):ℝ):ℂ) * I)‖ ≤ 0.00000011948 := by
  have hl := lg_7
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.694193233956125904 27.694193248188154368 (-2.561452) 0.00000001947 (-0.836385560092) (-0.5481415828085) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_8 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2479059904728):ℝ):ℂ) + ((0.968784093535:ℝ):ℂ) * I)‖ ≤ 0.00000012582 := by
  have hl := lg_8
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.5946120100888 29.5946120314368 1.8213145 0.00000002581 (-0.2479059904728) 0.968784093535 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_9 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9895020909274:ℝ):ℂ) + ((0.1445185526161:ℝ):ℂ) * I)‖ ≤ 0.0000001556 := by
  have hl := lg_9
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.270900177249980096 31.27090019148200856 0.1450264 0.00000005559 0.9895020909274 0.1445185526161 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_10 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2146484020421:ℝ):ℂ) + (((-0.9766913860072):ℝ):ℂ) * I)‖ ≤ 0.00000011786 := by
  have hl := lg_10
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.770391032392622488 32.77039105374063672 (-1.3544645) 0.00000001785 0.2146484020421 (-0.9766913860072) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_11 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9086847168966):ℝ):ℂ) + (((-0.4174830357651):ℝ):ℂ) * I)‖ ≤ 0.00000012455 := by
  have hl := lg_11
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.126845511367761656 34.12684553271579012 (-2.710919) 0.00000002454 (-0.9086847168966) (-0.4174830357651) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_12 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.691182520307):ℝ):ℂ) + ((0.7226802360656:ℝ):ℂ) * I)‖ ≤ 0.00000011441 := by
  have hl := lg_12
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.365191428684190048 35.36519145003220428 2.3339204 0.0000000144 (-0.691182520307) 0.7226802360656 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_13 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3672435251452:ℝ):ℂ) + ((0.9301248266974:ℝ):ℂ) * I)‖ ≤ 0.00000012258 := by
  have hl := lg_13
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.5043592442939544 36.504359265641982864 1.1947526 0.00000002257 0.3672435251452 0.9301248266974 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_14 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9902093109615:ℝ):ℂ) + ((0.1395905458304:ℝ):ℂ) * I)‖ ≤ 0.00000013911 := by
  have hl := lg_14
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.559063903985725904 37.559063925333754368 0.1400479 0.0000000391 0.9902093109615 0.1395905458304 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p232_15 : ‖exp (-((((((14232:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6660776800959:ℝ):ℂ) + (((-0.7458823795198):ℝ):ℂ) * I)‖ ≤ 0.00000012927 := by
  have hl := lg_15
  refine (ecis_approx ((((14232:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.540970450988012536 38.540970472336041 (-0.8418586) 0.00000002926 0.6660776800959 (-0.7458823795198) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_2 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8620031181411):ℝ):ℂ) + ((0.5069029731941:ℝ):ℂ) * I)‖ ≤ 0.00000011654 := by
  have hl := lg_2
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.9563660978292 9.9563661050112 2.6100045 0.00000001653 (-0.8620031181411) 0.5069029731941 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_3 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9973727610653):ℝ):ℂ) + ((0.0724401474162:ℝ):ℂ) * I)‖ ≤ 0.00000011086 := by
  have hl := lg_3
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.780466910694867696 15.78046691787688206 3.069089 0.00000001085 (-0.9973727610653) 0.0724401474162 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_4 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4860987577169:ℝ):ℂ) + (((-0.8739038835857):ℝ):ℂ) * I)‖ ≤ 0.0000001259 := by
  have hl := lg_4
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.9127321956584 19.9127322100224 (-1.0631763) 0.00000002589 0.4860987577169 (-0.8739038835857) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_5 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4295358858012):ℝ):ℂ) + ((0.9030497897708:ℝ):ℂ) * I)‖ ≤ 0.0000001524 := by
  have hl := lg_5
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.117966166735698076 23.11796618109971244 2.0147751 0.00000005239 (-0.4295358858012) 0.9030497897708 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_6 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.823018308068:ℝ):ℂ) + (((-0.5680148453913):ℝ):ℂ) * I)‖ ≤ 0.00000012021 := by
  have hl := lg_6
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.736833008524067696 25.73683302288808206 (-0.6040918) 0.0000000202 0.823018308068 (-0.5680148453913) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_7 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9481983913251):ℝ):ℂ) + (((-0.3176787850797):ℝ):ℂ) * I)‖ ≤ 0.00000015517 := by
  have hl := lg_7
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.951053373562801608 27.951053387926830336 (-2.8183122) 0.00000005516 (-0.9481983913251) (-0.3176787850797) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_8 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0239658320281:ℝ):ℂ) + ((0.9997127781993:ℝ):ℂ) * I)‖ ≤ 0.00000014243 := by
  have hl := lg_8
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.8690982934876 29.8690983150336 1.5468282 0.00000004242 0.0239658320281 0.9997127781993 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_9 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9895048510513:ℝ):ℂ) + (((-0.1444996530998):ℝ):ℂ) * I)‖ ≤ 0.00000011452 := by
  have hl := lg_9
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.560933821389735392 31.56093383575376412 (-0.1450073) 0.00000001451 0.9895048510513 (-0.1444996530998) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_10 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0874973433438):ℝ):ℂ) + (((-0.9961647528935):ℝ):ℂ) * I)‖ ≤ 0.00000015023 := by
  have hl := lg_10
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.074332264564898076 33.07433228611091244 (-1.6584057) 0.00000005022 (-0.0874973433438) (-0.9961647528935) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_11 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.993491794353):ℝ):ℂ) + (((-0.1139037053921):ℝ):ℂ) * I)‖ ≤ 0.00000014864 := by
  have hl := lg_11
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.443367687274208012 34.44336770882023674 (-3.0274412) 0.00000004863 (-0.993491794353) (-0.1139037053921) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_12 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4215159338864):ℝ):ℂ) + ((0.9068209952775:ℝ):ℂ) * I)‖ ≤ 0.00000013674 := by
  have hl := lg_12
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.693199106353267696 35.69319912789928206 2.0059127 0.00000003673 (-0.4215159338864) 0.9068209952775 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_13 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6553281881463:ℝ):ℂ) + ((0.7553442697346:ℝ):ℂ) * I)‖ ≤ 0.00000013786 := by
  have hl := lg_13
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.8429325593759388 36.842932580921967528 0.8561793 0.00000003785 0.6553281881463 0.7553442697346 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_14 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9783823114438:ℝ):ℂ) + (((-0.206804382579):ℝ):ℂ) * I)‖ ≤ 0.00000014988 := by
  have hl := lg_14
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.907419471392001608 37.907419492938030336 (-0.2083076) 0.00000004987 0.9783823114438 (-0.206804382579) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p364_15 : ‖exp (-((((((14364:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.362990339078:ℝ):ℂ) + (((-0.9317929028148):ℝ):ℂ) * I)‖ ≤ 0.00000015591 := by
  have hl := lg_15
  refine (ecis_approx ((((14364:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.898433077430565772 38.8984330989765945 (-1.1993212) 0.0000000559 0.362990339078 (-0.9317929028148) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_2 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8120829371368):ℝ):ℂ) + ((0.5835420320398:ℝ):ℂ) * I)‖ ≤ 0.00000011853 := by
  have hl := lg_2
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.0478615256288 10.0478615328768 2.5185091 0.00000001852 (-0.8120829371368) 0.5835420320398 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_3 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9764355591522):ℝ):ℂ) + ((0.2158091715381:ℝ):ℂ) * I)‖ ≤ 0.00000011849 := by
  have hl := lg_3
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.925483732764745344 15.92548374001275984 2.9240722 0.00000001848 (-0.9764355591522) 0.2158091715381 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_4 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3189574004198:ℝ):ℂ) + (((-0.947769052416):ℝ):ℂ) * I)‖ ≤ 0.00000014423 := by
  have hl := lg_4
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.0957230512576 20.0957230657536 (-1.2461671) 0.00000004422 0.3189574004198 (-0.947769052416) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_5 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2294698595706):ℝ):ℂ) + ((0.9733157676456:ℝ):ℂ) * I)‖ ≤ 0.0000001569 := by
  have hl := lg_5
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.330411971108373664 23.33041198560438816 1.8023293 0.00000005689 (-0.2294698595706) 0.9733157676456 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_6 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6670129396736:ℝ):ℂ) + (((-0.7450461316643):ℝ):ℂ) * I)‖ ≤ 0.00000014419 := by
  have hl := lg_6
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.973345258393545344 25.97334527288955984 (-0.840604) 0.00000004418 0.6670129396736 (-0.7450461316643) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_7 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9977949788905):ℝ):ℂ) + (((-0.0663715267389):ℝ):ℂ) * I)‖ ≤ 0.00000011556 := by
  have hl := lg_7
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.207913513169477312 28.207913527665506304 (-3.0751723) 0.00000001555 (-0.9977949788905) (-0.0663715267389) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_8 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.294043311801:ℝ):ℂ) + ((0.9557920960047:ℝ):ℂ) * I)‖ ≤ 0.00000015903 := by
  have hl := lg_8
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.1435845768864 30.1435845986304 1.2723419 0.00000005902 0.294043311801 0.9557920960047 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_9 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9068528058554:ℝ):ℂ) + (((-0.4214474919989):ℝ):ℂ) * I)‖ ≤ 0.00000014414 := by
  have hl := lg_9
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.850967465529490688 31.85096748002551968 (-0.4350409) 0.00000004413 0.9068528058554 (-0.4214474919989) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_10 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3816221891467):ℝ):ℂ) + (((-0.9243184000916):ℝ):ℂ) * I)‖ ≤ 0.00000013918 := by
  have hl := lg_10
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.378273496737173664 33.37827351848118816 (-1.962347) 0.00000003917 (-0.3816221891467) (-0.9243184000916) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_11 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9795928480036):ℝ):ℂ) + ((0.2009921685501:ℝ):ℂ) * I)‖ ≤ 0.00000014186 := by
  have hl := lg_11
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.759889863180654368 34.75988988492468336 2.939222 0.00000004185 (-0.9795928480036) 0.2009921685501 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_12 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.106903994082):ℝ):ℂ) + ((0.9942693478373:ℝ):ℂ) * I)‖ ≤ 0.00000015907 := by
  have hl := lg_12
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.021206784022345344 36.02120680576635984 1.677905 0.00000005906 (-0.106903994082) 0.9942693478373 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_13 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8690062227543:ℝ):ℂ) + ((0.4948011568441:ℝ):ℂ) * I)‖ ≤ 0.00000015314 := by
  have hl := lg_13
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.1815058744579232 37.181505896201952192 0.517606 0.00000005313 0.8690062227543 0.4948011568441 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_14 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8490228530654:ℝ):ℂ) + (((-0.5283561251397):ℝ):ℂ) * I)‖ ≤ 0.00000011748 := by
  have hl := lg_14
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.255775038798277312 38.255775060542306304 (-0.5566632) 0.00000001747 0.8490228530654 (-0.5283561251397) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p496_15 : ‖exp (-((((((14496:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0140119682471:ℝ):ℂ) + (((-0.9999018275539):ℝ):ℂ) * I)‖ ≤ 0.00000013922 := by
  have hl := lg_15
  refine (ecis_approx ((((14496:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.255895703873119008 39.255895725617148 (-1.5567839) 0.00000003921 0.0140119682471 (-0.9999018275539) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_2 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7345652027319):ℝ):ℂ) + ((0.6785381071872:ℝ):ℂ) * I)‖ ≤ 0.00000013783 := by
  have hl := lg_2
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.1705485765419 10.1705485838784 2.395822 0.00000003782 (-0.7345652027319) 0.6785381071872 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_3 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9163318398166):ℝ):ℂ) + ((0.4004197287857:ℝ):ℂ) * I)‖ ≤ 0.00000011374 := by
  have hl := lg_3
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.119938107812990372 16.119938115149505045 2.7296178 0.00000001373 (-0.9163318398166) 0.4004197287857 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_4 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0791721809862:ℝ):ℂ) + (((-0.9968609560805):ℝ):ℂ) * I)‖ ≤ 0.00000014623 := by
  have hl := lg_4
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.3410971530838 20.3410971677568 (-1.4915412) 0.00000004622 0.0791721809862 (-0.9968609560805) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_5 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0533123403346:ℝ):ℂ) + ((0.9985778859798:ℝ):ℂ) * I)‖ ≤ 0.00000014722 := by
  have hl := lg_5
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.615282481517188657 23.61528249619020333 1.5174587 0.00000004721 0.0533123403346 0.9985778859798 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_6 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4014054453889:ℝ):ℂ) + (((-0.9159004686166):ℝ):ℂ) * I)‖ ≤ 0.00000014438 := by
  have hl := lg_6
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.290486684354890372 26.290486699027905045 (-1.1577455) 0.00000004437 0.4014054453889 (-0.9159004686166) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_7 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9616046480492):ℝ):ℂ) + ((0.2744385188191:ℝ):ℂ) * I)‖ ≤ 0.00000012645 := by
  have hl := lg_7
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.552339609460247006 28.552339624133276352 2.8635869 0.00000002644 (-0.9616046480492) 0.2744385188191 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_8 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6182510171076:ℝ):ℂ) + ((0.7859807121332:ℝ):ℂ) * I)‖ ≤ 0.00000011575 := by
  have hl := lg_8
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.5116457296257 30.5116457516352 0.9042808 0.00000001574 0.6182510171076 0.7859807121332 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_9 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6793280867494:ℝ):ℂ) + (((-0.7338346888458):ℝ):ℂ) * I)‖ ≤ 0.00000012029 := by
  have hl := lg_9
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.239876215625980744 32.23987623029901009 (-0.8239497) 0.00000002028 0.6793280867494 (-0.7338346888458) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_10 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.71673446399):ℝ):ℂ) + (((-0.697346189566):ℝ):ℂ) * I)‖ ≤ 0.00000014419 := by
  have hl := lg_10
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.785831058059088657 33.78583108006860333 (-2.3699045) 0.00000004418 (-0.71673446399) (-0.697346189566) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_11 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8099097142331):ℝ):ℂ) + ((0.5865545624557:ℝ):ℂ) * I)‖ ≤ 0.00000011676 := by
  have hl := lg_11
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.184317326327934709 35.184317348337464055 2.5147945 0.00000001675 (-0.8099097142331) 0.5865545624557 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_12 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3266148034752:ℝ):ℂ) + ((0.9451575372132:ℝ):ℂ) * I)‖ ≤ 0.00000013984 := by
  have hl := lg_12
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.461035260896790372 36.461035282906305045 1.2380766 0.00000003983 0.3266148034752 0.9451575372132 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_13 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9979775723811:ℝ):ℂ) + ((0.0635670120759:ℝ):ℂ) * I)‖ ≤ 0.0000001325 := by
  have hl := lg_13
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.6355019105905841 37.635501932600113446 0.0636099 0.00000003249 0.9979775723811 0.0635670120759 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_14 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5201443262581:ℝ):ℂ) + (((-0.854078380397):ℝ):ℂ) * I)‖ ≤ 0.00000015709 := by
  have hl := lg_14
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.722888186002147006 38.722888208011676352 (-1.0237764) 0.00000005708 0.5201443262581 (-0.854078380397) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p673_15 : ‖exp (-((((((14673:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4487020748386):ℝ):ℂ) + (((-0.8936814018603):ℝ):ℂ) * I)‖ ≤ 0.00000015376 := by
  have hl := lg_15
  refine (ecis_approx ((((14673:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.735220589330179029 39.735220611339708375 (-2.0361088) 0.00000005375 (-0.4487020748386) (-0.8936814018603) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p909_2 : ‖exp (-((((((14909:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6142561508919):ℝ):ℂ) + ((0.7891066981583:ℝ):ℂ) * I)‖ ≤ 0.0000001042 := by
  have hl := lg_2
  refine (ecis_approx ((((14909:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.3341313110927 10.3341313185472 2.2322393 0.00000000419 (-0.6142561508919) 0.7891066981583 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p909_3 : ‖exp (-((((((14909:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7830464672028):ℝ):ℂ) + ((0.6219632064342:ℝ):ℂ) * I)‖ ≤ 0.00000011368 := by
  have hl := lg_3
  refine (ecis_approx ((((14909:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.379210607877317076 16.379210615331831985 2.4703453 0.00000001367 (-0.7830464672028) 0.6219632064342 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p909_4 : ‖exp (-((((((14909:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2453787552203):ℝ):ℂ) + (((-0.9694272878795):ℝ):ℂ) * I)‖ ≤ 0.00000011557 := by
  have hl := lg_4
  refine (ecis_approx ((((14909:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.6682626221854 20.6682626370944 (-1.8187067) 0.00000001556 (-0.2453787552203) (-0.9694272878795) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p909_5 : ‖exp (-((((((14909:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4197455198373:ℝ):ℂ) + ((0.9076418338621:ℝ):ℂ) * I)‖ ≤ 0.00000011493 := by
  have hl := lg_5
  refine (ecis_approx ((((14909:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.995109828728941981 23.99510984363795689 1.1376314 0.00000001492 0.4197455198373 0.9076418338621 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p909_6 : ‖exp (-((((((14909:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0098042161305):ℝ):ℂ) + (((-0.9999519375179):ℝ):ℂ) * I)‖ ≤ 0.00000010976 := by
  have hl := lg_6
  refine (ecis_approx ((((14909:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.713341918970017076 26.713341933879031985 (-1.5806007) 0.00000000975 (-0.0098042161305) (-0.9999519375179) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p909_7 : ‖exp (-((((((14909:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7403264061713):ℝ):ℂ) + ((0.6722475825869:ℝ):ℂ) * I)‖ ≤ 0.0000001314 := by
  have hl := lg_7
  refine (ecis_approx ((((14909:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.011574404514606598 29.011574419423636416 2.4043521 0.00000003139 (-0.7403264061713) 0.6722475825869 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p909_8 : ‖exp (-((((((14909:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9157069759434:ℝ):ℂ) + ((0.401846655092:ℝ):ℂ) * I)‖ ≤ 0.00000011976 := by
  have hl := lg_8
  refine (ecis_approx ((((14909:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.0023939332781 31.0023939556416 0.4135326 0.00000001975 0.9157069759434 0.401846655092 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p909_9 : ‖exp (-((((((14909:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2263235466169:ℝ):ℂ) + (((-0.9740521814804):ℝ):ℂ) * I)‖ ≤ 0.00000012016 := by
  have hl := lg_9
  refine (ecis_approx ((((14909:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.758421215754634152 32.75842123066366397 (-1.3424947) 0.00000002015 0.2263235466169 (-0.9740521814804) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p909_10 : ‖exp (-((((((14909:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9740575162657):ℝ):ℂ) + (((-0.2263005848766):ℝ):ℂ) * I)‖ ≤ 0.0000001263 := by
  have hl := lg_10
  refine (ecis_approx ((((14909:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.329241139821641981 34.32924116218515689 (-2.9133146) 0.00000002629 (-0.9740575162657) (-0.2263005848766) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p224_2 : ‖exp (-((((((15224:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4287435653676):ℝ):ℂ) + ((0.9034262311622:ℝ):ℂ) * I)‖ ≤ 0.00000014149 := by
  have hl := lg_2
  refine (ecis_approx ((((15224:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.5524726728872 10.5524726804992 2.0138979 0.00000004148 (-0.4287435653676) 0.9034262311622 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p224_3 : ‖exp (-((((((15224:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5256560097749):ℝ):ℂ) + ((0.8506972195677:ℝ):ℂ) * I)‖ ≤ 0.00000014283 := by
  have hl := lg_3
  refine (ecis_approx ((((15224:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.725273478725888736 16.72527348633790396 2.1242824 0.00000004282 (-0.5256560097749) 0.8506972195677 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p224_4 : ‖exp (-((((((15224:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.632357827281):ℝ):ℂ) + (((-0.7746764345593):ℝ):ℂ) * I)‖ ≤ 0.00000013947 := by
  have hl := lg_4
  refine (ecis_approx ((((15224:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.1049453457744 21.1049453609984 (-2.2553894) 0.00000003946 (-0.632357827281) (-0.7746764345593) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p224_5 : ‖exp (-((((((15224:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8076393813277:ℝ):ℂ) + ((0.5896767162849:ℝ):ℂ) * I)‖ ≤ 0.0000001575 := by
  have hl := lg_5
  refine (ecis_approx ((((15224:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.502082770981917816 24.50208278620593304 0.6306585 0.00000005749 0.8076393813277 0.5896767162849 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p224_6 : ‖exp (-((((((15224:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5431704611612):ℝ):ℂ) + (((-0.8396224449797):ℝ):ℂ) * I)‖ ≤ 0.00000013813 := by
  have hl := lg_6
  refine (ecis_approx ((((15224:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.277746151613088736 27.27774616683710396 (-2.1450049) 0.00000003812 (-0.5431704611612) (-0.8396224449797) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p224_7 : ‖exp (-((((((15224:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2188093390633):ℝ):ℂ) + ((0.9757676327578:ℝ):ℂ) * I)‖ ≤ 0.00000013461 := by
  have hl := lg_7
  refine (ecis_approx ((((15224:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.624536101303264528 29.624536116527294976 1.7913904 0.0000000346 (-0.2188093390633) 0.9757676327578 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p224_8 : ‖exp (-((((((15224:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9709823611106:ℝ):ℂ) + (((-0.2391511120862):ℝ):ℂ) * I)‖ ≤ 0.00000011725 := by
  have hl := lg_8
  refine (ecis_approx ((((15224:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.6574180186616 31.6574180414976 (-0.2414915) 0.00000001724 0.9709823611106 (-0.2391511120862) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p224_9 : ‖exp (-((((((15224:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4473714229187):ℝ):ℂ) + (((-0.8943482598805):ℝ):ℂ) * I)‖ ≤ 0.00000013679 := by
  have hl := lg_9
  refine (ecis_approx ((((15224:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.450546957451777472 33.45054697267580792 (-2.0346204) 0.00000003678 (-0.4473714229187) (-0.8943482598805) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p224_10 : ‖exp (-((((((15224:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8789996012544):ℝ):ℂ) + ((0.4768225046066:ℝ):ℂ) * I)‖ ≤ 0.00000012364 := by
  have hl := lg_10
  refine (ecis_approx ((((15224:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.054555443869117816 35.05455546670513304 2.6445564 0.00000002363 (-0.8789996012544) 0.4768225046066 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p645_2 : ‖exp (-((((((15645:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1507102336751):ℝ):ℂ) + ((0.9885779814789:ℝ):ℂ) * I)‖ ≤ 0.00000012927 := by
  have hl := lg_2
  refine (ecis_approx ((((15645:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.8442876357935 10.844287643616 1.722083 0.00000002926 (-0.1507102336751) 0.9885779814789 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p645_3 : ‖exp (-((((((15645:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0908449525762):ℝ):ℂ) + ((0.9958650483831:ℝ):ℂ) * I)‖ ≤ 0.00000013844 := by
  have hl := lg_3
  refine (ecis_approx ((((15645:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.18778925214572578 17.187789259968241425 1.6617667 0.00000003843 (-0.0908449525762) 0.9958650483831 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p645_4 : ‖exp (-((((((15645:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9545728785112):ℝ):ℂ) + (((-0.2979775484742):ℝ):ℂ) * I)‖ ≤ 0.00000014997 := by
  have hl := lg_4
  refine (ecis_approx ((((15645:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.688575271587 21.688575287232 (-2.8390194) 0.00000004996 (-0.9545728785112) (-0.2979775484742) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p645_5 : ‖exp (-((((((15645:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9988996979157:ℝ):ℂ) + (((-0.0468976918834):ℝ):ℂ) * I)‖ ≤ 0.00000011884 := by
  have hl := lg_5
  refine (ecis_approx ((((15645:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.179656131897799805 25.17965614754281545 (-0.0469149) 0.00000001883 0.9988996979157 (-0.0468976918834) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p645_6 : ‖exp (-((((((15645:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9707990174852):ℝ):ℂ) + (((-0.2398942837473):ℝ):ℂ) * I)‖ ≤ 0.00000014079 := by
  have hl := lg_6
  refine (ecis_approx ((((15645:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.03207688793922578 28.032076903584241425 (-2.8993357) 0.00000004078 (-0.9707990174852) (-0.2398942837473) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p645_7 : ‖exp (-((((((15645:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5635145606322:ℝ):ℂ) + ((0.8261061311693:ℝ):ℂ) * I)‖ ≤ 0.0000001536 := by
  have hl := lg_7
  refine (ecis_approx ((((15645:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.44376427383667719 30.44376428948170848 0.9721623 0.00000005359 0.5635145606322 0.8261061311693 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p645_8 : ‖exp (-((((((15645:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.438437945099:ℝ):ℂ) + (((-0.8987614635137):ℝ):ℂ) * I)‖ ≤ 0.00000012853 := by
  have hl := lg_8
  refine (ecis_approx ((((15645:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.5328629073805 32.532862930848 (-1.1169364) 0.00000002852 0.438437945099 (-0.8987614635137) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p645_9 : ‖exp (-((((((15645:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.983494405832):ℝ):ℂ) + (((-0.1809385347259):ℝ):ℂ) * I)‖ ≤ 0.00000013162 := by
  have hl := lg_9
  refine (ecis_approx ((((15645:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.37557850429145156 34.37557851993648285 (-2.959652) 0.00000003161 (-0.983494405832) (-0.1809385347259) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p645_10 : ‖exp (-((((((15645:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1041823813127):ℝ):ℂ) + ((0.994558209168:ℝ):ℂ) * I)‖ ≤ 0.0000001481 := by
  have hl := lg_10
  refine (ecis_approx ((((15645:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.023943767691299805 36.02394379115881545 1.6751681 0.00000004809 (-0.1041823813127) 0.994558209168 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p066_2 : ‖exp (-((((((16066:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1400662527881:ℝ):ℂ) + ((0.9901421336504:ℝ):ℂ) * I)‖ ≤ 0.00000011567 := by
  have hl := lg_2
  refine (ecis_approx ((((16066:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.1361025986998 11.1361026067328 1.430268 0.00000001566 0.1400662527881 0.9901421336504 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p066_3 : ‖exp (-((((((16066:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.363055843222:ℝ):ℂ) + ((0.9317673822915:ℝ):ℂ) * I)‖ ≤ 0.00000011207 := by
  have hl := lg_3
  refine (ecis_approx ((((16066:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.650305025565562824 17.65030503359857889 1.1992509 0.00000001206 0.363055843222 0.9317673822915 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p066_4 : ‖exp (-((((((16066:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9607628895719):ℝ):ℂ) + ((0.2773709966556:ℝ):ℂ) * I)‖ ≤ 0.00000013133 := by
  have hl := lg_4
  refine (ecis_approx ((((16066:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.2722051973996 22.2722052134656 2.860536 0.00000003132 (-0.9607628895719) 0.2773709966556 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p066_5 : ‖exp (-((((((16066:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.748838650365:ℝ):ℂ) + (((-0.6627523487092):ℝ):ℂ) * I)‖ ≤ 0.00000013592 := by
  have hl := lg_5
  refine (ecis_approx ((((16066:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.857229492813681794 25.85722950887969786 (-0.7244883) 0.00000003591 0.748838650365 (-0.6627523487092) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p066_6 : ‖exp (-((((((16066:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8717302724313):ℝ):ℂ) + ((0.489986052901:ℝ):ℂ) * I)‖ ≤ 0.00000011165 := by
  have hl := lg_6
  refine (ecis_approx ((((16066:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.786407624265362824 28.78640764033137889 2.6295189 0.00000001164 (-0.8717302724313) 0.489986052901 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p066_7 : ‖exp (-((((((16066:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9883283560069:ℝ):ℂ) + ((0.152338638279:ℝ):ℂ) * I)‖ ≤ 0.00000012655 := by
  have hl := lg_7
  refine (ecis_approx ((((16066:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.262992446370089852 31.262992462436121984 0.1529341 0.00000002654 0.9883283560069 0.152338638279 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p066_8 : ‖exp (-((((((16066:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4092071617824):ℝ):ℂ) + (((-0.9124415042853):ℝ):ℂ) * I)‖ ≤ 0.00000013981 := by
  have hl := lg_8
  refine (ecis_approx ((((16066:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.4083077960994 33.4083078201984 (-1.9923813) 0.0000000398 (-0.4092071617824) (-0.9124415042853) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p066_9 : ‖exp (-((((((16066:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7363809093998):ℝ):ℂ) + ((0.6765671853119:ℝ):ℂ) * I)‖ ≤ 0.00000012413 := by
  have hl := lg_9
  refine (ecis_approx ((((16066:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.300610051131125648 35.30061006719715778 2.3985018 0.00000002412 (-0.7363809093998) 0.6765671853119 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p066_10 : ‖exp (-((((((16066:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7611060483323:ℝ):ℂ) + ((0.6486274610221:ℝ):ℂ) * I)‖ ≤ 0.00000015158 := by
  have hl := lg_10
  refine (ecis_approx ((((16066:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.993332091513481794 36.99333211561249786 0.7057797 0.00000005157 0.7611060483323 0.6486274610221 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
