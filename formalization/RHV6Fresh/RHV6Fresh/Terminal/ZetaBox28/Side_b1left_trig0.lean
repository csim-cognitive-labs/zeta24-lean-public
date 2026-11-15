/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
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
namespace H28

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

lemma cs_b1left_vm0p92_2 : ‖exp (-((((((-920:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8034699232432:ℝ):ℂ) + ((0.5953453472092:ℝ):ℂ) * I)‖ ≤ 0.00000010635 := by
  have hl := lg_2
  refine (ecis_approx ((((-920:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.637695406336) (-0.637695405876) 0.6376954 0.00000000634 0.8034699232432 0.5953453472092 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p92_3 : ‖exp (-((((((-920:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5312480688297:ℝ):ℂ) + ((0.8472163179288:ℝ):ℂ) * I)‖ ≤ 0.00000010581 := by
  have hl := lg_3
  refine (ecis_approx ((((-920:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-1.0107233057955118) (-1.01072330533551088) 1.0107233 0.0000000058 0.5312480688297 0.8472163179288 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p92_4 : ‖exp (-((((((-920:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2911278351128:ℝ):ℂ) + ((0.9566841608507:ℝ):ℂ) * I)‖ ≤ 0.00000011269 := by
  have hl := lg_4
  refine (ecis_approx ((((-920:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-1.275390812672) (-1.275390811752) 1.2753908 0.00000001268 0.2911278351128 0.9566841608507 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p92_5 : ‖exp (-((((((-920:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0899915163459:ℝ):ℂ) + ((0.9959425319694:ℝ):ℂ) * I)‖ ≤ 0.00000012105 := by
  have hl := lg_5
  refine (ecis_approx ((((-920:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-1.4806828798810732) (-1.48068287896107228) 1.4806829 0.00000002104 0.0899915163459 0.9959425319694 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p683_2 : ‖exp (-((((((-683:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8900144340204:ℝ):ℂ) + ((0.4559323494065:ℝ):ℂ) * I)‖ ≤ 0.0000001245 := by
  have hl := lg_2
  refine (ecis_approx ((((-683:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.4734195244864) (-0.4734195241449) 0.4734195 0.00000002449 0.8900144340204 0.4559323494065 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p683_3 : ‖exp (-((((((-683:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7314487503264:ℝ):ℂ) + ((0.6818964185607:ℝ):ℂ) * I)‖ ≤ 0.00000010703 := by
  have hl := lg_3
  refine (ecis_approx ((((-683:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.750352193324276695) (-0.750352192982776012) 0.7503522 0.00000000702 0.7314487503264 0.6818964185607 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p683_4 : ‖exp (-((((((-683:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5842513855293:ℝ):ℂ) + ((0.8115727438173:ℝ):ℂ) * I)‖ ≤ 0.00000014899 := by
  have hl := lg_4
  refine (ecis_approx ((((-683:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.9468390489728) (-0.9468390482898) 0.946839 0.00000004898 0.5842513855293 0.8115727438173 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p683_5 : ‖exp (-((((((-683:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4542678736866:ℝ):ℂ) + ((0.8908651407123:ℝ):ℂ) * I)‖ ≤ 0.00000010618 := by
  have hl := lg_5
  refine (ecis_approx ((((-683:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-1.09924609452040543) (-1.099246093837404747) 1.0992461 0.00000000617 0.4542678736866 0.8908651407123 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p454_2 : ‖exp (-((((((-454:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9508927477582:ℝ):ℂ) + ((0.3095205683971:ℝ):ℂ) * I)‖ ≤ 0.0000001201 := by
  have hl := lg_2
  refine (ecis_approx ((((-454:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.3146888200832) (-0.3146888198562) 0.3146888 0.00000002009 0.9508927477582 0.3095205683971 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p454_3 : ‖exp (-((((((-454:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8781715913069:ℝ):ℂ) + ((0.4783457496639:ℝ):ℂ) * I)‖ ≤ 0.00000012108 := by
  have hl := lg_3
  refine (ecis_approx ((((-454:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.49876997916430691) (-0.498769978937306456) 0.49877 0.00000002107 0.8781715913069 0.4783457496639 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p454_4 : ‖exp (-((((((-454:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8083940354783:ℝ):ℂ) + ((0.5886417275416:ℝ):ℂ) * I)‖ ≤ 0.00000014018 := by
  have hl := lg_4
  refine (ecis_approx ((((-454:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.6293776401664) (-0.6293776397124) 0.6293776 0.00000004017 0.8083940354783 0.5886417275416 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p454_5 : ‖exp (-((((((-454:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7447175553294:ℝ):ℂ) + ((0.6673797740299:ℝ):ℂ) * I)‖ ≤ 0.00000011248 := by
  have hl := lg_5
  refine (ecis_approx ((((-454:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.73068481246305134) (-0.730684812009050886) 0.7306848 0.00000001247 0.7447175553294 0.6673797740299 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p286_2 : ‖exp (-((((((-286:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9804146980618:ℝ):ℂ) + ((0.1969442048511:ℝ):ℂ) * I)‖ ≤ 0.00000010645 := by
  have hl := lg_2
  refine (ecis_approx ((((-286:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.1982400937088) (-0.1982400935658) 0.1982401 0.00000000644 0.9804146980618 0.1969442048511 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p286_3 : ‖exp (-((((((-286:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9510429697324:ℝ):ℂ) + ((0.309058683299:ℝ):ℂ) * I)‖ ≤ 0.00000011464 := by
  have hl := lg_3
  refine (ecis_approx ((((-286:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.31420311462773519) (-0.314203114484734904) 0.3142031 0.00000001463 0.9510429697324 0.309058683299 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p286_4 : ‖exp (-((((((-286:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9224259603512:ℝ):ℂ) + ((0.3861739862682:ℝ):ℂ) * I)‖ ≤ 0.00000011288 := by
  have hl := lg_4
  refine (ecis_approx ((((-286:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.3964801874176) (-0.3964801871316) 0.3964802 0.00000001287 0.9224259603512 0.3861739862682 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p286_5 : ‖exp (-((((((-286:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8959196281463:ℝ):ℂ) + ((0.4442161859975:ℝ):ℂ) * I)‖ ≤ 0.00000014311 := by
  have hl := lg_5
  refine (ecis_approx ((((-286:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.46029924309346406) (-0.460299242807463774) 0.4602992 0.0000000431 0.8959196281463 0.4442161859975 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p066_2 : ‖exp (-((((((-66:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9989537564609:ℝ):ℂ) + ((0.0457317444751:ℝ):ℂ) * I)‖ ≤ 0.00000011395 := by
  have hl := lg_2
  refine (ecis_approx ((((-66:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.0457477139328) (-0.0457477138998) 0.0457477 0.00000001394 0.9989537564609 0.0457317444751 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p066_3 : ‖exp (-((((((-66:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.99737241747:ℝ):ℂ) + ((0.0724448816:ℝ):ℂ) * I)‖ ≤ 0.00000011108 := by
  have hl := lg_3
  refine (ecis_approx ((((-66:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.07250841106793889) (-0.072508411034938824) 0.0725084 0.00000001107 0.99737241747 0.0724448816 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p066_4 : ‖exp (-((((((-66:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9958172150945:ℝ):ℂ) + ((0.0913677958657:ℝ):ℂ) * I)‖ ≤ 0.00000012788 := by
  have hl := lg_4
  refine (ecis_approx ((((-66:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.0914954278656) (-0.0914954277996) 0.0914954 0.00000002787 0.9958172150945 0.0913677958657 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_vm0p066_5 : ‖exp (-((((((-66:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9943636504697:ℝ):ℂ) + ((0.106023255112:ℝ):ℂ) * I)‖ ≤ 0.00000010227 := by
  have hl := lg_5
  refine (ecis_approx ((((-66:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.10622290225233786) (-0.106222902186337794) 0.1062229 0.00000000226 0.9943636504697 0.106023255112 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p17_2 : ‖exp (-((((((170:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9930654858224:ℝ):ℂ) + (((-0.1175624977125):ℝ):ℂ) * I)‖ ≤ 0.00000012075 := by
  have hl := lg_2
  refine (ecis_approx ((((170:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.117835020651 0.117835020736 (-0.117835) 0.00000002074 0.9930654858224 (-0.1175624977125) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p17_3 : ‖exp (-((((((170:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9826102212463:ℝ):ℂ) + (((-0.1856802442432):ℝ):ℂ) * I)‖ ≤ 0.00000011099 := by
  have hl := lg_3
  refine (ecis_approx ((((170:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.18676408902938788 0.18676408911438805 (-0.1867641) 0.00000001098 0.9826102212463 (-0.1856802442432) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p17_4 : ‖exp (-((((((170:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9723581182632:ℝ):ℂ) + (((-0.2334945178108):ℝ):ℂ) * I)‖ ≤ 0.00000014149 := by
  have hl := lg_4
  refine (ecis_approx ((((170:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.235670041302 0.235670041472 (-0.23567) 0.00000004148 0.9723581182632 (-0.2334945178108) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p17_5 : ‖exp (-((((((170:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9628032311531:ℝ):ℂ) + (((-0.2702035123405):ℝ):ℂ) * I)‖ ≤ 0.00000014521 := by
  have hl := lg_5
  refine (ecis_approx ((((170:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 0.27360444502541553 0.2736044451954157 (-0.2736044) 0.0000000452 0.9628032311531 (-0.2702035123405) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p406_2 : ‖exp (-((((((406:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9606626554676:ℝ):ℂ) + (((-0.277717954749):ℝ):ℂ) * I)‖ ≤ 0.00000014481 := by
  have hl := lg_2
  refine (ecis_approx ((((406:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.2814177552018 0.2814177554048 (-0.2814178) 0.0000000448 0.9606626554676 (-0.277717954749) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p406_3 : ‖exp (-((((((406:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9021639678919:ℝ):ℂ) + (((-0.4313932950771):ℝ):ℂ) * I)‖ ≤ 0.00000011092 := by
  have hl := lg_3
  refine (ecis_approx ((((406:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.446036589093714584 0.44603658929671499 (-0.4460366) 0.00000001091 0.9021639678919 (-0.4313932950771) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p406_4 : ‖exp (-((((((406:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8457455285787:ℝ):ℂ) + (((-0.5335864511858):ℝ):ℂ) * I)‖ ≤ 0.00000011082 := by
  have hl := lg_4
  refine (ecis_approx ((((406:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.5628355104036 0.5628355108096 (-0.5628355) 0.00000001081 0.8457455285787 (-0.5335864511858) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p406_5 : ‖exp (-((((((406:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7940022360837:ℝ):ℂ) + (((-0.6079148370407):ℝ):ℂ) * I)‖ ≤ 0.00000010778 := by
  have hl := lg_5
  refine (ecis_approx ((((406:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 0.653431792237168854 0.65343179264316926 (-0.6534318) 0.00000000777 0.7940022360837 (-0.6079148370407) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p642_2 : ‖exp (-((((((642:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9026104501671:ℝ):ℂ) + (((-0.4304583316062):ℝ):ℂ) * I)‖ ≤ 0.00000011026 := by
  have hl := lg_2
  refine (ecis_approx ((((642:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.4450004897526 0.4450004900736 (-0.4450005) 0.00000001025 0.9026104501671 (-0.4304583316062) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p642_3 : ‖exp (-((((((642:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7614112081253:ℝ):ℂ) + (((-0.648269212705):ℝ):ℂ) * I)‖ ≤ 0.00000011086 := by
  have hl := lg_3
  refine (ecis_approx ((((642:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.705309089158041288 0.70530908947904193 (-0.7053091) 0.00000001085 0.7614112081253 (-0.648269212705) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p642_4 : ‖exp (-((((((642:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6294112495016:ℝ):ℂ) + (((-0.7770723769385):ℝ):ℂ) * I)‖ ≤ 0.00000012051 := by
  have hl := lg_4
  refine (ecis_approx ((((642:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.8900009795052 0.8900009801472 (-0.890001) 0.0000000205 0.6294112495016 (-0.7770723769385) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p642_5 : ‖exp (-((((((642:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5120220926488:ℝ):ℂ) + (((-0.8589722793196):ℝ):ℂ) * I)‖ ≤ 0.00000014011 := by
  have hl := lg_5
  refine (ecis_approx ((((642:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 1.033259139448922178 1.03325914009092282 (-1.0332591) 0.0000000401 0.5120220926488 (-0.8589722793196) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p878_2 : ‖exp (-((((((878:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8204588335427:ℝ):ℂ) + (((-0.5717056082126):ℝ):ℂ) * I)‖ ≤ 0.00000012476 := by
  have hl := lg_2
  refine (ecis_approx ((((878:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.6085832243034 0.6085832247424 (-0.6085832) 0.00000002475 0.8204588335427 (-0.5717056082126) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p878_3 : ‖exp (-((((((878:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5697607717285:ℝ):ℂ) + (((-0.8218106004423):ℝ):ℂ) * I)‖ ≤ 0.00000011079 := by
  have hl := lg_3
  refine (ecis_approx ((((878:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.964581589222367992 0.96458158966136887 (-0.9645816) 0.00000001078 0.5697607717285 (-0.8218106004423) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p878_4 : ‖exp (-((((((878:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3463053950765:ℝ):ℂ) + (((-0.9381218328879):ℝ):ℂ) * I)‖ ≤ 0.0000001495 := by
  have hl := lg_4
  refine (ecis_approx ((((878:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 1.2171664486068 1.2171664494848 (-1.2171664) 0.00000004949 0.3463053950765 (-0.9381218328879) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v0p878_5 : ‖exp (-((((((878:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1570568693156:ℝ):ℂ) + (((-0.9875895603948):ℝ):ℂ) * I)‖ ≤ 0.00000011335 := by
  have hl := lg_5
  refine (ecis_approx ((((878:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 1.413086486660675502 1.41308648753867638 (-1.4130865) 0.00000001334 0.1570568693156 (-0.9875895603948) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p193_2 : ‖exp (-((((((1193:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6771419991189:ℝ):ℂ) + (((-0.735852371763):ℝ):ℂ) * I)‖ ≤ 0.00000011392 := by
  have hl := lg_2
  refine (ecis_approx ((((1193:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.8269245860979 0.8269245866944 (-0.8269246) 0.00000001391 0.6771419991189 (-0.735852371763) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p193_3 : ‖exp (-((((((1193:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2572272728216:ℝ):ℂ) + (((-0.9663509352801):ℝ):ℂ) * I)‖ ≤ 0.00000013994 := by
  have hl := lg_3
  refine (ecis_approx ((((1193:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.310644460070939652 1.310644460667440845 (-1.3106445) 0.00000003993 0.2572272728216 (-0.9663509352801) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p193_4 : ‖exp (-((((((1193:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0829574260587):ℝ):ℂ) + (((-0.9965530921438):ℝ):ℂ) * I)‖ ≤ 0.00000012782 := by
  have hl := lg_4
  refine (ecis_approx ((((1193:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 1.6538491721958 1.6538491733888 (-1.6538492) 0.00000002781 (-0.0829574260587) (-0.9965530921438) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p193_5 : ‖exp (-((((((1193:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3422054654885):ℝ):ℂ) + (((-0.9396251483371):ℝ):ℂ) * I)‖ ≤ 0.00000013012 := by
  have hl := lg_5
  refine (ecis_approx ((((1193:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 1.920059428913651337 1.92005943010665253 (-1.9200594) 0.00000003011 (-0.3422054654885) (-0.9396251483371) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p429_2 : ‖exp (-((((((1429:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5482656740173:ℝ):ℂ) + (((-0.8363042213778):ℝ):ℂ) * I)‖ ≤ 0.00000012138 := by
  have hl := lg_2
  refine (ecis_approx ((((1429:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.9905073206487 0.9905073213632 (-0.9905073) 0.00000002137 0.5482656740173 (-0.8363042213778) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p429_3 : ‖exp (-((((((1429:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0008793266815:ℝ):ℂ) + (((-0.9999996133921):ℝ):ℂ) * I)‖ ≤ 0.00000013988 := by
  have hl := lg_3
  refine (ecis_approx ((((1429:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.569916960135266356 1.569916960849767785 (-1.569917) 0.00000003987 0.0008793266815 (-0.9999996133921) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p429_4 : ‖exp (-((((((1429:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3988095013889):ℝ):ℂ) + (((-0.9170337952326):ℝ):ℂ) * I)‖ ≤ 0.00000014274 := by
  have hl := lg_4
  refine (ecis_approx ((((1429:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 1.9810146412974 1.9810146427264 (-1.9810146) 0.00000004273 (-0.3988095013889) (-0.9170337952326) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p429_5 : ‖exp (-((((((1429:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6661916031789):ℝ):ℂ) + (((-0.7457806298337):ℝ):ℂ) * I)‖ ≤ 0.00000012389 := by
  have hl := lg_5
  refine (ecis_approx ((((1429:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 2.299886776125404661 2.29988677755440609 (-2.2998868) 0.00000002388 (-0.6661916031789) (-0.7457806298337) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p665_2 : ‖exp (-((((((1665:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4047507387294:ℝ):ℂ) + (((-0.9144270553182):ℝ):ℂ) * I)‖ ≤ 0.00000014482 := by
  have hl := lg_2
  refine (ecis_approx ((((1665:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.1540900551995 1.154090056032 (-1.1540901) 0.00000004481 0.4047507387294 (-0.9144270553182) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p665_3 : ‖exp (-((((((1665:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2555273993722):ℝ):ℂ) + (((-0.9668018143181):ℝ):ℂ) * I)‖ ≤ 0.00000013982 := by
  have hl := lg_3
  refine (ecis_approx ((((1665:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.82918946019959306 1.829189461032094725 (-1.8291895) 0.00000003981 (-0.2555273993722) (-0.9668018143181) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p665_4 : ‖exp (-((((((1665:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6723536049707):ℝ):ℂ) + (((-0.7402301195326):ℝ):ℂ) * I)‖ ≤ 0.00000011208 := by
  have hl := lg_4
  refine (ecis_approx ((((1665:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 2.308180110399 2.308180112064 (-2.3081801) 0.00000001207 (-0.6723536049707) (-0.7402301195326) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p665_5 : ‖exp (-((((((1665:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8952169366061):ℝ):ℂ) + (((-0.4456306052131):ℝ):ℂ) * I)‖ ≤ 0.00000012502 := by
  have hl := lg_5
  refine (ecis_approx ((((1665:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 2.679714123337157985 2.67971412500215965 (-2.6797141) 0.00000002501 (-0.8952169366061) (-0.4456306052131) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p901_2 : ‖exp (-((((((1901:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.250429171357:ℝ):ℂ) + (((-0.9681349235171):ℝ):ℂ) * I)‖ ≤ 0.00000011026 := by
  have hl := lg_2
  refine (ecis_approx ((((1901:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.3176727897503 1.3176727907008 (-1.3176728) 0.00000001025 0.250429171357 (-0.9681349235171) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p901_3 : ‖exp (-((((((1901:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4948530123495):ℝ):ℂ) + (((-0.8689766948328):ℝ):ℂ) * I)‖ ≤ 0.00000013975 := by
  have hl := lg_3
  refine (ecis_approx ((((1901:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 2.088461960263919764 2.088461961214421665 (-2.088462) 0.00000003974 (-0.4948530123495) (-0.8689766948328) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p901_4 : ‖exp (-((((((1901:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8745704602423):ℝ):ℂ) + (((-0.4848984532663):ℝ):ℂ) * I)‖ ≤ 0.00000012051 := by
  have hl := lg_4
  refine (ecis_approx ((((1901:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 2.6353455795006 2.6353455814016 (-2.6353456) 0.0000000205 (-0.8745704602423) (-0.4848984532663) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v1p901_5 : ‖exp (-((((((1901:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9966356919835):ℝ):ℂ) + (((-0.0819591175869):ℝ):ℂ) * I)‖ ≤ 0.00000012947 := by
  have hl := lg_5
  refine (ecis_approx ((((1901:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 3.059541470548911309 3.05954147244991321 (-3.0595415) 0.00000002946 (-0.9966356919835) (-0.0819591175869) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p216_2 : ‖exp (-((((((2216:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0347751140041:ℝ):ℂ) + (((-0.9993951628089):ℝ):ℂ) * I)‖ ≤ 0.00000014847 := by
  have hl := lg_2
  refine (ecis_approx ((((2216:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.5360141515448 1.5360141526528 (-1.5360142) 0.00000004846 0.0347751140041 (-0.9993951628089) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p216_3 : ‖exp (-((((((2216:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.760269885298):ℝ):ℂ) + (((-0.6496073440722):ℝ):ℂ) * I)‖ ≤ 0.00000013224 := by
  have hl := lg_3
  refine (ecis_approx ((((2216:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 2.434524831112491424 2.43452483222049364 (-2.4345248) 0.00000003223 (-0.760269885298) (-0.6496073440722) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p216_4 : ‖exp (-((((((2216:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9975813756912):ℝ):ℂ) + (((-0.0695082609553):ℝ):ℂ) * I)‖ ≤ 0.00000010532 := by
  have hl := lg_4
  refine (ecis_approx ((((2216:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 3.0720283030896 3.0720283053056 (-3.0720283) 0.00000000531 (-0.9975813756912) (-0.0695082609553) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p216_5 : ‖exp (-((((((2216:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9110709927463):ℝ):ℂ) + ((0.4122494949011:ℝ):ℂ) * I)‖ ≤ 0.00000010785 := by
  have hl := lg_5
  refine (ecis_approx ((((2216:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.566514412801887144 3.56651441501788936 2.7166709 0.00000000784 (-0.9110709927463) 0.4122494949011 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p531_2 : ‖exp (-((((((2531:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1825301021958):ℝ):ℂ) + (((-0.9832002653537):ℝ):ℂ) * I)‖ ≤ 0.00000011462 := by
  have hl := lg_2
  refine (ecis_approx ((((2531:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.7543555133393 1.7543555146048 (-1.7543555) 0.00000001461 (-0.1825301021958) (-0.9832002653537) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p531_3 : ‖exp (-((((((2531:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9355423318292):ℝ):ℂ) + (((-0.3532145880134):ℝ):ℂ) * I)‖ ≤ 0.00000010324 := by
  have hl := lg_3
  refine (ecis_approx ((((2531:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 2.780587701961063084 2.780587703226565615 (-2.7805877) 0.00000000323 (-0.9355423318292) (-0.3532145880134) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p531_4 : ‖exp (-((((((2531:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9333655209527):ℝ):ℂ) + ((0.3589272964415:ℝ):ℂ) * I)‖ ≤ 0.00000012205 := by
  have hl := lg_4
  refine (ecis_approx ((((2531:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.5087110266786 3.5087110292096 2.7744743 0.00000002204 (-0.9333655209527) 0.3589272964415 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p531_5 : ‖exp (-((((((2531:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5963141180708):ℝ):ℂ) + ((0.802751189708:ℝ):ℂ) * I)‖ ≤ 0.00000015042 := by
  have hl := lg_5
  refine (ecis_approx ((((2531:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.073487355054862979 4.07348735758586551 2.209698 0.00000005041 (-0.5963141180708) 0.802751189708 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p846_2 : ‖exp (-((((((2846:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3911681817763):ℝ):ℂ) + (((-0.9203192128619):ℝ):ℂ) * I)‖ ≤ 0.00000012488 := by
  have hl := lg_2
  refine (ecis_approx ((((2846:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.9726968751338 1.9726968765568 (-1.9726969) 0.00000002487 (-0.3911681817763) (-0.9203192128619) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p846_3 : ‖exp (-((((((2846:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998883692729):ℝ):ℂ) + (((-0.0149414972984):ℝ):ℂ) * I)‖ ≤ 0.00000012721 := by
  have hl := lg_3
  refine (ecis_approx ((((2846:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 3.126650572809634744 3.12665057423263759 (-3.1266506) 0.0000000272 (-0.9998883692729) (-0.0149414972984) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p846_4 : ‖exp (-((((((2846:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6939749739595):ℝ):ℂ) + ((0.7199991218711:ℝ):ℂ) * I)‖ ≤ 0.00000014595 := by
  have hl := lg_4
  refine (ecis_approx ((((2846:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.9453937502676 3.9453937531136 2.3377916 0.00000004594 (-0.6939749739595) 0.7199991218711 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v2p846_5 : ‖exp (-((((((2846:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1315462991846):ℝ):ℂ) + ((0.9913100277765:ℝ):ℂ) * I)‖ ≤ 0.00000010989 := by
  have hl := lg_5
  refine (ecis_approx ((((2846:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.580460297307838814 4.58046030015384166 1.702725 0.00000000988 (-0.1315462991846) 0.9913100277765 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p161_2 : ‖exp (-((((((3161:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5812319989295):ℝ):ℂ) + (((-0.8137378960143):ℝ):ℂ) * I)‖ ≤ 0.00000013852 := by
  have hl := lg_2
  refine (ecis_approx ((((3161:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.1910382369283 2.1910382385088 (-2.1910382) 0.00000003851 (-0.5812319989295) (-0.8137378960143) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p161_3 : ‖exp (-((((((3161:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9456785769934):ℝ):ℂ) + ((0.3251031049119:ℝ):ℂ) * I)‖ ≤ 0.00000013807 := by
  have hl := lg_3
  refine (ecis_approx ((((3161:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.472713443658206404 3.472713445238709565 2.8104719 0.00000003806 (-0.9456785769934) 0.3251031049119 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p161_4 : ‖exp (-((((((3161:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3243386254537):ℝ):ℂ) + ((0.9459410425797:ℝ):ℂ) * I)‖ ≤ 0.00000013334 := by
  have hl := lg_4
  refine (ecis_approx ((((3161:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.3820764738566 4.3820764770176 1.9011088 0.00000003333 (-0.3243386254537) 0.9459410425797 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p161_5 : ‖exp (-((((((3161:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3663136820976:ℝ):ℂ) + ((0.9304914219423:ℝ):ℂ) * I)‖ ≤ 0.00000013556 := by
  have hl := lg_5
  refine (ecis_approx ((((3161:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.087433239560814649 5.08743324272181781 1.1957521 0.00000003555 0.3663136820976 0.9304914219423 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p476_2 : ‖exp (-((((((3476:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7436967605199):ℝ):ℂ) + (((-0.6685171114937):ℝ):ℂ) * I)‖ ≤ 0.00000010129 := by
  have hl := lg_2
  refine (ecis_approx ((((3476:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.4093795987228 2.4093796004608 (-2.4093796) 0.00000000128 (-0.7436967605199) (-0.6685171114937) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p476_3 : ‖exp (-((((((3476:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7793405316015):ℝ):ℂ) + ((0.6266006190238:ℝ):ℂ) * I)‖ ≤ 0.00000010908 := by
  have hl := lg_3
  refine (ecis_approx ((((3476:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.818776314506778064 3.81877631624478154 2.464409 0.00000000907 (-0.7793405316015) 0.6266006190238 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p476_4 : ‖exp (-((((((3476:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1061697503704:ℝ):ℂ) + ((0.9943480196119:ℝ):ℂ) * I)‖ ≤ 0.00000010975 := by
  have hl := lg_4
  refine (ecis_approx ((((3476:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.8187591974456 4.8187592009216 1.4644261 0.00000000974 0.1061697503704 0.9943480196119 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p476_5 : ‖exp (-((((((3476:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7720225882415:ℝ):ℂ) + ((0.6355950937861:ℝ):ℂ) * I)‖ ≤ 0.00000012538 := by
  have hl := lg_5
  refine (ecis_approx ((((3476:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.594406181813790484 5.59440618528979396 0.6887791 0.00000002537 0.7720225882415 0.6355950937861 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p897_2 : ‖exp (-((((((3897:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9045820447775):ℝ):ℂ) + (((-0.426299570894):ℝ):ℂ) * I)‖ ≤ 0.00000013839 := by
  have hl := lg_2
  refine (ecis_approx ((((3897:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.7011945616291 2.7011945635776 (-2.7011946) 0.00000003838 (-0.9045820447775) (-0.426299570894) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p897_3 : ‖exp (-((((((3897:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4178675716295):ℝ):ℂ) + ((0.908507948549:ℝ):ℂ) * I)‖ ≤ 0.00000011927 := by
  have hl := lg_3
  refine (ecis_approx ((((3897:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.281292087926615108 4.281292089875119005 2.0018932 0.00000001926 (-0.4178675716295) 0.908507948549 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p897_4 : ‖exp (-((((((3897:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.636537280012:ℝ):ℂ) + ((0.7712459342874:ℝ):ℂ) * I)‖ ≤ 0.00000011999 := by
  have hl := lg_4
  refine (ecis_approx ((((3897:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.4023891232582 5.4023891271552 0.8807962 0.00000001998 0.636537280012 0.7712459342874 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v3p897_5 : ‖exp (-((((((3897:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999372156802:ℝ):ℂ) + ((0.0112055654828:ℝ):ℂ) * I)‖ ≤ 0.00000013946 := by
  have hl := lg_5
  refine (ecis_approx ((((3897:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.271979542729672473 6.27197954662667637 0.0112058 0.00000003945 0.9999372156802 0.0112055654828 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p212_2 : ‖exp (-((((((4212:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9754465408301):ℝ):ℂ) + (((-0.2202363405179):ℝ):ℂ) * I)‖ ≤ 0.00000012554 := by
  have hl := lg_2
  refine (ecis_approx ((((4212:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.9195359234236 2.9195359255296 (-2.9195359) 0.00000002553 (-0.9754465408301) (-0.2202363405179) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p212_3 : ‖exp (-((((((4212:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0849315333043):ℝ):ℂ) + ((0.9963867896807:ℝ):ℂ) * I)‖ ≤ 0.00000014842 := by
  have hl := lg_3
  refine (ecis_approx ((((4212:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.627354958775186768 4.62735496088119098 1.6558303 0.00000004841 (-0.0849315333043) 0.9963867896807 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p212_4 : ‖exp (-((((((4212:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9029919115842:ℝ):ℂ) + ((0.4296575469062:ℝ):ℂ) * I)‖ ≤ 0.00000014389 := by
  have hl := lg_4
  refine (ecis_approx ((((4212:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.8390718468472 5.8390718510592 0.4441135 0.00000004388 0.9029919115842 0.4296575469062 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p212_5 : ‖exp (-((((((4212:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8796040066162:ℝ):ℂ) + (((-0.4757066233981):ℝ):ℂ) * I)‖ ≤ 0.00000012221 := by
  have hl := lg_5
  refine (ecis_approx ((((4212:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.778952484982648308 6.77895248919465252 (-0.4957672) 0.0000000222 0.8796040066162 (-0.4757066233981) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p527_2 : ‖exp (-((((((4527:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999930977437):ℝ):ℂ) + (((-0.0037153447408):ℝ):ℂ) * I)‖ ≤ 0.0000001148 := by
  have hl := lg_2
  refine (ecis_approx ((((4527:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 3.1378772852181 3.1378772874816 (-3.1378773) 0.00000001479 (-0.9999930977437) (-0.0037153447408) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p527_3 : ‖exp (-((((((4527:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2580746635627:ℝ):ℂ) + ((0.9661249753665:ℝ):ℂ) * I)‖ ≤ 0.00000012472 := by
  have hl := lg_3
  refine (ecis_approx ((((4527:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.973417829623758428 4.973417831887262955 1.3097675 0.00000002471 0.2580746635627 0.9661249753665 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p527_4 : ‖exp (-((((((4527:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999723924758:ℝ):ℂ) + ((0.0074306316188:ℝ):ℂ) * I)‖ ≤ 0.00000013676 := by
  have hl := lg_4
  refine (ecis_approx ((((4527:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.2757545704362 6.2757545749632 0.0074307 0.00000003675 0.9999723924758 0.0074306316188 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p527_5 : ‖exp (-((((((4527:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5379945657744:ℝ):ℂ) + (((-0.8429483063612):ℝ):ℂ) * I)‖ ≤ 0.0000001246 := by
  have hl := lg_5
  refine (ecis_approx ((((4527:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.285925427235624143 7.28592543176262867 (-1.0027401) 0.00000002459 0.5379945657744 (-0.8429483063612) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p842_2 : ‖exp (-((((((4842:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9770561275763):ℝ):ℂ) + ((0.2129819787187:ℝ):ℂ) * I)‖ ≤ 0.00000014227 := by
  have hl := lg_2
  refine (ecis_approx ((((4842:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.3562186470126 3.3562186494336 2.9269667 0.00000004226 (-0.9770561275763) 0.2129819787187 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p842_3 : ‖exp (-((((((4842:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5704812804229:ℝ):ℂ) + ((0.8213106042704:ℝ):ℂ) * I)‖ ≤ 0.00000010672 := by
  have hl := lg_3
  refine (ecis_approx ((((4842:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.319480700472330088 5.31948070289333493 0.9637046 0.00000000671 0.5704812804229 0.8213106042704 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p842_4 : ‖exp (-((((((4842:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9092773147211:ℝ):ℂ) + (((-0.4161907794914):ℝ):ℂ) * I)‖ ≤ 0.00000011317 := by
  have hl := lg_4
  refine (ecis_approx ((((4842:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.7124372940252 6.7124372988672 (-0.429252) 0.00000001316 0.9092773147211 (-0.4161907794914) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v4p842_5 : ‖exp (-((((((4842:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0610452486592:ℝ):ℂ) + (((-0.9981349996949):ℝ):ℂ) * I)‖ ≤ 0.00000013771 := by
  have hl := lg_5
  refine (ecis_approx ((((4842:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.792898369488599978 7.79289837433060482 (-1.5097131) 0.0000000377 0.0610452486592 (-0.9981349996949) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p157_2 : ‖exp (-((((((5157:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9077247465762):ℝ):ℂ) + ((0.4195661858723:ℝ):ℂ) * I)‖ ≤ 0.00000010422 := by
  have hl := lg_2
  refine (ecis_approx ((((5157:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.5745600088071 3.5745600113856 2.7086253 0.00000000421 (-0.9077247465762) 0.4195661858723 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p157_3 : ‖exp (-((((((5157:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8152464473879:ℝ):ℂ) + ((0.5791141770164:ℝ):ℂ) * I)‖ ≤ 0.00000013587 := by
  have hl := lg_3
  refine (ecis_approx ((((5157:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.665543571320901748 5.665543573899406905 0.6176417 0.00000003586 0.8152464473879 0.5791141770164 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p157_4 : ‖exp (-((((((5157:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6479284367005:ℝ):ℂ) + (((-0.7617012149884):ℝ):ℂ) * I)‖ ≤ 0.00000011561 := by
  have hl := lg_4
  refine (ecis_approx ((((5157:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.1491200176142 7.1491200227712 (-0.8659347) 0.0000000156 0.6479284367005 (-0.7617012149884) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p157_5 : ‖exp (-((((((5157:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.431260738361):ℝ):ℂ) + (((-0.9022273413859):ℝ):ℂ) * I)‖ ≤ 0.00000010973 := by
  have hl := lg_5
  refine (ecis_approx ((((5157:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.299871311741575813 8.29987131689858097 (-2.016686) 0.00000000972 (-0.431260738361) (-0.9022273413859) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p472_2 : ‖exp (-((((((5472:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7952910771042):ℝ):ℂ) + ((0.6062277646487:ℝ):ℂ) * I)‖ ≤ 0.00000013659 := by
  have hl := lg_2
  refine (ecis_approx ((((5472:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.7929013706016 3.7929013733376 2.4902839 0.00000003658 (-0.7952910771042) 0.6062277646487 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p472_3 : ‖exp (-((((((5472:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9633485529713:ℝ):ℂ) + ((0.2682528014542:ℝ):ℂ) * I)‖ ≤ 0.00000013774 := by
  have hl := lg_3
  refine (ecis_approx ((((5472:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.011606442169473408 6.01160644490547888 0.2715789 0.00000003773 0.9633485529713 0.2682528014542 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p472_4 : ‖exp (-((((((5472:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.264975898022:ℝ):ℂ) + (((-0.9642550354898):ℝ):ℂ) * I)‖ ≤ 0.00000013951 := by
  have hl := lg_4
  refine (ecis_approx ((((5472:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.5858027412032 7.5858027466752 (-1.3026174) 0.0000000395 0.264975898022 (-0.9642550354898) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p472_5 : ‖exp (-((((((5472:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8150772802357):ℝ):ℂ) + (((-0.5793522479357):ℝ):ℂ) * I)‖ ≤ 0.0000001523 := by
  have hl := lg_5
  refine (ecis_approx ((((5472:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.806844253994551648 8.80684425946655712 (-2.5236589) 0.00000005229 (-0.8150772802357) (-0.5793522479357) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p787_2 : ‖exp (-((((((5787:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6450939819171):ℝ):ℂ) + ((0.7641032354846:ℝ):ℂ) * I)‖ ≤ 0.00000012813 := by
  have hl := lg_2
  refine (ecis_approx ((((5787:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.0112427323961 4.0112427352896 2.2719426 0.00000002812 (-0.6450939819171) 0.7641032354846 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p787_3 : ‖exp (-((((((5787:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9972273490857:ℝ):ℂ) + (((-0.0744151478902):ℝ):ℂ) * I)‖ ≤ 0.00000010875 := by
  have hl := lg_3
  refine (ecis_approx ((((5787:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.357669313018045068 6.357669315911550855 (-0.074484) 0.00000000874 0.9972273490857 (-0.0744151478902) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p787_4 : ‖exp (-((((((5787:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1677076004903):ℝ):ℂ) + (((-0.9858367819964):ℝ):ℂ) * I)‖ ≤ 0.0000001424 := by
  have hl := lg_4
  refine (ecis_approx ((((5787:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.0224854647922 8.0224854705792 (-1.7393002) 0.00000004239 (-0.1677076004903) (-0.9858367819964) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v5p787_5 : ‖exp (-((((((5787:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9938501691364):ℝ):ℂ) + (((-0.110733196698):ℝ):ℂ) * I)‖ ≤ 0.00000011095 := by
  have hl := lg_5
  refine (ecis_approx ((((5787:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.313817196247527483 9.31381720203453327 (-3.0306319) 0.00000001094 (-0.9938501691364) (-0.110733196698) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p208_2 : ‖exp (-((((((6208:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3979959356337):ℝ):ℂ) + ((0.9173871784671:ℝ):ℂ) * I)‖ ≤ 0.00000011189 := by
  have hl := lg_2
  refine (ecis_approx ((((6208:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.3030576953024 4.3030576984064 1.9801276 0.00000001188 (-0.3979959356337) 0.9173871784671 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p208_3 : ‖exp (-((((((6208:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8592473296511:ℝ):ℂ) + (((-0.511560384009):ℝ):ℂ) * I)‖ ≤ 0.00000012076 := by
  have hl := lg_3
  refine (ecis_approx ((((6208:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.820185086437882112 6.82018508954188832 (-0.5369998) 0.00000002075 0.8592473296511 (-0.511560384009) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p208_4 : ‖exp (-((((((6208:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6831984651929):ℝ):ℂ) + (((-0.7302327417591):ℝ):ℂ) * I)‖ ≤ 0.00000011659 := by
  have hl := lg_4
  refine (ecis_approx ((((6208:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.6061153906048 8.6061153968128 (-2.3229301) 0.00000001658 (-0.6831984651929) (-0.7302327417591) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p208_5 : ‖exp (-((((((6208:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8437241159806):ℝ):ℂ) + ((0.5367770636332:ℝ):ℂ) * I)‖ ≤ 0.00000014903 := by
  have hl := lg_5
  refine (ecis_approx ((((6208:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.991390557163409472 9.99139056337141568 2.5749801 0.00000004902 (-0.8437241159806) 0.5367770636332 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p629_2 : ‖exp (-((((((6629:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1172459751671):ℝ):ℂ) + ((0.9931029056984:ℝ):ℂ) * I)‖ ≤ 0.00000014899 := by
  have hl := lg_2
  refine (ecis_approx ((((6629:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.5948726582087 4.5948726615232 1.6883126 0.00000004898 (-0.1172459751671) 0.9931029056984 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p629_3 : ‖exp (-((((((6629:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5407098510081:ℝ):ℂ) + (((-0.8412091636584):ℝ):ℂ) * I)‖ ≤ 0.00000014734 := by
  have hl := lg_3
  refine (ecis_approx ((((6629:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.282700859857719156 7.282700863172225785 (-0.9995156) 0.00000004733 0.5407098510081 (-0.8412091636584) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p629_4 : ‖exp (-((((((6629:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9725067375433):ℝ):ℂ) + (((-0.2328747413304):ℝ):ℂ) * I)‖ ≤ 0.00000011588 := by
  have hl := lg_4
  refine (ecis_approx ((((6629:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.1897453164174 9.1897453230464 (-2.90656) 0.00000001587 (-0.9725067375433) (-0.2328747413304) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v6p629_5 : ‖exp (-((((((6629:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3208344425032):ℝ):ℂ) + ((0.9471352915512:ℝ):ℂ) * I)‖ ≤ 0.00000011036 := by
  have hl := lg_5
  refine (ecis_approx ((((6629:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.668963918079291461 10.66896392470829809 1.8974067 0.00000001035 (-0.3208344425032) 0.9471352915512 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p05_2 : ‖exp (-((((((7050:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1734174340174:ℝ):ℂ) + ((0.9848484114719:ℝ):ℂ) * I)‖ ≤ 0.00000011748 := by
  have hl := lg_2
  refine (ecis_approx ((((7050:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.886687621115 4.88668762464 1.3964977 0.00000001747 0.1734174340174 0.9848484114719 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p05_3 : ‖exp (-((((((7050:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1085507082865:ℝ):ℂ) + (((-0.9940909132119):ℝ):ℂ) * I)‖ ≤ 0.00000012964 := by
  have hl := lg_3
  refine (ecis_approx ((((7050:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.7452166332775562 7.74521663680256325 (-1.4620313) 0.00000002963 0.1085507082865 (-0.9940909132119) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p05_4 : ‖exp (-((((((7050:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9398527870964):ℝ):ℂ) + ((0.3415797687334:ℝ):ℂ) * I)‖ ≤ 0.00000013494 := by
  have hl := lg_4
  refine (ecis_approx ((((7050:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.77337524223 9.77337524928 2.7929954 0.00000003493 (-0.9398527870964) 0.3415797687334 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p05_5 : ‖exp (-((((((7050:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3438022894033:ℝ):ℂ) + ((0.9390420575252:ℝ):ℂ) * I)‖ ≤ 0.00000013538 := by
  have hl := lg_5
  refine (ecis_approx ((((7050:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.34653727899517345 11.3465372860451805 1.2198333 0.00000003537 0.3438022894033 0.9390420575252 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p471_2 : ‖exp (-((((((7471:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4494179068262:ℝ):ℂ) + ((0.8933216358199:ℝ):ℂ) * I)‖ ≤ 0.00000012317 := by
  have hl := lg_2
  refine (ecis_approx ((((7471:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.1785025840213 5.1785025877568 1.1046827 0.00000002316 0.4494179068262 0.8933216358199 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p471_3 : ‖exp (-((((((7471:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3464187612035):ℝ):ℂ) + (((-0.9380799762728):ℝ):ℂ) * I)‖ ≤ 0.00000010327 := by
  have hl := lg_3
  refine (ecis_approx ((((7471:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.207732406697393244 8.207732410432900715 (-1.9245471) 0.00000000326 (-0.3464187612035) (-0.9380799762728) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p471_4 : ‖exp (-((((((7471:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5960470900471):ℝ):ℂ) + ((0.8029494793788:ℝ):ℂ) * I)‖ ≤ 0.00000014633 := by
  have hl := lg_4
  refine (ecis_approx ((((7471:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.3570051680426 10.3570051755136 2.2093654 0.00000004632 (-0.5960470900471) 0.8029494793788 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p471_5 : ‖exp (-((((((7471:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8565445445963:ℝ):ℂ) + ((0.5160730986229:ℝ):ℂ) * I)‖ ≤ 0.00000013304 := by
  have hl := lg_5
  refine (ecis_approx ((((7471:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.024110639911055439 12.02411064738206291 0.54226 0.00000003303 0.8565445445963 0.5160730986229 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p892_2 : ‖exp (-((((((7892:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6874184897292:ℝ):ℂ) + ((0.7262615368987:ℝ):ℂ) * I)‖ ≤ 0.00000014371 := by
  have hl := lg_2
  refine (ecis_approx ((((7892:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.4703175469276 5.4703175508736 0.8128678 0.0000000437 0.6874184897292 0.7262615368987 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p892_3 : ‖exp (-((((((7892:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7285937171808):ℝ):ℂ) + (((-0.6849461258053):ℝ):ℂ) * I)‖ ≤ 0.00000012708 := by
  have hl := lg_3
  refine (ecis_approx ((((7892:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.670248180117230288 8.67024818406323818 (-2.3870629) 0.00000002707 (-0.7285937171808) (-0.6849461258053) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p892_4 : ‖exp (-((((((7892:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0549115401079):ℝ):ℂ) + ((0.9984912231776:ℝ):ℂ) * I)‖ ≤ 0.00000012052 := by
  have hl := lg_4
  refine (ecis_approx ((((7892:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.9406350938552 10.9406351017472 1.6257355 0.00000002051 (-0.0549115401079) 0.9984912231776 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v7p892_5 : ‖exp (-((((((7892:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9908591019388:ℝ):ℂ) + (((-0.1349008528698):ℝ):ℂ) * I)‖ ≤ 0.00000011355 := by
  have hl := lg_5
  refine (ecis_approx ((((7892:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.701684000826937428 12.70168400871894532 (-0.1353134) 0.00000001354 0.9908591019388 (-0.1349008528698) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p313_2 : ‖exp (-((((((8313:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8672955834251:ℝ):ℂ) + ((0.4977935023394:ℝ):ℂ) * I)‖ ≤ 0.00000010683 := by
  have hl := lg_2
  refine (ecis_approx ((((8313:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.7621325098339 5.7621325139904 0.5210528 0.00000000682 0.8672955834251 0.4977935023394 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p313_3 : ‖exp (-((((((8313:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9576660091984):ℝ):ℂ) + (((-0.2878815982317):ℝ):ℂ) * I)‖ ≤ 0.00000015053 := by
  have hl := lg_3
  refine (ecis_approx ((((8313:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.132763953537067332 9.132763957693575645 (-2.8495786) 0.00000005052 (-0.9576660091984) (-0.2878815982317) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p313_4 : ‖exp (-((((((8313:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5044032580574:ℝ):ℂ) + ((0.8634682120733:ℝ):ℂ) * I)‖ ≤ 0.00000011364 := by
  have hl := lg_4
  refine (ecis_approx ((((8313:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.5242650196678 11.5242650279808 1.0421056 0.00000001363 0.5044032580574 0.8634682120733 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p313_5 : ‖exp (-((((((8313:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6874046906359:ℝ):ℂ) + (((-0.7262745977189):ℝ):ℂ) * I)‖ ≤ 0.00000015263 := by
  have hl := lg_5
  refine (ecis_approx ((((8313:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.379257361742819417 13.37925737005582773 (-0.8128868) 0.00000005262 0.6874046906359 (-0.7262745977189) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p734_2 : ‖exp (-((((((8734:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9738398766318:ℝ):ℂ) + ((0.2272353288591:ℝ):ℂ) * I)‖ ≤ 0.00000013445 := by
  have hl := lg_2
  refine (ecis_approx ((((8734:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.0539474727402 6.0539474771072 0.2292378 0.00000003444 0.9738398766318 0.2272353288591 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p734_3 : ‖exp (-((((((8734:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9854997548443):ℝ):ℂ) + ((0.1696768482671:ℝ):ℂ) * I)‖ ≤ 0.00000011698 := by
  have hl := lg_3
  refine (ecis_approx ((((8734:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.595279726956904376 9.59527973132391311 2.9710909 0.00000001697 (-0.9854997548443) 0.1696768482671 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p734_4 : ‖exp (-((((((8734:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8967281663784:ℝ):ℂ) + ((0.442581738918:ℝ):ℂ) * I)‖ ≤ 0.00000013987 := by
  have hl := lg_4
  refine (ecis_approx ((((8734:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.1078949454804 12.1078949542144 0.4584757 0.00000003986 0.8967281663784 0.442581738918 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v8p734_5 : ‖exp (-((((((8734:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0802498408886:ℝ):ℂ) + (((-0.9967747804982):ℝ):ℂ) * I)‖ ≤ 0.00000011705 := by
  have hl := lg_5
  refine (ecis_approx ((((8734:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.056830722658701406 14.05683073139271014 (-1.4904601) 0.00000001704 0.0802498408886 (-0.9967747804982) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p155_2 : ‖exp (-((((((9155:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9980426921203:ℝ):ℂ) + (((-0.0625362671197):ℝ):ℂ) * I)‖ ≤ 0.00000013306 := by
  have hl := lg_2
  refine (ecis_approx ((((9155:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.3457624356465 6.345762440224 (-0.0625771) 0.00000003305 0.9980426921203 (-0.0625362671197) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p155_3 : ‖exp (-((((((9155:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8062460563232):ℝ):ℂ) + ((0.5915803382564:ℝ):ℂ) * I)‖ ≤ 0.000000114 := by
  have hl := lg_3
  refine (ecis_approx ((((9155:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.05779550037674142 10.057795504954250575 2.5085751 0.00000001399 (-0.8062460563232) 0.5915803382564 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p155_4 : ‖exp (-((((((9155:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9921784181067:ℝ):ℂ) + (((-0.1248278280005):ℝ):ℂ) * I)‖ ≤ 0.00000014308 := by
  have hl := lg_4
  refine (ecis_approx ((((9155:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.691524871293 12.691524880448 (-0.1251543) 0.00000004307 0.9921784181067 (-0.1248278280005) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p155_5 : ‖exp (-((((((9155:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5623600619274):ℝ):ℂ) + (((-0.8268924722959):ℝ):ℂ) * I)‖ ≤ 0.0000001308 := by
  have hl := lg_5
  refine (ecis_approx ((((9155:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.734404083574583395 14.73440409272959255 (-2.1680335) 0.00000003079 (-0.5623600619274) (-0.8268924722959) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p576_2 : ‖exp (-((((((9576:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9378576157393:ℝ):ℂ) + (((-0.3470203057456):ℝ):ℂ) * I)‖ ≤ 0.00000010864 := by
  have hl := lg_2
  refine (ecis_approx ((((9576:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.6375773985528 6.6375774033408 (-0.3543921) 0.00000000863 0.9378576157393 (-0.3470203057456) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p576_3 : ‖exp (-((((((9576:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4575722915199):ℝ):ℂ) + ((0.8891724231151:ℝ):ℂ) * I)‖ ≤ 0.00000014058 := by
  have hl := lg_3
  refine (ecis_approx ((((9576:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.520311273796578464 10.52031127858458804 2.0460593 0.00000004057 (-0.4575722915199) 0.8891724231151 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p576_4 : ‖exp (-((((((9576:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7591538148004:ℝ):ℂ) + (((-0.6509112731195):ℝ):ℂ) * I)‖ ≤ 0.00000011727 := by
  have hl := lg_4
  refine (ecis_approx ((((9576:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.2751547971056 13.2751548066816 (-0.7087842) 0.00000001726 0.7591538148004 (-0.6509112731195) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p576_5 : ‖exp (-((((((9576:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9565150503998):ℝ):ℂ) + (((-0.2916829753973):ℝ):ℂ) * I)‖ ≤ 0.00000013972 := by
  have hl := lg_5
  refine (ecis_approx ((((9576:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.411977444490465384 15.41197745406647496 (-2.8456068) 0.00000003971 (-0.9565150503998) (-0.2916829753973) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p997_2 : ‖exp (-((((((9997:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7983734783038:ℝ):ℂ) + (((-0.6021625936083):ℝ):ℂ) * I)‖ ≤ 0.00000014574 := by
  have hl := lg_2
  refine (ecis_approx ((((9997:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.9293923614591 6.9293923664576 (-0.6462071) 0.00000004573 0.7983734783038 (-0.6021625936083) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p997_3 : ‖exp (-((((((9997:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0127469279842):ℝ):ℂ) + ((0.999918754613:ℝ):ℂ) * I)‖ ≤ 0.00000013787 := by
  have hl := lg_3
  refine (ecis_approx ((((9997:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.982827047216415508 10.982827052214925505 1.5835436 0.00000003786 (-0.0127469279842) 0.999918754613 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p997_4 : ‖exp (-((((((9997:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.274800517868:ℝ):ℂ) + (((-0.9615012612469):ℝ):ℂ) * I)‖ ≤ 0.00000011857 := by
  have hl := lg_4
  refine (ecis_approx ((((9997:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.8587847229182 13.8587847329152 (-1.2924141) 0.00000001856 0.274800517868 (-0.9615012612469) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v9p997_5 : ‖exp (-((((((9997:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9280746093814):ℝ):ℂ) + ((0.3723943061667:ℝ):ℂ) * I)‖ ≤ 0.00000011615 := by
  have hl := lg_5
  refine (ecis_approx ((((9997:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.089550805406347373 16.08955081540335737 2.7600051 0.00000001614 (-0.9280746093814) 0.3723943061667 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p418_2 : ‖exp (-((((((10418:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5913842201444:ℝ):ℂ) + (((-0.8063899206738):ℝ):ℂ) * I)‖ ≤ 0.00000012241 := by
  have hl := lg_2
  refine (ecis_approx ((((10418:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.2212073243654 7.2212073295744 (-0.938022) 0.0000000224 0.5913842201444 (-0.8063899206738) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p418_3 : ‖exp (-((((((10418:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4347570930836:ℝ):ℂ) + ((0.9005477610952:ℝ):ℂ) * I)‖ ≤ 0.0000001115 := by
  have hl := lg_3
  refine (ecis_approx ((((10418:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.445342820636252552 11.44534282584526297 1.1210278 0.00000001149 0.4347570930836 0.9005477610952 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p418_4 : ‖exp (-((((((10418:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3005294083286):ℝ):ℂ) + (((-0.9537725487389):ℝ):ℂ) * I)‖ ≤ 0.0000001448 := by
  have hl := lg_4
  refine (ecis_approx ((((10418:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.4424146487308 14.4424146591488 (-1.876044) 0.00000004479 (-0.3005294083286) (-0.9537725487389) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p418_5 : ‖exp (-((((((10418:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4896039436222):ℝ):ℂ) + ((0.8719449399955:ℝ):ℂ) * I)‖ ≤ 0.00000015522 := by
  have hl := lg_5
  refine (ecis_approx ((((10418:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.767124166322229362 16.76712417674023978 2.0824318 0.00000005521 (-0.4896039436222) 0.8719449399955 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p839_2 : ‖exp (-((((((10839:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3343913483584:ℝ):ℂ) + (((-0.9424343086619):ℝ):ℂ) * I)‖ ≤ 0.00000011992 := by
  have hl := lg_2
  refine (ecis_approx ((((10839:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.5130222872717 7.5130222926912 (-1.229837) 0.00000001991 0.3343913483584 (-0.9424343086619) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p839_3 : ‖exp (-((((((10839:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7909036744583:ℝ):ℂ) + ((0.6119406652024:ℝ):ℂ) * I)‖ ≤ 0.00000012032 := by
  have hl := lg_3
  refine (ecis_approx ((((10839:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.907858594056089596 11.907858599475600435 0.658512 0.00000002031 0.7909036744583 0.6119406652024 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p839_4 : ‖exp (-((((((10839:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7763648522785):ℝ):ℂ) + (((-0.6302837584021):ℝ):ℂ) * I)‖ ≤ 0.00000013983 := by
  have hl := lg_4
  refine (ecis_approx ((((10839:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.0260445745434 15.0260445853824 (-2.459674) 0.00000003982 (-0.7763648522785) (-0.6302837584021) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v10p839_5 : ‖exp (-((((((10839:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1651774468143:ℝ):ℂ) + ((0.9862638648272:ℝ):ℂ) * I)‖ ≤ 0.00000011655 := by
  have hl := lg_5
  refine (ecis_approx ((((10839:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.444697527238111351 17.44469753807712219 1.4048584 0.00000001654 0.1651774468143 0.9862638648272 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p154_2 : ‖exp (-((((((11154:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1223109936732:ℝ):ℂ) + (((-0.9924918240603):ℝ):ℂ) * I)‖ ≤ 0.00000014748 := by
  have hl := lg_2
  refine (ecis_approx ((((11154:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.7313636490662 7.7313636546432 (-1.4481783) 0.00000004747 0.1223109936732 (-0.9924918240603) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p154_3 : ‖exp (-((((((11154:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9515835954359:ℝ):ℂ) + ((0.3073900793736:ℝ):ℂ) * I)‖ ≤ 0.00000014947 := by
  have hl := lg_3
  refine (ecis_approx ((((11154:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.253921464904661256 12.25392147048167241 0.3124491 0.00000004946 0.9515835954359 0.3073900793736 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p154_4 : ‖exp (-((((((11154:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.970080065826):ℝ):ℂ) + (((-0.2427852252817):ℝ):ℂ) * I)‖ ≤ 0.00000011624 := by
  have hl := lg_4
  refine (ecis_approx ((((11154:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.4627272981324 15.4627273092864 (-2.8963567) 0.00000001623 (-0.970080065826) (-0.2427852252817) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p154_5 : ‖exp (-((((((11154:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.623265000345:ℝ):ℂ) + ((0.7820107028327:ℝ):ℂ) * I)‖ ≤ 0.00000015206 := by
  have hl := lg_5
  refine (ecis_approx ((((11154:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.951670469491087186 17.95167048064509834 0.8978854 0.00000005205 0.623265000345 0.7820107028327 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p154_6 : ‖exp (-((((((11154:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4214712756965:ℝ):ℂ) + (((-0.9068417523266):ℝ):ℂ) * I)‖ ≤ 0.00000010758 := by
  have hl := lg_6
  refine (ecis_approx ((((11154:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.985285113970861256 19.98528512512487241 (-1.1357292) 0.00000000757 0.4214712756965 (-0.9068417523266) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p154_7 : ‖exp (-((((((11154:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9592482317273):ℝ):ℂ) + (((-0.2825647354101):ℝ):ℂ) * I)‖ ≤ 0.00000012479 := by
  have hl := lg_7
  refine (ecis_approx ((((11154:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.704681796764096988 21.704681807918119296 (-2.8551259) 0.00000002478 (-0.9592482317273) (-0.2825647354101) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p154_8 : ‖exp (-((((((11154:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3596138013384):ℝ):ℂ) + ((0.9331012345316:ℝ):ℂ) * I)‖ ≤ 0.00000013523 := by
  have hl := lg_8
  refine (ecis_approx ((((11154:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.1940909471986 23.1940909639296 1.9386503 0.00000003522 (-0.3596138013384) 0.9331012345316 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p154_9 : ‖exp (-((((((11154:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8110226197039:ℝ):ℂ) + ((0.5850147949656:ℝ):ℂ) * I)‖ ≤ 0.00000011226 := by
  have hl := lg_9
  refine (ecis_approx ((((11154:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.507842929809322512 24.50784294096334482 0.6248983 0.00000001225 0.8110226197039 0.5850147949656 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p154_10 : ‖exp (-((((((11154:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8523713904031:ℝ):ℂ) + (((-0.5229369109388):ℝ):ℂ) * I)‖ ≤ 0.00000011018 := by
  have hl := lg_10
  refine (ecis_approx ((((11154:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.683034118557287186 25.68303413528829834 (-0.5502929) 0.00000001017 0.8523713904031 (-0.5229369109388) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p469_2 : ‖exp (-((((((11469:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0955772551917):ℝ):ℂ) + (((-0.9954220151723):ℝ):ℂ) * I)‖ ≤ 0.00000010943 := by
  have hl := lg_2
  refine (ecis_approx ((((11469:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.9497050108607 7.9497050165952 (-1.6665197) 0.00000000942 (-0.0955772551917) (-0.9954220151723) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p469_3 : ‖exp (-((((((11469:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9994351127771:ℝ):ℂ) + (((-0.0336073704451):ℝ):ℂ) * I)‖ ≤ 0.00000012714 := by
  have hl := lg_3
  refine (ecis_approx ((((11469:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.599984335753232916 12.599984341487744385 (-0.0336137) 0.00000002713 0.9994351127771 (-0.0336073704451) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p469_4 : ‖exp (-((((((11469:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.981729975075):ℝ):ℂ) + ((0.1902794148179:ℝ):ℂ) * I)‖ ≤ 0.00000011167 := by
  have hl := lg_4
  refine (ecis_approx ((((11469:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.8994100217214 15.8994100331904 2.9501459 0.00000001166 (-0.981729975075) 0.1902794148179 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p469_5 : ‖exp (-((((((11469:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.924561752911:ℝ):ℂ) + ((0.38103223624:ℝ):ℂ) * I)‖ ≤ 0.00000010981 := by
  have hl := lg_5
  refine (ecis_approx ((((11469:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.458643411744063021 18.45864342321307449 0.3909125 0.0000000098 0.924561752911 0.38103223624 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p469_6 : ‖exp (-((((((11469:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1289767812345):ℝ):ℂ) + (((-0.9916476137731):ℝ):ℂ) * I)‖ ≤ 0.00000013656 := by
  have hl := lg_6
  refine (ecis_approx ((((11469:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.549689346613932916 20.549689358082944385 (-1.7001334) 0.00000003655 (-0.1289767812345) (-0.9916476137731) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p469_7 : ‖exp (-((((((11469:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9471723157624):ℝ):ℂ) + ((0.3207251222733:ℝ):ℂ) * I)‖ ≤ 0.00000013518 := by
  have hl := lg_7
  refine (ecis_approx ((((11469:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.317643493552754918 22.317643505021777856 2.8150977 0.00000003517 (-0.9471723157624) 0.3207251222733 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p469_8 : ‖exp (-((((((11469:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2832393750789:ℝ):ℂ) + ((0.9590492460791:ℝ):ℂ) * I)‖ ≤ 0.00000012108 := by
  have hl := lg_8
  refine (ecis_approx ((((11469:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.8491150325821 23.8491150497856 1.2836262 0.00000002107 0.2832393750789 0.9590492460791 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p469_9 : ‖exp (-((((((11469:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9977410893035:ℝ):ℂ) + (((-0.0671767721418):ℝ):ℂ) * I)‖ ≤ 0.00000015427 := by
  have hl := lg_9
  refine (ecis_approx ((((11469:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.199968671506465832 25.19996868297548877 (-0.0672274) 0.00000005426 0.9977410893035 (-0.0671767721418) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p469_10 : ‖exp (-((((((11469:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2909208018454:ℝ):ℂ) + (((-0.9567471385134):ℝ):ℂ) * I)‖ ≤ 0.0000001111 := by
  have hl := lg_10
  refine (ecis_approx ((((11469:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.408348422604763021 26.40834843980827449 (-1.2756072) 0.00000001109 0.2909208018454 (-0.9567471385134) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p784_2 : ‖exp (-((((((11784:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3089271256169):ℝ):ℂ) + (((-0.9510857117296):ℝ):ℂ) * I)‖ ≤ 0.00000013454 := by
  have hl := lg_2
  refine (ecis_approx ((((11784:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.1680463726552 8.1680463785472 (-1.8848611) 0.00000003453 (-0.3089271256169) (-0.9510857117296) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p784_3 : ‖exp (-((((((11784:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9287845426908:ℝ):ℂ) + (((-0.3706201198782):ℝ):ℂ) * I)‖ ≤ 0.00000010777 := by
  have hl := lg_3
  refine (ecis_approx ((((11784:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.946047206601804576 12.94604721249381636 (-0.3796766) 0.00000000776 0.9287845426908 (-0.3706201198782) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p784_4 : ‖exp (-((((((11784:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8091281166493):ℝ):ℂ) + ((0.5876322751472:ℝ):ℂ) * I)‖ ≤ 0.00000013557 := by
  have hl := lg_4
  refine (ecis_approx ((((11784:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.3360927453104 16.3360927570944 2.5134632 0.00000003556 (-0.8091281166493) 0.5876322751472 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p784_5 : ‖exp (-((((((11784:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9932725484382:ℝ):ℂ) + (((-0.1158000195122):ℝ):ℂ) * I)‖ ≤ 0.00000014426 := by
  have hl := lg_5
  refine (ecis_approx ((((11784:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.965616353997038856 18.96561636578105064 (-0.1160604) 0.00000004425 0.9932725484382 (-0.1158000195122) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p784_6 : ‖exp (-((((((11784:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6394182395854):ℝ):ℂ) + (((-0.7688590994909):ℝ):ℂ) * I)‖ ≤ 0.0000001423 := by
  have hl := lg_6
  refine (ecis_approx ((((11784:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.114093579257004576 21.11409359104101636 (-2.2645377) 0.00000004229 (-0.6394182395854) (-0.7688590994909) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p784_7 : ‖exp (-((((((11784:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5902267217434):ℝ):ℂ) + ((0.8072375220025:ℝ):ℂ) * I)‖ ≤ 0.00000013839 := by
  have hl := lg_7
  refine (ecis_approx ((((11784:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.930605190341412848 22.930605202125436416 2.202136 0.00000003838 (-0.5902267217434) 0.8072375220025 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p784_8 : ‖exp (-((((((11784:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.808850284008:ℝ):ℂ) + ((0.5880146410253:ℝ):ℂ) * I)‖ ≤ 0.00000011077 := by
  have hl := lg_8
  refine (ecis_approx ((((11784:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.5041391179656 24.5041391356416 0.6286021 0.00000001076 0.808850284008 0.5880146410253 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p784_9 : ‖exp (-((((((11784:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7252814534829:ℝ):ℂ) + (((-0.6884524771063):ℝ):ℂ) * I)‖ ≤ 0.00000011553 := by
  have hl := lg_9
  refine (ecis_approx ((((11784:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.892094413203609152 25.89209442498763272 (-0.7593532) 0.00000001552 0.7252814534829 (-0.6884524771063) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v11p784_10 : ‖exp (-((((((11784:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4169845773194):ℝ):ℂ) + (((-0.9089135614975):ℝ):ℂ) * I)‖ ≤ 0.00000011562 := by
  have hl := lg_10
  refine (ecis_approx ((((11784:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.133662726652238856 27.13366274432825064 (-2.0009215) 0.00000001561 (-0.4169845773194) (-0.9089135614975) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p02_2 : ‖exp (-((((((12020:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4596912203128):ℝ):ℂ) + (((-0.8880788151749):ℝ):ℂ) * I)‖ ≤ 0.00000010605 := by
  have hl := lg_2
  refine (ecis_approx ((((12020:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.331629107206 8.331629113216 (-2.0484438) 0.00000000604 (-0.4596912203128) (-0.8880788151749) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p02_3 : ‖exp (-((((((12020:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8027229075446:ℝ):ℂ) + (((-0.596352189317):ℝ):ℂ) * I)‖ ≤ 0.00000010771 := by
  have hl := lg_3
  refine (ecis_approx ((((12020:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.20531970666613128 13.2053197126761433 (-0.6389491) 0.0000000077 0.8027229075446 (-0.596352189317) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p02_4 : ‖exp (-((((((12020:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.577367958072):ℝ):ℂ) + ((0.8164840727053:ℝ):ℂ) * I)‖ ≤ 0.00000010714 := by
  have hl := lg_4
  refine (ecis_approx ((((12020:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.663258214412 16.663258226432 2.1862977 0.00000000713 (-0.577367958072) 0.8164840727053 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p02_5 : ‖exp (-((((((12020:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8795466300009:ℝ):ℂ) + (((-0.4758127001816):ℝ):ℂ) * I)‖ ≤ 0.00000012034 := by
  have hl := lg_5
  refine (ecis_approx ((((12020:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.34544370120879218 19.3454437132288042 (-0.4958878) 0.00000002033 0.8795466300009 (-0.4758127001816) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p02_6 : ‖exp (-((((((12020:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8986124186259):ℝ):ℂ) + (((-0.4387433429427):ℝ):ℂ) * I)‖ ≤ 0.00000010768 := by
  have hl := lg_6
  refine (ecis_approx ((((12020:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.53694881387213128 21.5369488258921433 (-2.6873929) 0.00000000767 (-0.8986124186259) (-0.4387433429427) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p02_7 : ‖exp (-((((((12020:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1712565037221):ℝ):ℂ) + ((0.9852264764673:ℝ):ℂ) * I)‖ ≤ 0.00000014334 := by
  have hl := lg_7
  refine (ecis_approx ((((12020:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.38983998539577244 23.38983999741579648 1.7429012 0.00000004333 (-0.1712565037221) 0.9852264764673 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p02_8 : ‖exp (-((((((12020:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9905131891207:ℝ):ℂ) + ((0.1374176923762:ℝ):ℂ) * I)‖ ≤ 0.00000011094 := by
  have hl := lg_8
  refine (ecis_approx ((((12020:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.994887321618 24.994887339648 0.1378539 0.00000001093 0.9905131891207 0.1374176923762 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p02_9 : ‖exp (-((((((12020:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2887281325936:ℝ):ℂ) + (((-0.9574111266583):ℝ):ℂ) * I)‖ ≤ 0.0000001154 := by
  have hl := lg_9
  refine (ecis_approx ((((12020:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.41063941333226256 26.4106394253522866 (-1.2778982) 0.00000001539 0.2887281325936 (-0.9574111266583) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p02_10 : ‖exp (-((((((12020:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8268790426771):ℝ):ℂ) + (((-0.562379808244):ℝ):ℂ) * I)‖ ≤ 0.00000012032 := by
  have hl := lg_10
  refine (ecis_approx ((((12020:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.67707280841479218 27.6770728264448042 (-2.5443316) 0.00000002031 (-0.8268790426771) (-0.562379808244) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p197_2 : ‖exp (-((((((12197:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5649185769685):ℝ):ℂ) + (((-0.825146654472):ℝ):ℂ) * I)‖ ≤ 0.00000014908 := by
  have hl := lg_2
  refine (ecis_approx ((((12197:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.4543161581191 8.4543161642176 (-2.1711309) 0.00000004907 (-0.5649185769685) (-0.825146654472) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p197_3 : ‖exp (-((((((12197:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6723603066853:ℝ):ℂ) + (((-0.7402240322997):ℝ):ℂ) * I)‖ ≤ 0.00000013266 := by
  have hl := lg_3
  refine (ecis_approx ((((12197:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.399774081714376308 13.399774087812888505 (-0.8334035) 0.00000003265 0.6723603066853 (-0.7402240322997) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p197_4 : ‖exp (-((((((12197:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3617340893254):ℝ):ℂ) + ((0.9322813140986:ℝ):ℂ) * I)‖ ≤ 0.00000010691 := by
  have hl := lg_4
  refine (ecis_approx ((((12197:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.9086323162382 16.9086323284352 1.9409236 0.0000000069 (-0.3617340893254) 0.9322813140986 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p197_5 : ‖exp (-((((((12197:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7103800368855:ℝ):ℂ) + (((-0.7038183026852):ℝ):ℂ) * I)‖ ≤ 0.00000010994 := by
  have hl := lg_5
  refine (ecis_approx ((((12197:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.630314211617607173 19.63031422381461937 (-0.7807583) 0.00000000993 0.7103800368855 (-0.7038183026852) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p197_6 : ‖exp (-((((((12197:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9906221976346):ℝ):ℂ) + (((-0.1366296495634):ℝ):ℂ) * I)‖ ≤ 0.00000013051 := by
  have hl := lg_6
  refine (ecis_approx ((((12197:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.854090239833476308 21.854090252030488505 (-3.0045343) 0.0000000305 (-0.9906221976346) (-0.1366296495634) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p197_7 : ‖exp (-((((((12197:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1714696569971:ℝ):ℂ) + ((0.9851894014499:ℝ):ℂ) * I)‖ ≤ 0.00000014705 := by
  have hl := lg_7
  refine (ecis_approx ((((12197:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.734266081686542134 23.734266093883566528 1.3984751 0.00000004704 0.1714696569971 0.9851894014499 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p197_8 : ‖exp (-((((((12197:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9736191143443:ℝ):ℂ) + (((-0.228179359679):ℝ):ℂ) * I)‖ ≤ 0.00000015438 := by
  have hl := lg_8
  refine (ecis_approx ((((12197:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.3629484743573 25.3629484926528 (-0.2302073) 0.00000005437 0.9736191143443 (-0.228179359679) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p197_9 : ‖exp (-((((((12197:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0958631364487):ℝ):ℂ) + (((-0.9953945243318):ℝ):ℂ) * I)‖ ≤ 0.00000014692 := by
  have hl := lg_9
  refine (ecis_approx ((((12197:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.799548163428752616 26.79954817562577701 (-1.6668069) 0.00000004691 (-0.0958631364487) (-0.9953945243318) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p197_10 : ‖exp (-((((((12197:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.982060197225):ℝ):ℂ) + (((-0.1885676766795):ℝ):ℂ) * I)‖ ≤ 0.000000159 := by
  have hl := lg_10
  refine (ecis_approx ((((12197:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.084630369736707173 28.08463038803221937 (-2.9518892) 0.00000005899 (-0.982060197225) (-0.1885676766795) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p374_2 : ‖exp (-((((((12374:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6616532945021):ℝ):ℂ) + (((-0.7498099211509):ℝ):ℂ) * I)‖ ≤ 0.00000010805 := by
  have hl := lg_2
  refine (ecis_approx ((((12374:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.5770032090322 8.5770032152192 (-2.2938179) 0.00000000804 (-0.6616532945021) (-0.7498099211509) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p374_3 : ‖exp (-((((((12374:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5166541682032:ℝ):ℂ) + (((-0.8561941780217):ℝ):ℂ) * I)‖ ≤ 0.00000014861 := by
  have hl := lg_3
  refine (ecis_approx ((((12374:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.594228456762621336 13.59422846294963371 (-1.0278578) 0.0000000486 0.5166541682032 (-0.8561941780217) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p374_4 : ‖exp (-((((((12374:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1244298286199):ℝ):ℂ) + ((0.9922284100695:ℝ):ℂ) * I)‖ ≤ 0.00000010891 := by
  have hl := lg_4
  refine (ecis_approx ((((12374:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.1540064180644 17.1540064304384 1.6955495 0.0000000089 (-0.1244298286199) 0.9922284100695 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p374_5 : ‖exp (-((((((12374:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4839540487089:ℝ):ℂ) + (((-0.8750934114358):ℝ):ℂ) * I)‖ ≤ 0.00000011288 := by
  have hl := lg_5
  refine (ecis_approx ((((12374:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.915184722026422166 19.91518473440043454 (-1.0656288) 0.00000001287 0.4839540487089 (-0.8750934114358) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p374_6 : ‖exp (-((((((12374:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9838288201992):ℝ):ℂ) + ((0.1791112843868:ℝ):ℂ) * I)‖ ≤ 0.00000014947 := by
  have hl := lg_6
  refine (ecis_approx ((((12374:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.171231665794821336 22.17123167816883371 2.9615096 0.00000004946 (-0.9838288201992) 0.1791112843868 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p374_7 : ‖exp (-((((((12374:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4940547821639:ℝ):ℂ) + ((0.8694307748297:ℝ):ℂ) * I)‖ ≤ 0.00000015076 := by
  have hl := lg_7
  refine (ecis_approx ((((12374:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.078692177977311828 24.078692190351336576 1.054049 0.00000005075 0.4940547821639 0.8694307748297 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p374_8 : ‖exp (-((((((12374:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8263121119692:ℝ):ℂ) + (((-0.5632124764358):ℝ):ℂ) * I)‖ ≤ 0.00000011695 := by
  have hl := lg_8
  refine (ecis_approx ((((12374:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.7310096270966 25.7310096456576 (-0.5982684) 0.00000001694 0.8263121119692 (-0.5632124764358) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p374_9 : ‖exp (-((((((12374:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4661370294277):ℝ):ℂ) + (((-0.8847125351159):ℝ):ℂ) * I)‖ ≤ 0.00000011521 := by
  have hl := lg_9
  refine (ecis_approx ((((12374:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.188456913525242672 27.18845692589926742 (-2.0557157) 0.0000000152 (-0.4661370294277) (-0.8847125351159) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p374_10 : ‖exp (-((((((12374:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9763635108808):ℝ):ℂ) + ((0.2161348984262:ℝ):ℂ) * I)‖ ≤ 0.00000011374 := by
  have hl := lg_10
  refine (ecis_approx ((((12374:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.492187931058622166 28.49218794961963454 2.9237386 0.00000001373 (-0.9763635108808) 0.2161348984262 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p551_2 : ‖exp (-((((((12551:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7484412928832):ℝ):ℂ) + (((-0.6632010487582):ℝ):ℂ) * I)‖ ≤ 0.00000014725 := by
  have hl := lg_2
  refine (ecis_approx ((((12551:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.6996902599453 8.6996902662208 (-2.416505) 0.00000004724 (-0.7484412928832) (-0.6632010487582) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p551_3 : ‖exp (-((((((12551:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3414734441083:ℝ):ℂ) + (((-0.939891422968):ℝ):ℂ) * I)‖ ≤ 0.00000012374 := by
  have hl := lg_3
  refine (ecis_approx ((((12551:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.788682831810866364 13.788682838086378915 (-1.2223122) 0.00000002373 0.3414734441083 (-0.939891422968) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p551_4 : ‖exp (-((((((12551:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.120328645656:ℝ):ℂ) + ((0.9927341119527:ℝ):ℂ) * I)‖ ≤ 0.00000011092 := by
  have hl := lg_4
  refine (ecis_approx ((((12551:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.3993805198906 17.3993805324416 1.4501754 0.00000001091 0.120328645656 0.9927341119527 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p551_5 : ‖exp (-((((((12551:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2185194811415:ℝ):ℂ) + (((-0.9758325862368):ℝ):ℂ) * I)‖ ≤ 0.00000012346 := by
  have hl := lg_5
  refine (ecis_approx ((((12551:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.200055232435237159 20.20005524498624971 (-1.3504993) 0.00000002345 0.2185194811415 (-0.9758325862368) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p551_6 : ‖exp (-((((((12551:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.878909799994):ℝ):ℂ) + ((0.4769880117773:ℝ):ℂ) * I)‖ ≤ 0.00000013698 := by
  have hl := lg_6
  refine (ecis_approx ((((12551:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.488373091756166364 22.488373104307178915 2.6443681 0.00000003697 (-0.878909799994) 0.4769880117773 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p551_7 : ‖exp (-((((((12551:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7586076285785:ℝ):ℂ) + ((0.6515477464181:ℝ):ℂ) * I)‖ ≤ 0.00000015447 := by
  have hl := lg_7
  refine (ecis_approx ((((12551:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.423118274268081522 24.423118286819106624 0.7096229 0.00000005446 0.7586076285785 0.6515477464181 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p551_8 : ‖exp (-((((((12551:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5683233770775:ℝ):ℂ) + (((-0.8228052862417):ℝ):ℂ) * I)‖ ≤ 0.0000001489 := by
  have hl := lg_8
  refine (ecis_approx ((((12551:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.0990707798359 26.0990707986624 (-0.9663296) 0.00000004889 0.5683233770775 (-0.8228052862417) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p551_9 : ‖exp (-((((((12551:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7667917739307):ℝ):ℂ) + (((-0.6418959225559):ℝ):ℂ) * I)‖ ≤ 0.00000014747 := by
  have hl := lg_9
  refine (ecis_approx ((((12551:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.577365663621732728 27.57736567617275783 (-2.4446244) 0.00000004746 (-0.7667917739307) (-0.6418959225559) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p551_10 : ‖exp (-((((((12551:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8107221933954):ℝ):ℂ) + ((0.5854310592055:ℝ):ℂ) * I)‖ ≤ 0.00000014353 := by
  have hl := lg_10
  refine (ecis_approx ((((12551:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.899745492380537159 28.89974551120704971 2.516181 0.00000004352 (-0.8107221933954) 0.5854310592055 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_2 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8239777269574):ℝ):ℂ) + (((-0.5666221893101):ℝ):ℂ) * I)‖ ≤ 0.00000011006 := by
  have hl := lg_2
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.8223773108584 8.8223773172224 (-2.539192) 0.00000001005 (-0.8239777269574) (-0.5666221893101) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_3 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1534213856579:ℝ):ℂ) + (((-0.9881608565526):ℝ):ℂ) * I)‖ ≤ 0.00000010752 := by
  have hl := lg_3
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.983137206859111392 13.98313721322312412 (-1.4167666) 0.00000000751 0.1534213856579 (-0.9881608565526) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_4 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3578785957918:ℝ):ℂ) + ((0.933768124683:ℝ):ℂ) * I)‖ ≤ 0.00000011292 := by
  have hl := lg_4
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.6447546217168 17.6447546344448 1.2048013 0.00000001291 0.3578785957918 0.933768124683 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_5 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0645286068651):ℝ):ℂ) + (((-0.9979158576231):ℝ):ℂ) * I)‖ ≤ 0.00000013405 := by
  have hl := lg_5
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.484925742844052152 20.48492575557206488 (-1.6353698) 0.00000003404 (-0.0645286068651) (-0.9979158576231) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_6 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6863296673619):ℝ):ℂ) + ((0.7272905799454:ℝ):ℂ) * I)‖ ≤ 0.00000011102 := by
  have hl := lg_6
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.805514517717511392 22.80551453044552412 2.3272267 0.00000001101 (-0.6863296673619) 0.7272905799454 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_7 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9340534597412:ℝ):ℂ) + ((0.3571332165249:ℝ):ℂ) * I)‖ ≤ 0.00000015458 := by
  have hl := lg_7
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.767544370558851216 24.767544383286876672 0.3651969 0.00000005457 0.9340534597412 0.3571332165249 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_8 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2342097472549:ℝ):ℂ) + (((-0.9721860903607):ℝ):ℂ) * I)‖ ≤ 0.00000012296 := by
  have hl := lg_8
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.4671319325752 26.4671319516672 (-1.3343907) 0.00000002295 0.2342097472549 (-0.9721860903607) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_9 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9529237567695):ℝ):ℂ) + (((-0.3032100156211):ℝ):ℂ) * I)‖ ≤ 0.00000011502 := by
  have hl := lg_9
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.966274413718222784 27.96627442644624824 (-2.8335332) 0.00000001501 (-0.9529237567695) (-0.3032100156211) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_10 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5122711270514):ℝ):ℂ) + ((0.8588237842437:ℝ):ℂ) * I)‖ ≤ 0.00000013691 := by
  have hl := lg_10
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.307303053702452152 29.30730307279446488 2.1086235 0.0000000369 (-0.5122711270514) 0.8588237842437 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_11 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6251165355148:ℝ):ℂ) + ((0.7805314324394:ℝ):ℂ) * I)‖ ≤ 0.00000011366 := by
  have hl := lg_11
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.520411022251888024 30.52041104134391348 0.8955155 0.00000001365 0.6251165355148 0.7805314324394 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_12 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.977619339972:ℝ):ℂ) + (((-0.2103816201874):ℝ):ℂ) * I)‖ ≤ 0.00000011178 := by
  have hl := lg_12
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.627891828575911392 31.62789184766792412 (-0.2119653) 0.00000001177 0.977619339972 (-0.2103816201874) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_13 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3335318035979:ℝ):ℂ) + (((-0.9427388482442):ℝ):ℂ) * I)‖ ≤ 0.00000012407 := by
  have hl := lg_13
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.6466754118446776 32.646675430936703056 (-1.2307489) 0.00000002406 0.3335318035979 (-0.9427388482442) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_14 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5672797239442):ℝ):ℂ) + (((-0.8235251755667):ℝ):ℂ) * I)‖ ≤ 0.0000001545 := by
  have hl := lg_14
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.589921681417251216 33.589921700509276672 (-2.1739952) 0.00000005449 (-0.5672797239442) (-0.8235251755667) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p728_15 : ‖exp (-((((((12728:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9960014566886):ℝ):ℂ) + (((-0.089336989983):ℝ):ℂ) * I)‖ ≤ 0.00000013291 := by
  have hl := lg_15
  refine (ecis_approx ((((12728:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.468062949703163544 34.468062968795189 (-3.0521364) 0.0000000329 (-0.9960014566886) (-0.089336989983) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_2 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8871271613461):ℝ):ℂ) + (((-0.4615250800327):ℝ):ℂ) * I)‖ ≤ 0.00000014542 := by
  have hl := lg_2
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.9450643617715 8.945064368224 (-2.6618791) 0.00000004541 (-0.8871271613461) (-0.4615250800327) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_3 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0404136640798):ℝ):ℂ) + (((-0.9991830341611):ℝ):ℂ) * I)‖ ≤ 0.00000013247 := by
  have hl := lg_3
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.17759158190735642 14.177591588359869325 (-1.611221) 0.00000003246 (-0.0404136640798) (-0.9991830341611) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_4 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5739891248912:ℝ):ℂ) + ((0.8188629216826:ℝ):ℂ) * I)‖ ≤ 0.00000011492 := by
  have hl := lg_4
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.890128723543 17.890128736448 0.9594272 0.00000001491 0.5739891248912 0.8188629216826 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_5 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3423754380776):ℝ):ℂ) + (((-0.9395632279942):ℝ):ℂ) * I)‖ ≤ 0.00000014463 := by
  have hl := lg_5
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.769796253252867145 20.76979626615788005 (-1.9202403) 0.00000004462 (-0.3423754380776) (-0.9395632279942) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_6 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4252960547762):ℝ):ℂ) + ((0.9050542888622:ℝ):ℂ) * I)‖ ≤ 0.00000012788 := by
  have hl := lg_6
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.12265594367885642 23.122655956583869325 2.0100853 0.00000002787 (-0.4252960547762) 0.9050542888622 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_7 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997842946889:ℝ):ℂ) + ((0.0207693065212:ℝ):ℂ) * I)‖ ≤ 0.00000015105 := by
  have hl := lg_7
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.11197046684962091 25.11197047975464672 0.0207708 0.00000005104 0.9997842946889 0.0207693065212 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_8 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1312755675138):ℝ):ℂ) + (((-0.9913459161026):ℝ):ℂ) * I)‖ ≤ 0.00000014342 := by
  have hl := lg_8
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.8351930853145 26.835193104672 (-1.7024519) 0.00000004341 (-0.1312755675138) (-0.9913459161026) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_9 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9967334787705):ℝ):ℂ) + ((0.0807612022383:ℝ):ℂ) * I)‖ ≤ 0.00000014084 := by
  have hl := lg_9
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.35518316381471284 28.35518317671973865 3.0607434 0.00000004083 (-0.9967334787705) 0.0807612022383 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_10 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.129901436424):ℝ):ℂ) + ((0.9915269117954:ℝ):ℂ) * I)‖ ≤ 0.00000012089 := by
  have hl := lg_10
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.714860615024367145 29.71486063438188005 1.7010659 0.00000002088 (-0.129901436424) 0.9915269117954 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_11 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8910750203198:ℝ):ℂ) + ((0.4538560434346:ℝ):ℂ) * I)‖ ≤ 0.00000015051 := by
  have hl := lg_11
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.944838485399168365 30.944838504756694175 0.471088 0.0000000505 0.8910750203198 0.4538560434346 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_12 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7949969349702:ℝ):ℂ) + (((-0.6066134464286):ℝ):ℂ) * I)‖ ≤ 0.00000013046 := by
  have hl := lg_12
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.06772030545035642 32.067720324807869325 (-0.6517938) 0.00000003045 0.7949969349702 (-0.6066134464286) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_13 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1137021432659):ℝ):ℂ) + (((-0.9935148829365):ℝ):ℂ) * I)‖ ≤ 0.00000013145 := by
  have hl := lg_13
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.1006714479773385 33.10067146733486431 (-1.6847449) 0.00000003144 (-0.1137021432659) (-0.9935148829365) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_14 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8773502474536):ℝ):ℂ) + (((-0.4798505425642):ℝ):ℂ) * I)‖ ≤ 0.0000001121 := by
  have hl := lg_14
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.05703482862112091 34.05703484797864672 (-2.6411083) 0.00000001209 (-0.8773502474536) (-0.4798505425642) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v12p905_15 : ‖exp (-((((((12905:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9249589882138):ℝ):ℂ) + ((0.3800669282792:ℝ):ℂ) * I)‖ ≤ 0.00000011146 := by
  have hl := lg_15
  refine (ecis_approx ((((12905:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.947387835160223565 34.947387854517749375 2.751724 0.00000001145 (-0.9249589882138) 0.3800669282792 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_2 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.936940153322):ℝ):ℂ) + (((-0.3494898409395):ℝ):ℂ) * I)‖ ≤ 0.00000011206 := by
  have hl := lg_2
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.0677514126846 9.0677514192256 (-2.7845661) 0.00000001205 (-0.936940153322) (-0.3494898409395) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_3 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2327252835138):ℝ):ℂ) + (((-0.9725425144498):ℝ):ℂ) * I)‖ ≤ 0.00000014915 := by
  have hl := lg_3
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.372045956955601448 14.37204596349661453 (-1.8056753) 0.00000004914 (-0.2327252835138) (-0.9725425144498) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_4 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.755713706735:ℝ):ℂ) + ((0.6549021250942:ℝ):ℂ) * I)‖ ≤ 0.00000011693 := by
  have hl := lg_4
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.1355028253692 18.1355028384512 0.7140531 0.00000001692 0.755713706735 0.6549021250942 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_5 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5926254767975):ℝ):ℂ) + (((-0.8054781463448):ℝ):ℂ) * I)‖ ≤ 0.00000015522 := by
  have hl := lg_5
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.054666763661682138 21.05466677674369522 (-2.2051108) 0.00000005521 (-0.5926254767975) (-0.8054781463448) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_6 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1218440588138):ℝ):ℂ) + ((0.9925492558716:ℝ):ℂ) * I)‖ ≤ 0.00000015402 := by
  have hl := lg_6
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.439797369640201448 23.43979738272221453 1.6929439 0.00000005401 (-0.1218440588138) 0.9925492558716 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_7 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9480792440303:ℝ):ℂ) + (((-0.3180341916193):ℝ):ℂ) * I)‖ ≤ 0.00000014752 := by
  have hl := lg_7
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.456396563140390604 25.456396576222416768 (-0.3236553) 0.00000004751 0.9480792440303 (-0.3180341916193) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_8 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4791768767102):ℝ):ℂ) + (((-0.8777183607631):ℝ):ℂ) * I)‖ ≤ 0.00000012897 := by
  have hl := lg_8
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.2032542380538 27.2032542576768 (-2.070513) 0.00000002896 (-0.4791768767102) (-0.8777183607631) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_9 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8916778362793):ℝ):ℂ) + ((0.4526705603206:ℝ):ℂ) * I)‖ ≤ 0.000000122 := by
  have hl := lg_9
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.744091913911202896 28.74409192699322906 2.6718346 0.00000002199 (-0.8916778362793) 0.4526705603206 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_10 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2737482788922:ℝ):ℂ) + ((0.9618013723236:ℝ):ℂ) * I)‖ ≤ 0.00000015957 := by
  have hl := lg_10
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.122418176346282138 30.12241819596929522 1.2935083 0.00000005956 0.2737482788922 0.9618013723236 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_11 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9989115916999:ℝ):ℂ) + ((0.0466436701766:ℝ):ℂ) * I)‖ ≤ 0.00000013229 := by
  have hl := lg_11
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.369265948546448706 31.36926596816947487 0.0466606 0.00000003228 0.9989115916999 0.0466436701766 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_12 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4610463840653:ℝ):ℂ) + (((-0.8873760373936):ℝ):ℂ) * I)‖ ≤ 0.00000015359 := by
  have hl := lg_12
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.507548782324801448 32.50754880194781453 (-1.0916223) 0.00000005358 0.4610463840653 (-0.8873760373936) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_13 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5379005285172):ℝ):ℂ) + (((-0.8430083163367):ℝ):ℂ) * I)‖ ≤ 0.0000001518 := by
  have hl := lg_13
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.5546674841099994 33.554667503733025564 (-2.138741) 0.00000005179 (-0.5379005285172) (-0.8430083163367) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_14 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9994432310943):ℝ):ℂ) + (((-0.0333650597287):ℝ):ℂ) * I)‖ ≤ 0.00000015957 := by
  have hl := lg_14
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.524147975824990604 34.524147995448016768 (-3.1082214) 0.00000005956 (-0.9994432310943) (-0.0333650597287) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p082_15 : ‖exp (-((((((13082:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6454427278157):ℝ):ℂ) + ((0.7638086704755:ℝ):ℂ) * I)‖ ≤ 0.00000012248 := by
  have hl := lg_15
  refine (ecis_approx ((((13082:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.426712720617283586 35.42671274024030975 2.2723991 0.00000002247 (-0.6454427278157) 0.7638086704755 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_2 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9649532506067):ℝ):ℂ) + (((-0.2624218433987):ℝ):ℂ) * I)‖ ≤ 0.00000013993 := by
  have hl := lg_2
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.1592468404842 9.1592468470912 (-2.8760615) 0.00000003992 (-0.9649532506067) (-0.2624218433987) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_3 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3708237685304):ℝ):ℂ) + (((-0.9287032533001):ℝ):ℂ) * I)‖ ≤ 0.00000013535 := by
  have hl := lg_3
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.517062779025479096 14.51706278563249231 (-1.9506922) 0.00000003534 (-0.3708237685304) (-0.9287032533001) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_4 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8622696063616:ℝ):ℂ) + ((0.5064495295141:ℝ):ℂ) * I)‖ ≤ 0.00000014059 := by
  have hl := lg_4
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.3184936809684 18.3184936941824 0.5310622 0.00000004058 0.8622696063616 0.5064495295141 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_5 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7491383673823):ℝ):ℂ) + (((-0.6624135464211):ℝ):ℂ) * I)‖ ≤ 0.00000015352 := by
  have hl := lg_5
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.267112568034357726 21.26711258124837094 (-2.4175567) 0.00000005351 (-0.7491383673823) (-0.6624135464211) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_6 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1141155881933:ℝ):ℂ) + ((0.9934674793526:ℝ):ℂ) * I)‖ ≤ 0.00000010922 := by
  have hl := lg_6
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.676309619509679096 23.67630963272369231 1.4564316 0.00000000921 0.1141155881933 0.9934674793526 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_7 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8361800324474:ℝ):ℂ) + (((-0.5484550604528):ℝ):ℂ) * I)‖ ≤ 0.00000012599 := by
  have hl := lg_7
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.713256702747066308 25.713256715961092736 (-0.5805155) 0.00000002598 0.8361800324474 (-0.5484550604528) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_8 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6991464404488):ℝ):ℂ) + (((-0.7149784995258):ℝ):ℂ) * I)‖ ≤ 0.00000011257 := by
  have hl := lg_8
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.4777405214526 27.4777405412736 (-2.3449993) 0.00000001256 (-0.6991464404488) (-0.7149784995258) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_9 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7249795293137):ℝ):ℂ) + ((0.6887704131624:ℝ):ℂ) * I)‖ ≤ 0.00000013538 := by
  have hl := lg_9
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.034125558050958192 29.03412557126498462 2.381801 0.00000003537 (-0.7249795293137) 0.6887704131624 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_10 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5490517248035:ℝ):ℂ) + ((0.8357883724307:ℝ):ℂ) * I)‖ ≤ 0.00000012739 := by
  have hl := lg_10
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.426359408518557726 30.42635942833957094 0.9895671 0.00000002738 0.5490517248035 0.8357883724307 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_11 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9638078027663:ℝ):ℂ) + (((-0.2665980482426):ℝ):ℂ) * I)‖ ≤ 0.00000011146 := by
  have hl := lg_11
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.685788124452895062 31.68578814427392149 (-0.2698616) 0.00000001145 0.9638078027663 (-0.2665980482426) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_12 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1505913596323:ℝ):ℂ) + (((-0.9885960966967):ℝ):ℂ) * I)‖ ≤ 0.00000014393 := by
  have hl := lg_12
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.835556459993879096 32.83555647981489231 (-1.4196299) 0.00000004392 0.1505913596323 (-0.9885960966967) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_13 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7873618786864):ℝ):ℂ) + (((-0.6164910964051):ℝ):ℂ) * I)‖ ≤ 0.00000013672 := by
  have hl := lg_13
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.8932407991919838 33.893240819013010228 (-2.4773143) 0.00000003671 (-0.7873618786864) (-0.6164910964051) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_14 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9508012262399):ℝ):ℂ) + ((0.309801594533:ℝ):ℂ) * I)‖ ≤ 0.00000011999 := by
  have hl := lg_14
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.872503543231266308 34.872503563052292736 2.8266083 0.00000001998 (-0.9508012262399) 0.309801594533 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p214_15 : ‖exp (-((((((13214:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3373873904427):ℝ):ℂ) + ((0.941365895265:ℝ):ℂ) * I)‖ ≤ 0.00000012382 := by
  have hl := lg_15
  refine (ecis_approx ((((13214:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.784175347059836822 35.78417536688086325 1.9149365 0.00000002381 (-0.3373873904427) 0.941365895265 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_2 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9848939814049):ℝ):ℂ) + (((-0.1731584391053):ℝ):ℂ) * I)‖ ≤ 0.00000013891 := by
  have hl := lg_2
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.2507422682838 9.2507422749568 (-2.967557) 0.0000000389 (-0.9848939814049) (-0.1731584391053) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_3 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5011374367963):ℝ):ℂ) + (((-0.8653677076451):ℝ):ℂ) * I)‖ ≤ 0.00000011328 := by
  have hl := lg_3
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.662079601095356744 14.66207960776837009 (-2.095709) 0.00000001327 (-0.5011374367963) (-0.8653677076451) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_4 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.940032278152:ℝ):ℂ) + ((0.3410854966609:ℝ):ℂ) * I)‖ ≤ 0.00000012839 := by
  have hl := lg_4
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.5014845365676 18.5014845499136 0.3480714 0.00000002838 0.940032278152 0.3410854966609 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_5 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8719671277419):ℝ):ℂ) + (((-0.4895644268613):ℝ):ℂ) * I)‖ ≤ 0.00000014915 := by
  have hl := lg_5
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.479558372407033314 21.47955838575304666 (-2.6300025) 0.00000004914 (-0.8719671277419) (-0.4895644268613) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_6 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3437214366079:ℝ):ℂ) + ((0.9390716554216:ℝ):ℂ) * I)‖ ≤ 0.00000015402 := by
  have hl := lg_6
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.912821869379156744 23.91282188272517009 1.2199194 0.00000005401 0.3437214366079 0.9390716554216 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_7 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6694147664365:ℝ):ℂ) + (((-0.7428888681874):ℝ):ℂ) * I)‖ ≤ 0.000000127 := by
  have hl := lg_7
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.970116842353742012 25.970116855699768704 (-0.8373756) 0.00000002699 0.6694147664365 (-0.7428888681874) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_8 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8667703009351):ℝ):ℂ) + (((-0.498707574969):ℝ):ℂ) * I)‖ ≤ 0.00000012388 := by
  have hl := lg_8
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.7522268048514 27.7522268248704 (-2.6194856) 0.00000002387 (-0.8667703009351) (-0.498707574969) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_9 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.497722532655):ℝ):ℂ) + ((0.8673363133648:ℝ):ℂ) * I)‖ ≤ 0.00000013372 := by
  have hl := lg_9
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.324159202190713488 29.32415921553674018 2.0917673 0.00000003371 (-0.497722532655) 0.8673363133648 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_10 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7740229053902:ℝ):ℂ) + ((0.6331575964412:ℝ):ℂ) * I)‖ ≤ 0.00000012483 := by
  have hl := lg_10
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.730300640690833314 30.73030066070984666 0.6856259 0.00000002482 0.7740229053902 0.6331575964412 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_11 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8329471543871:ℝ):ℂ) + (((-0.5533525440426):ℝ):ℂ) * I)‖ ≤ 0.00000013555 := by
  have hl := lg_11
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.002310300359341418 32.00231032037836811 (-0.5863838) 0.00000003554 0.8329471543871 (-0.5533525440426) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_12 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1759209920214):ℝ):ℂ) + (((-0.9844042891848):ℝ):ℂ) * I)‖ ≤ 0.0000001218 := by
  have hl := lg_12
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.163564137662956744 33.16356415768197009 (-1.7476376) 0.00000002179 (-0.1759209920214) (-0.9844042891848) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_13 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9474253610196):ℝ):ℂ) + (((-0.3199768508816):ℝ):ℂ) * I)‖ ≤ 0.00000012164 := by
  have hl := lg_13
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.2318141142739682 34.231814134292994892 (-2.8158876) 0.00000002163 (-0.9474253610196) (-0.3199768508816) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_14 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.787940047173):ℝ):ℂ) + ((0.6157519646872:ℝ):ℂ) * I)‖ ≤ 0.00000013245 := by
  have hl := lg_14
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.220859110637542012 35.220859130656568704 2.4782527 0.00000003244 (-0.787940047173) 0.6157519646872 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p346_15 : ‖exp (-((((((13346:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0133220327053:ℝ):ℂ) + ((0.9999112577846:ℝ):ℂ) * I)‖ ≤ 0.00000015046 := by
  have hl := lg_15
  refine (ecis_approx ((((13346:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.141637973502390058 36.14163799352141675 1.5574739 0.00000005045 0.0133220327053 0.9999112577846 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_2 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9944490709841):ℝ):ℂ) + (((-0.1052190322735):ℝ):ℂ) * I)‖ ≤ 0.00000013869 := by
  have hl := lg_2
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.3193638391335 9.319363845856 (-3.0361785) 0.00000003868 (-0.9944490709841) (-0.1052190322735) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_3 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5921104941349):ℝ):ℂ) + (((-0.805856787974):ℝ):ℂ) * I)‖ ≤ 0.00000011003 := by
  have hl := lg_3
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.77084221764776498 14.770842224370278425 (-2.2044716) 0.00000001002 (-0.5921104941349) (-0.805856787974) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_4 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9778579328317:ℝ):ℂ) + ((0.2092698334642:ℝ):ℂ) * I)‖ ≤ 0.00000014329 := by
  have hl := lg_4
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.638727678267 18.638727691712 0.2108282 0.00000004328 0.9778579328317 0.2092698334642 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_5 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9385967960193):ℝ):ℂ) + (((-0.3450160203903):ℝ):ℂ) * I)‖ ≤ 0.00000011761 := by
  have hl := lg_5
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.638892725686540005 21.63889273913155345 (-2.7893368) 0.0000000176 (-0.9385967960193) (-0.3450160203903) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_6 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5040322655795:ℝ):ℂ) + ((0.8636848240271:ℝ):ℂ) * I)‖ ≤ 0.00000014152 := by
  have hl := lg_6
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.09020605678126498 24.090206070226278425 1.0425352 0.00000004151 0.5040322655795 0.8636848240271 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_7 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5148010987706:ℝ):ℂ) + (((-0.857309645755):ℝ):ℂ) * I)‖ ≤ 0.0000001318 := by
  have hl := lg_7
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.16276194705874879 26.16276196050377568 (-1.0300207) 0.00000003179 0.5148010987706 (-0.857309645755) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_8 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9504107435853):ℝ):ℂ) + (((-0.3109974570204):ℝ):ℂ) * I)‖ ≤ 0.00000011133 := by
  have hl := lg_8
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.9580915174005 27.958091537568 (-2.8253503) 0.00000001132 (-0.9504107435853) (-0.3109974570204) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_9 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2988103186172):ℝ):ℂ) + ((0.954312524012:ℝ):ℂ) * I)‖ ≤ 0.00000011286 := by
  have hl := lg_9
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.54168443529552996 29.54168444874055685 1.8742421 0.00000001285 (-0.2988103186172) 0.954312524012 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_10 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8970844633902:ℝ):ℂ) + ((0.441859101461:ℝ):ℂ) * I)‖ ≤ 0.0000001491 := by
  have hl := lg_10
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.958256564820040005 30.95825658498755345 0.45767 0.00000004909 0.8970844633902 0.441859101461 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_11 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6794559838159:ℝ):ℂ) + (((-0.7337162708137):ℝ):ℂ) * I)‖ ≤ 0.00000011657 := by
  have hl := lg_11
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.239701932289176185 32.239701952456703075 (-0.8237754) 0.00000001656 0.6794559838159 (-0.7337162708137) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_12 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.410358427987):ℝ):ℂ) + (((-0.9119243173513):ℝ):ℂ) * I)‖ ≤ 0.00000014 := by
  have hl := lg_12
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.40956989591476498 33.409569916082278425 (-1.9936434) 0.00000003999 (-0.410358427987) (-0.9119243173513) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_13 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9974252762198):ℝ):ℂ) + (((-0.0717134424583):ℝ):ℂ) * I)‖ ≤ 0.00000013533 := by
  have hl := lg_13
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.4857441005854565 34.48574412075298339 (-3.0698176) 0.00000003532 (-0.9974252762198) (-0.0717134424583) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_14 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.602148680425):ℝ):ℂ) + ((0.7983839719397:ℝ):ℂ) * I)‖ ≤ 0.0000001569 := by
  have hl := lg_14
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.48212578619224879 35.48212580635977568 2.216986 0.00000005689 (-0.602148680425) 0.7983839719397 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_15 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2777195175497:ℝ):ℂ) + ((0.9606622036762:ℝ):ℂ) * I)‖ ≤ 0.00000012044 := by
  have hl := lg_15
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.409734943334304985 36.409734963501831875 1.2893769 0.00000002043 0.2777195175497 0.9606622036762 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p445_16 : ‖exp (-((((((13445:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9124122326765:ℝ):ℂ) + ((0.4092724247518:ℝ):ℂ) * I)‖ ≤ 0.00000014036 := by
  have hl := lg_16
  refine (ecis_approx ((((13445:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.277455356534 37.277455383424 0.4216565 0.00000004035 0.9124122326765 0.4092724247518 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
