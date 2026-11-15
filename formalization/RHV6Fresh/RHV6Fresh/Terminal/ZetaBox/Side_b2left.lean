/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox.Base
/-!
# Certificat (V2), côté b2left (b2)

Fichier GENERE par `experiments/e192_zeta_box_certificate_generator.py` : constantes rationnelles calculees en
arithmetique exacte puis verifiees par Lean (`norm_num`, `linarith`, `decide`). Aucune preuve admise, aucun axiome ajoute.
-/

set_option maxHeartbeats 4000000
set_option linter.style.longLine false

namespace RHV6Fresh
namespace ZB
namespace Cert

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

lemma cs_b2left_vm0p768_2 : ‖exp (-((((((-768:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8616232840327:ℝ):ℂ) + ((0.5075483389912:ℝ):ℂ) * I)‖ ≤ 0.00000013487 := by
  have hl := lg_2
  refine (ecis_approx ((((-768:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.5323370348544) (-0.5323370344704) 0.532337 0.00000003486 0.8616232840327 0.5075483389912 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p768_3 : ‖exp (-((((((-768:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6646775323363:ℝ):ℂ) + ((0.7471303621238:ℝ):ℂ) * I)‖ ≤ 0.0000001379 := by
  have hl := lg_3
  refine (ecis_approx ((((-768:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.84373423788147072) (-0.843734237497469952) 0.8437342 0.00000003789 0.6646775323363 0.7471303621238 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p768_4 : ‖exp (-((((((-768:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4847892797114:ℝ):ℂ) + ((0.8746309817728:ℝ):ℂ) * I)‖ ≤ 0.00000013107 := by
  have hl := lg_4
  refine (ecis_approx ((((-768:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-1.0646740697088) (-1.0646740689408) 1.0646741 0.00000003106 0.4847892797114 0.8746309817728 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p768_5 : ‖exp (-((((((-768:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3285311933469:ℝ):ℂ) + ((0.9444931206727:ℝ):ℂ) * I)‖ ≤ 0.00000011713 := by
  have hl := lg_5
  refine (ecis_approx ((((-768:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-1.23604831711811328) (-1.236048316350112512) 1.2360483 0.00000001712 0.3285311933469 0.9444931206727 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p471_2 : ‖exp (-((((((-471:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9471795811637:ℝ):ℂ) + ((0.3207036654399:ℝ):ℂ) * I)‖ ≤ 0.00000012217 := by
  have hl := lg_2
  refine (ecis_approx ((((-471:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.3264723221568) (-0.3264723219213) 0.3264723 0.00000002216 0.9471795811637 0.3207036654399 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p471_3 : ‖exp (-((((((-471:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8690851819509:ℝ):ℂ) + ((0.4946624571497:ℝ):ℂ) * I)‖ ≤ 0.00000011217 := by
  have hl := lg_3
  refine (ecis_approx ((((-471:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.517446388075745715) (-0.517446387840245244) 0.5174464 0.00000001216 0.8690851819509 0.4946624571497 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p471_4 : ‖exp (-((((((-471:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7942983179468:ℝ):ℂ) + ((0.607527927018:ℝ):ℂ) * I)‖ ≤ 0.00000014433 := by
  have hl := lg_4
  refine (ecis_approx ((((-471:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.6529446443136) (-0.6529446438426) 0.6529446 0.00000004432 0.7942983179468 0.607527927018 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p471_5 : ‖exp (-((((((-471:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.726181259887:ℝ):ℂ) + ((0.6875032929296:ℝ):ℂ) * I)‖ ≤ 0.0000001435 := by
  have hl := lg_5
  refine (ecis_approx ((((-471:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.75804525698259291) (-0.758045256511592439) 0.7580453 0.00000004349 0.726181259887 0.6875032929296 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p228_2 : ‖exp (-((((((-228:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9875380283113:ℝ):ℂ) + ((0.1573805662686:ℝ):ℂ) * I)‖ ≤ 0.00000014291 := by
  have hl := lg_2
  refine (ecis_approx ((((-228:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.1580375572224) (-0.1580375571084) 0.1580376 0.0000000429 0.9875380283113 0.1573805662686 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p228_3 : ‖exp (-((((((-228:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9687926638613:ℝ):ℂ) + ((0.2478724963533:ℝ):ℂ) * I)‖ ≤ 0.00000010189 := by
  have hl := lg_3
  refine (ecis_approx ((((-228:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.25048360187106162) (-0.250483601757061392) 0.2504836 0.00000000188 0.9687926638613 0.2478724963533 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p228_4 : ‖exp (-((((((-228:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9504627458058:ℝ):ℂ) + ((0.3108384931685:ℝ):ℂ) * I)‖ ≤ 0.00000011446 := by
  have hl := lg_4
  refine (ecis_approx ((((-228:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.3160751144448) (-0.3160751142168) 0.3160751 0.00000001445 0.9504627458058 0.3108384931685 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p228_5 : ‖exp (-((((((-228:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9334252886915:ℝ):ℂ) + ((0.3587718361733:ℝ):ℂ) * I)‖ ≤ 0.00000014416 := by
  have hl := lg_5
  refine (ecis_approx ((((-228:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.36695184414443988) (-0.366951843916439652) 0.3669518 0.00000004415 0.9334252886915 0.3587718361733 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p063_2 : ‖exp (-((((((-63:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9990466912923:ℝ):ℂ) + ((0.043654422661:ℝ):ℂ) * I)‖ ≤ 0.00000012766 := by
  have hl := lg_2
  refine (ecis_approx ((((-63:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.0436682723904) (-0.0436682723589) 0.0436683 0.00000002765 0.9990466912923 0.043654422661 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p063_3 : ‖exp (-((((((-63:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9976057640054:ℝ):ℂ) + ((0.0691573540789:ℝ):ℂ) * I)‖ ≤ 0.00000012585 := by
  have hl := lg_3
  refine (ecis_approx ((((-63:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.069212574201214395) (-0.069212574169714332) 0.0692126 0.00000002584 0.9976057640054 0.0691573540789 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p063_4 : ‖exp (-((((((-63:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9961885914868:ℝ):ℂ) + ((0.0872255134207:ℝ):ℂ) * I)‖ ≤ 0.0000001448 := by
  have hl := lg_4
  refine (ecis_approx ((((-63:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.0873365447808) (-0.0873365447178) 0.0873365 0.00000004479 0.9961885914868 0.0872255134207 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_vm0p063_5 : ‖exp (-((((((-63:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9948639700441:ℝ):ℂ) + ((0.1012209519225:ℝ):ℂ) * I)‖ ≤ 0.00000011156 := by
  have hl := lg_5
  refine (ecis_approx ((((-63:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.10139458851359523) (-0.101394588450595167) 0.1013946 0.00000001155 0.9948639700441 0.1012209519225 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p173_2 : ‖exp (-((((((173:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9928188676187:ℝ):ℂ) + (((-0.1196273217131):ℝ):ℂ) * I)‖ ≤ 0.00000013782 := by
  have hl := lg_2
  refine (ecis_approx ((((173:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.1199144621919 0.1199144622784 (-0.1199145) 0.00000003781 0.9928188676187 (-0.1196273217131) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p173_3 : ‖exp (-((((((173:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9819929207077:ℝ):ℂ) + (((-0.1889177166913):ℝ):ℂ) * I)‖ ≤ 0.000000126 := by
  have hl := lg_3
  refine (ecis_approx ((((173:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.190059925894612372 0.190059925981112545 (-0.1900599) 0.00000002599 0.9819929207077 (-0.1889177166913) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p173_4 : ‖exp (-((((((173:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9713786315532:ℝ):ℂ) + (((-0.2375364270211):ℝ):ℂ) * I)‖ ≤ 0.00000012457 := by
  have hl := lg_4
  refine (ecis_approx ((((173:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.2398289243838 0.2398289245568 (-0.2398289) 0.00000002456 0.9713786315532 (-0.2375364270211) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p173_5 : ‖exp (-((((((173:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9614873624744:ℝ):ℂ) + (((-0.2748491437171):ℝ):ℂ) * I)‖ ≤ 0.00000014125 := by
  have hl := lg_5
  refine (ecis_approx ((((173:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 0.278432758761158157 0.27843275893415833 (-0.2784328) 0.00000004124 0.9614873624744 (-0.2748491437171) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p35_2 : ‖exp (-((((((350:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9707163052571:ℝ):ℂ) + (((-0.2402287549567):ℝ):ℂ) * I)‖ ≤ 0.00000011329 := by
  have hl := lg_2
  refine (ecis_approx ((((350:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.242601513105 0.24260151328 (-0.2426015) 0.00000001328 0.9707163052571 (-0.2402287549567) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p35_3 : ‖exp (-((((((350:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9269807324208:ℝ):ℂ) + (((-0.3751089464684):ℝ):ℂ) * I)‖ ≤ 0.00000010113 := by
  have hl := lg_3
  refine (ecis_approx ((((350:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.3845143009428574 0.38451430111785775 (-0.3845143) 0.00000000112 0.9269807324208 (-0.3751089464684) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p35_4 : ‖exp (-((((((350:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8845802905839:ℝ):ℂ) + (((-0.4663879388561):ℝ):ℂ) * I)‖ ≤ 0.00000012657 := by
  have hl := lg_4
  refine (ecis_approx ((((350:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.48520302621 0.48520302656 (-0.485203) 0.00000002656 0.8845802905839 (-0.4663879388561) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p35_5 : ‖exp (-((((((350:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8454958243058:ℝ):ℂ) + (((-0.5339820325455):ℝ):ℂ) * I)‖ ≤ 0.00000013085 := by
  have hl := lg_5
  refine (ecis_approx ((((350:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 0.56330326916997315 0.5633032695199735 (-0.5633033) 0.00000003084 0.8454958243058 (-0.5339820325455) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p665_2 : ‖exp (-((((((665:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8956335005951:ℝ):ℂ) + (((-0.4447927973919):ℝ):ℂ) * I)‖ ≤ 0.00000012512 := by
  have hl := lg_2
  refine (ecis_approx ((((665:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.4609428748995 0.460942875232 (-0.4609429) 0.00000002511 0.8956335005951 (-0.4447927973919) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p665_3 : ‖exp (-((((((665:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7447893610818:ℝ):ℂ) + (((-0.6672996385578):ℝ):ℂ) * I)‖ ≤ 0.00000012822 := by
  have hl := lg_3
  refine (ecis_approx ((((665:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.73057717179142906 0.730577172123929725 (-0.7305772) 0.00000002821 0.7447893610818 (-0.6672996385578) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p665_4 : ‖exp (-((((((665:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6043187347765:ℝ):ℂ) + (((-0.7967426603352):ℝ):ℂ) * I)‖ ≤ 0.00000015022 := by
  have hl := lg_4
  refine (ecis_approx ((((665:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.921885749799 0.921885750464 (-0.9218858) 0.00000005021 0.6043187347765 (-0.7967426603352) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p665_5 : ‖exp (-((((((665:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4798819279388:ℝ):ℂ) + (((-0.8773330811258):ℝ):ℂ) * I)‖ ≤ 0.0000001121 := by
  have hl := lg_5
  refine (ecis_approx ((((665:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 1.070276211422948985 1.07027621208794965 (-1.0702762) 0.00000001209 0.4798819279388 (-0.8773330811258) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p98_2 : ‖exp (-((((((980:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7780226095568:ℝ):ℂ) + (((-0.6282362764267):ℝ):ℂ) * I)‖ ≤ 0.0000001372 := by
  have hl := lg_2
  refine (ecis_approx ((((980:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.679284236694 0.679284237184 (-0.6792842) 0.00000003719 0.7780226095568 (-0.6282362764267) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p98_3 : ‖exp (-((((((980:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4742890762771:ℝ):ℂ) + (((-0.8803691680904):ℝ):ℂ) * I)‖ ≤ 0.00000014315 := by
  have hl := lg_3
  refine (ecis_approx ((((980:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.07664004264000072 1.0766400431300017 (-1.07664) 0.00000004314 0.4742890762771 (-0.8803691680904) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p98_4 : ‖exp (-((((((980:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2106382642066:ℝ):ℂ) + (((-0.9775640754713):ℝ):ℂ) * I)‖ ≤ 0.00000012663 := by
  have hl := lg_4
  refine (ecis_approx ((((980:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 1.358568473388 1.358568474368 (-1.3585685) 0.00000002662 0.2106382642066 (-0.9775640754713) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v0p98_5 : ‖exp (-((((((980:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0064528284228):ℝ):ℂ) + (((-0.9999791802858):ℝ):ℂ) * I)‖ ≤ 0.00000014634 := by
  have hl := lg_5
  refine (ecis_approx ((((980:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 1.57724915367592482 1.5772491546559258 (-1.5772492) 0.00000004633 (-0.0064528284228) (-0.9999791802858) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p401_2 : ‖exp (-((((((1401:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5643924754579:ℝ):ℂ) + (((-0.8255065921278):ℝ):ℂ) * I)‖ ≤ 0.00000010041 := by
  have hl := lg_2
  refine (ecis_approx ((((1401:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.9710991996003 0.9710992003008 (-0.9710992) 0.0000000004 0.5643924754579 (-0.8255065921278) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p401_3 : ‖exp (-((((((1401:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0316352477163:ℝ):ℂ) + (((-0.9994994802909):ℝ):ℂ) * I)‖ ≤ 0.00000011678 := by
  have hl := lg_3
  refine (ecis_approx ((((1401:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.539155816059837764 1.539155816760339165 (-1.5391558) 0.00000001677 0.0316352477163 (-0.9994994802909) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p401_4 : ‖exp (-((((((1401:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.362922267293):ℝ):ℂ) + (((-0.9318194180743):ℝ):ℂ) * I)‖ ≤ 0.00000010081 := by
  have hl := lg_4
  refine (ecis_approx ((((1401:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 1.9421983992006 1.9421984006016 (-1.9421984) 0.0000000008 (-0.362922267293) (-0.9318194180743) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p401_5 : ‖exp (-((((((1401:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6319185616215):ℝ):ℂ) + (((-0.7750347937114):ℝ):ℂ) * I)‖ ≤ 0.00000011601 := by
  have hl := lg_5
  refine (ecis_approx ((((1401:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 2.254822514591806809 2.25482251599280821 (-2.2548225) 0.000000016 (-0.6319185616215) (-0.7750347937114) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p822_2 : ‖exp (-((((((1822:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3030410320485:ℝ):ℂ) + (((-0.9529775091234):ℝ):ℂ) * I)‖ ≤ 0.00000013751 := by
  have hl := lg_2
  refine (ecis_approx ((((1822:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.2629141625066 1.2629141634176 (-1.2629142) 0.0000000375 0.3030410320485 (-0.9529775091234) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p822_3 : ‖exp (-((((((1822:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4176662360097):ℝ):ℂ) + (((-0.9086005256953):ℝ):ℂ) * I)‖ ≤ 0.00000011054 := by
  have hl := lg_3
  refine (ecis_approx ((((1822:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 2.001671589479674808 2.00167159039067663 (-2.0016716) 0.00000001053 (-0.4176662360097) (-0.9086005256953) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p822_4 : ‖exp (-((((((1822:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8163322080195):ℝ):ℂ) + (((-0.5775826573695):ℝ):ℂ) * I)‖ ≤ 0.00000012685 := by
  have hl := lg_4
  refine (ecis_approx ((((1822:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 2.5258283250132 2.5258283268352 (-2.5258283) 0.00000002684 (-0.8163322080195) (-0.5775826573695) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v1p822_5 : ‖exp (-((((((1822:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9781980437302):ℝ):ℂ) + (((-0.207674232704):ℝ):ℂ) * I)‖ ≤ 0.00000012451 := by
  have hl := lg_5
  refine (ecis_approx ((((1822:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 2.932395875507688798 2.93239587732969062 (-2.9323959) 0.0000000245 (-0.9781980437302) (-0.207674232704) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p384_2 : ‖exp (-((((((2384:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0815758252346):ℝ):ℂ) + (((-0.9966671383852):ℝ):ℂ) * I)‖ ≤ 0.00000012218 := by
  have hl := lg_2
  refine (ecis_approx ((((2384:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.6524628778352 1.6524628790272 (-1.6524629) 0.00000002217 (-0.0815758252346) (-0.9966671383852) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p384_3 : ‖exp (-((((((2384:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8665737927836):ℝ):ℂ) + (((-0.4990489570927):ℝ):ℂ) * I)‖ ≤ 0.00000010445 := by
  have hl := lg_3
  refine (ecis_approx ((((2384:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 2.619091695565062976 2.61909169675706536 (-2.6190917) 0.00000000444 (-0.8665737927836) (-0.4990489570927) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p384_4 : ‖exp (-((((((2384:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9866907844083):ℝ):ℂ) + ((0.1626077968288:ℝ):ℂ) * I)‖ ≤ 0.00000015089 := by
  have hl := lg_4
  refine (ecis_approx ((((2384:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.3049257556704 3.3049257580544 2.9782596 0.00000005088 (-0.9866907844083) 0.1626077968288 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p384_5 : ‖exp (-((((((2384:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7678568407469):ℝ):ℂ) + ((0.6406214733207:ℝ):ℂ) * I)‖ ≤ 0.00000012519 := by
  have hl := lg_5
  refine (ecis_approx ((((2384:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.836899982003474256 3.83689998438747664 2.4462853 0.00000002518 (-0.7678568407469) 0.6406214733207 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p946_2 : ‖exp (-((((((2946:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4539694497322):ℝ):ℂ) + (((-0.891017249387):ℝ):ℂ) * I)‖ ≤ 0.00000010685 := by
  have hl := lg_2
  refine (ecis_approx ((((2946:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.0420115931638 2.0420115946368 (-2.0420116) 0.00000000684 (-0.4539694497322) (-0.891017249387) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p946_3 : ‖exp (-((((((2946:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9954985581415):ℝ):ℂ) + ((0.094776686232:ℝ):ℂ) * I)‖ ≤ 0.00000010554 := by
  have hl := lg_3
  refine (ecis_approx ((((2946:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.236511801650451144 3.23651180312345409 3.0466735 0.00000000553 (-0.9954985581415) 0.094776686232 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p946_4 : ‖exp (-((((((2946:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5878234716107):ℝ):ℂ) + ((0.8089892250286:ℝ):ℂ) * I)‖ ≤ 0.00000012087 := by
  have hl := lg_4
  refine (ecis_approx ((((2946:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.0840231863276 4.0840231892736 2.1991621 0.00000002086 (-0.5878234716107) 0.8089892250286 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v2p946_5 : ‖exp (-((((((2946:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0290110557688:ℝ):ℂ) + ((0.9995790907392:ℝ):ℂ) * I)‖ ≤ 0.0000001187 := by
  have hl := lg_5
  refine (ecis_approx ((((2946:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.741404088499259714 4.74140409144526266 1.5417812 0.00000001869 0.0290110557688 0.9995790907392 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v3p508_2 : ‖exp (-((((((3508:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7583407864249):ℝ):ℂ) + (((-0.6518583063891):ℝ):ℂ) * I)‖ ≤ 0.00000011026 := by
  have hl := lg_2
  refine (ecis_approx ((((3508:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.4315603084924 2.4315603102464 (-2.4315603) 0.00000001025 (-0.7583407864249) (-0.6518583063891) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v3p508_3 : ‖exp (-((((((3508:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7568349979683):ℝ):ℂ) + ((0.6536059866729:ℝ):ℂ) * I)‖ ≤ 0.00000010233 := by
  have hl := lg_3
  refine (ecis_approx ((((3508:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.853931907735839312 3.85393190948984282 2.4292534 0.00000000232 (-0.7568349979683) 0.6536059866729 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v3p508_4 : ‖exp (-((((((3508:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1501615038282:ℝ):ℂ) + ((0.9886614803703:ℝ):ℂ) * I)‖ ≤ 0.00000011333 := by
  have hl := lg_4
  refine (ecis_approx ((((3508:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.8631206169848 4.8631206204928 1.4200647 0.00000001332 0.1501615038282 0.9886614803703 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v3p508_5 : ‖exp (-((((((3508:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8037188859011:ℝ):ℂ) + ((0.5950092036648:ℝ):ℂ) * I)‖ ≤ 0.0000001122 := by
  have hl := lg_5
  refine (ecis_approx ((((3508:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.645908194995045172 5.64590819850304868 0.6372771 0.00000001219 0.8037188859011 0.5950092036648 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p07_2 : ‖exp (-((((((4070:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9490831657479):ℝ):ℂ) + (((-0.3150256248196):ℝ):ℂ) * I)‖ ≤ 0.00000012587 := by
  have hl := lg_2
  refine (ecis_approx ((((4070:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.821109023821 2.821109025856 (-2.821109) 0.00000002586 (-0.9490831657479) (-0.3150256248196) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p07_3 : ‖exp (-((((((4070:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2387097498973):ℝ):ℂ) + ((0.9710909613949:ℝ):ℂ) * I)‖ ≤ 0.00000010869 := by
  have hl := lg_3
  refine (ecis_approx ((((4070:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.47135201382122748 4.47135201585623155 1.8118333 0.00000000868 (-0.2387097498973) 0.9710909613949 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p07_4 : ‖exp (-((((((4070:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8015177155758:ℝ):ℂ) + ((0.5979710290793:ℝ):ℂ) * I)‖ ≤ 0.00000014455 := by
  have hl := lg_4
  refine (ecis_approx ((((4070:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.642218047642 5.642218051712 0.6409673 0.00000004454 0.8015177155758 0.5979710290793 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p07_5 : ‖exp (-((((((4070:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9645068362222:ℝ):ℂ) + (((-0.2640578778994):ℝ):ℂ) * I)‖ ≤ 0.0000001057 := by
  have hl := lg_5
  refine (ecis_approx ((((4070:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.55041230149083063 6.5504123055608347 (-0.267227) 0.00000000569 0.9645068362222 (-0.2640578778994) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p632_2 : ‖exp (-((((((4632:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9976159568152):ℝ):ℂ) + ((0.0690101599304:ℝ):ℂ) * I)‖ ≤ 0.0000001343 := by
  have hl := lg_2
  refine (ecis_approx ((((4632:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.2106577391496 3.2106577414656 3.0725276 0.00000003429 (-0.9976159568152) 0.0690101599304 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p632_3 : ‖exp (-((((((4632:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3675591883535:ℝ):ℂ) + ((0.9300001306757:ℝ):ℂ) * I)‖ ≤ 0.00000011506 := by
  have hl := lg_3
  refine (ecis_approx ((((4632:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.088772119906615648 5.08877212222262028 1.1944132 0.00000001505 0.3675591883535 0.9300001306757 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p632_4 : ‖exp (-((((((4632:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.990475182804:ℝ):ℂ) + (((-0.1376913659215):ℝ):ℂ) * I)‖ ≤ 0.0000001289 := by
  have hl := lg_4
  refine (ecis_approx ((((4632:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.4213154782992 6.4213154829312 (-0.1381302) 0.00000002889 0.990475182804 (-0.1376913659215) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v4p632_5 : ‖exp (-((((((4632:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3885571891595:ℝ):ℂ) + (((-0.9214246093699):ℝ):ℂ) * I)‖ ≤ 0.00000010545 := by
  have hl := lg_5
  refine (ecis_approx ((((4632:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.454916407986616088 7.45491641261862072 (-1.1717311) 0.00000000544 0.3885571891595 (-0.9214246093699) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p194_2 : ‖exp (-((((((5194:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8966670578027):ℝ):ℂ) + ((0.4427055311815:ℝ):ℂ) * I)‖ ≤ 0.00000014991 := by
  have hl := lg_2
  refine (ecis_approx ((((5194:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.6002064544782 3.6002064570752 2.6829789 0.0000000499 (-0.8966670578027) 0.4427055311815 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p194_3 : ‖exp (-((((((5194:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8381067191938:ℝ):ℂ) + ((0.545506303577:ℝ):ℂ) * I)‖ ≤ 0.00000012142 := by
  have hl := lg_3
  refine (ecis_approx ((((5194:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.706192225992003816 5.70619222858900901 0.5769931 0.00000002141 0.8381067191938 0.545506303577 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p194_4 : ‖exp (-((((((5194:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6080235515228:ℝ):ℂ) + (((-0.7939189888104):ℝ):ℂ) * I)‖ ≤ 0.00000010699 := by
  have hl := lg_4
  refine (ecis_approx ((((5194:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.2004129089564 7.2004129141504 (-0.9172276) 0.00000000698 0.6080235515228 (-0.7939189888104) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p194_5 : ‖exp (-((((((5194:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4841914843452):ℝ):ℂ) + (((-0.8749620600243):ℝ):ℂ) * I)‖ ≤ 0.00000011251 := by
  have hl := lg_5
  refine (ecis_approx ((((5194:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.359420514482401546 8.35942051967640674 (-2.0762352) 0.0000000125 (-0.4841914843452) (-0.8749620600243) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p756_2 : ‖exp (-((((((5756:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6613624684694):ℝ):ℂ) + ((0.7500664539105:ℝ):ℂ) * I)‖ ≤ 0.00000013739 := by
  have hl := lg_2
  refine (ecis_approx ((((5756:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.9897551698068 3.9897551726848 2.2934301 0.00000003738 (-0.6613624684694) 0.7500664539105 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p756_3 : ‖exp (-((((((5756:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9991829401242:ℝ):ℂ) + (((-0.0404159889736):ℝ):ℂ) * I)‖ ≤ 0.00000012779 := by
  have hl := lg_3
  refine (ecis_approx ((((5756:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.323612332077391984 6.32361233495539774 (-0.040427) 0.00000002778 0.9991829401242 (-0.0404159889736) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p756_4 : ‖exp (-((((((5756:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1251992642587):ℝ):ℂ) + (((-0.9921316163839):ℝ):ℂ) * I)‖ ≤ 0.00000013821 := by
  have hl := lg_4
  refine (ecis_approx ((((5756:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.9795103396136 7.9795103453696 (-1.696325) 0.0000000382 (-0.1251992642587) (-0.9921316163839) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v5p756_5 : ‖exp (-((((((5756:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9870909690115):ℝ):ℂ) + (((-0.160160602266):ℝ):ℂ) * I)‖ ≤ 0.00000011957 := by
  have hl := lg_5
  refine (ecis_approx ((((5756:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.263924620978187004 9.26392462673419276 (-2.9807393) 0.00000001956 (-0.9870909690115) (-0.160160602266) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p318_2 : ‖exp (-((((((6318:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.326960091583):ℝ):ℂ) + ((0.9450381465899:ℝ):ℂ) * I)‖ ≤ 0.00000012206 := by
  have hl := lg_2
  refine (ecis_approx ((((6318:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.3793038851354 4.3793038882944 1.9038814 0.00000002205 (-0.326960091583) 0.9450381465899 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p318_3 : ‖exp (-((((((6318:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7913103789505:ℝ):ℂ) + (((-0.6114146581209):ℝ):ℂ) * I)‖ ≤ 0.00000013416 := by
  have hl := lg_3
  refine (ecis_approx ((((6318:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.941032438162780152 6.94103244132178647 (-0.6578471) 0.00000003415 0.7913103789505 (-0.6114146581209) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p318_4 : ‖exp (-((((((6318:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7861941925788):ℝ):ℂ) + (((-0.6179795235371):ℝ):ℂ) * I)‖ ≤ 0.00000013692 := by
  have hl := lg_4
  refine (ecis_approx ((((6318:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.7586077702708 8.7586077765888 (-2.4754225) 0.00000003691 (-0.7861941925788) (-0.6179795235371) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p318_5 : ‖exp (-((((((6318:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7360019840293):ℝ):ℂ) + ((0.6769793789137:ℝ):ℂ) * I)‖ ≤ 0.00000011945 := by
  have hl := lg_5
  refine (ecis_approx ((((6318:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.168428727473972462 10.16842873379197878 2.3979419 0.00000001944 (-0.7360019840293) 0.6769793789137 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p88_2 : ‖exp (-((((((6880:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0564336292417:ℝ):ℂ) + ((0.9984063528897:ℝ):ℂ) * I)‖ ≤ 0.00000010673 := by
  have hl := lg_2
  refine (ecis_approx ((((6880:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.768852600464 4.768852603904 1.5143327 0.00000000672 0.0564336292417 0.9984063528897 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p88_3 : ‖exp (-((((((6880:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.291246079051:ℝ):ℂ) + (((-0.9566481701427):ℝ):ℂ) * I)‖ ≤ 0.00000014052 := by
  have hl := lg_3
  refine (ecis_approx ((((6880:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.55845254424816832 7.5584525476881752 (-1.2752672) 0.00000004051 0.291246079051 (-0.9566481701427) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p88_4 : ‖exp (-((((((6880:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9936304907775):ℝ):ℂ) + ((0.1126873876884:ℝ):ℂ) * I)‖ ≤ 0.00000011345 := by
  have hl := lg_4
  refine (ecis_approx ((((6880:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.537705200928 9.537705207808 3.0286654 0.00000001344 (-0.9936304907775) 0.1126873876884 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v6p88_5 : ‖exp (-((((((6880:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0772813932356:ℝ):ℂ) + ((0.9970093210494:ℝ):ℂ) * I)‖ ≤ 0.00000012651 := by
  have hl := lg_5
  refine (ecis_approx ((((6880:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.07293283396975792 11.0729328408497648 1.4934378 0.0000000265 0.0772813932356 0.9970093210494 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p442_2 : ‖exp (-((((((7442:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.431371396539:ℝ):ℂ) + ((0.9021744389241:ℝ):ℂ) * I)‖ ≤ 0.00000011235 := by
  have hl := lg_2
  refine (ecis_approx ((((7442:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.1584013157926 5.1584013195136 1.124784 0.00000001234 0.431371396539 0.9021744389241 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p442_3 : ‖exp (-((((((7442:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3163609758772):ℝ):ℂ) + (((-0.9486388843707):ℝ):ℂ) * I)‖ ≤ 0.00000014689 := by
  have hl := lg_3
  refine (ecis_approx ((((7442:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.175872650333556488 8.17587265405456393 (-1.8926873) 0.00000004688 (-0.3163609758772) (-0.9486388843707) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p442_4 : ‖exp (-((((((7442:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6278374364947):ℝ):ℂ) + ((0.7783444952727:ℝ):ℂ) * I)‖ ≤ 0.00000012468 := by
  have hl := lg_4
  refine (ecis_approx ((((7442:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.3168026315852 10.3168026390272 2.249568 0.00000002467 (-0.6278374364947) 0.7783444952727 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v7p442_5 : ‖exp (-((((((7442:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8315334543585:ℝ):ℂ) + ((0.5554746747445:ℝ):ℂ) * I)‖ ≤ 0.00000013356 := by
  have hl := lg_5
  refine (ecis_approx ((((7442:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.977436940465543378 11.97743694790755082 0.5889337 0.00000003355 0.8315334543585 0.5554746747445 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p004_2 : ‖exp (-((((((8004:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7416729437099:ℝ):ℂ) + ((0.6707616898487:ℝ):ℂ) * I)‖ ≤ 0.00000012796 := by
  have hl := lg_2
  refine (ecis_approx ((((8004:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.5479500311212 5.5479500351232 0.7352353 0.00000002795 0.7416729437099 0.6707616898487 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p004_3 : ‖exp (-((((((8004:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8071516470453):ℝ):ℂ) + (((-0.590344152694):ℝ):ℂ) * I)‖ ≤ 0.00000015078 := by
  have hl := lg_3
  refine (ecis_approx ((((8004:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.793292756418944656 8.79329276042095266 (-2.5101075) 0.00000005077 (-0.8071516470453) (-0.590344152694) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p004_4 : ‖exp (-((((((8004:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1001576103598:ℝ):ℂ) + ((0.99497158406:ℝ):ℂ) * I)‖ ≤ 0.00000015213 := by
  have hl := lg_4
  refine (ecis_approx ((((8004:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.0959000622424 11.0959000702464 1.4704705 0.00000005212 0.1001576103598 0.99497158406 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p004_5 : ‖exp (-((((((8004:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9506195049347:ℝ):ℂ) + (((-0.3103587550524):ℝ):ℂ) * I)‖ ≤ 0.00000014062 := by
  have hl := lg_5
  refine (ecis_approx ((((8004:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.881941046961328836 12.88194105496533684 (-0.3155704) 0.00000004061 0.9506195049347 (-0.3103587550524) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p566_2 : ‖exp (-((((((8566:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9408430249655:ℝ):ℂ) + ((0.3388427398865:ℝ):ℂ) * I)‖ ≤ 0.00000014357 := by
  have hl := lg_2
  refine (ecis_approx ((((8566:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.9374987464498 5.9374987507328 0.3456866 0.00000004356 0.9408430249655 0.3388427398865 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p566_3 : ‖exp (-((((((8566:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999010884417):ℝ):ℂ) + (((-0.014064589564):ℝ):ℂ) * I)‖ ≤ 0.00000014469 := by
  have hl := lg_3
  refine (ecis_approx ((((8566:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.410712862504332824 9.41071286678734139 (-3.1275276) 0.00000004468 (-0.9999010884417) (-0.014064589564) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p566_4 : ‖exp (-((((((8566:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.770371259012:ℝ):ℂ) + ((0.6375955797277:ℝ):ℂ) * I)‖ ≤ 0.00000012147 := by
  have hl := lg_4
  refine (ecis_approx ((((8566:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.8749974928996 11.8749975014656 0.6913731 0.00000002146 0.770371259012 0.6375955797277 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v8p566_5 : ‖exp (-((((((8566:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3435757824604:ℝ):ℂ) + (((-0.939124955321):ℝ):ℂ) * I)‖ ≤ 0.00000014768 := by
  have hl := lg_5
  refine (ecis_approx ((((8566:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.786445153457114294 13.78644516202312286 (-1.2200745) 0.00000004767 0.3435757824604 (-0.939124955321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p128_2 : ‖exp (-((((((9128:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9990382079191:ℝ):ℂ) + (((-0.0438481369926):ℝ):ℂ) * I)‖ ≤ 0.00000014542 := by
  have hl := lg_2
  refine (ecis_approx ((((9128:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.3270474617784 6.3270474663424 (-0.0438622) 0.00000004541 0.9990382079191 (-0.0438481369926) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p128_3 : ‖exp (-((((((9128:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.82343656755):ℝ):ℂ) + ((0.5674083354713:ℝ):ℂ) * I)‖ ≤ 0.00000014578 := by
  have hl := lg_3
  refine (ecis_approx ((((9128:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.028132968589720992 10.02813297315373012 2.5382376 0.00000004577 (-0.82343656755) 0.5674083354713 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p128_4 : ‖exp (-((((((9128:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9961546905257:ℝ):ℂ) + (((-0.0876118287879):ℝ):ℂ) * I)‖ ≤ 0.00000011834 := by
  have hl := lg_4
  refine (ecis_approx ((((9128:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.6540949235568 12.6540949326848 (-0.0877243) 0.00000001833 0.9961546905257 (-0.0876118287879) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p128_5 : ‖exp (-((((((9128:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5259080482827):ℝ):ℂ) + (((-0.8505414303513):ℝ):ℂ) * I)‖ ≤ 0.00000015442 := by
  have hl := lg_5
  refine (ecis_approx ((((9128:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.690949259952899752 14.69094926908090888 (-2.1245787) 0.00000005441 (-0.5259080482827) (-0.8505414303513) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p69_2 : ‖exp (-((((((9690:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9075385602548:ℝ):ℂ) + (((-0.4199687627081):ℝ):ℂ) * I)‖ ≤ 0.00000013009 := by
  have hl := lg_2
  refine (ecis_approx ((((9690:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.716596177107 6.716596181952 (-0.4334109) 0.00000003008 0.9075385602548 (-0.4199687627081) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p69_3 : ‖exp (-((((((9690:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3429176969098):ℝ):ℂ) + ((0.93936545239:ℝ):ℂ) * I)‖ ≤ 0.0000001397 := by
  have hl := lg_3
  refine (ecis_approx ((((9690:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.64555307467510916 10.64555307952011885 1.9208175 0.00000003969 (-0.3429176969098) 0.93936545239 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p69_4 : ‖exp (-((((((9690:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6472525529264:ℝ):ℂ) + (((-0.762275627795):ℝ):ℂ) * I)‖ ≤ 0.00000014956 := by
  have hl := lg_4
  refine (ecis_approx ((((9690:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.433192354214 13.433192363904 (-0.8668217) 0.00000004955 0.6472525529264 (-0.762275627795) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v9p69_5 : ‖exp (-((((((9690:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9936774399349):ℝ):ℂ) + (((-0.1122726365168):ℝ):ℂ) * I)‖ ≤ 0.00000014793 := by
  have hl := lg_5
  refine (ecis_approx ((((9690:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.59545336644868521 15.5954533761386949 (-3.0290828) 0.00000004792 (-0.9936774399349) (-0.1122726365168) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p252_2 : ‖exp (-((((((10252:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6800543233842:ℝ):ℂ) + (((-0.7331617265287):ℝ):ℂ) * I)‖ ≤ 0.00000011476 := by
  have hl := lg_2
  refine (ecis_approx ((((10252:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.1061448924356 7.1061448975616 (-0.8229596) 0.00000001475 0.6800543233842 (-0.7331617265287) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p252_3 : ‖exp (-((((((10252:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.264223698565:ℝ):ℂ) + ((0.9644614233429:ℝ):ℂ) * I)‖ ≤ 0.00000013361 := by
  have hl := lg_3
  refine (ecis_approx ((((10252:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.262973180760497328 11.26297318588650758 1.3033974 0.0000000336 0.264223698565 0.9644614233429 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p252_4 : ‖exp (-((((((10252:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.075052234493):ℝ):ℂ) + (((-0.9971796037311):ℝ):ℂ) * I)‖ ≤ 0.0000001295 := by
  have hl := lg_4
  refine (ecis_approx ((((10252:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.2122897848712 14.2122897951232 (-1.6459192) 0.00000002949 (-0.075052234493) (-0.9971796037311) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p252_5 : ‖exp (-((((((10252:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7024272924118):ℝ):ℂ) + ((0.7117555049671:ℝ):ℂ) * I)‖ ≤ 0.00000014861 := by
  have hl := lg_5
  refine (ecis_approx ((((10252:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.499957472944470668 16.49995748319648092 2.3495984 0.0000000486 (-0.7024272924118) 0.7117555049671 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p814_2 : ‖exp (-((((((10814:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3506714875411:ℝ):ℂ) + (((-0.9364985359442):ℝ):ℂ) * I)‖ ≤ 0.00000010601 := by
  have hl := lg_2
  refine (ecis_approx ((((10814:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.4956936077642 7.4956936131712 (-1.2125083) 0.000000006 0.3506714875411 (-0.9364985359442) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p814_3 : ‖exp (-((((((10814:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7738003660265:ℝ):ℂ) + ((0.6334295489928:ℝ):ℂ) * I)‖ ≤ 0.00000012753 := by
  have hl := lg_3
  refine (ecis_approx ((((10814:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.880393286845885496 11.88039329225289631 0.6859773 0.00000002752 0.7738003660265 0.6334295489928 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p814_4 : ‖exp (-((((((10814:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7540590156454):ℝ):ℂ) + (((-0.6568066693396):ℝ):ℂ) * I)‖ ≤ 0.000000112 := by
  have hl := lg_4
  refine (ecis_approx ((((10814:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.9913872155284 14.9913872263424 (-2.4250166) 0.00000001199 (-0.7540590156454) (-0.6568066693396) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v10p814_5 : ‖exp (-((((((10814:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1253712519538:ℝ):ℂ) + ((0.9921098977349:ℝ):ℂ) * I)‖ ≤ 0.00000014211 := by
  have hl := lg_5
  refine (ecis_approx ((((10814:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.404461579440256126 17.40446159025426694 1.4450943 0.0000000421 0.1253712519538 0.9921098977349 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p376_2 : ‖exp (-((((((11376:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0312555819776):ℝ):ℂ) + (((-0.9995114249447):ℝ):ℂ) * I)‖ ≤ 0.00000012162 := by
  have hl := lg_2
  refine (ecis_approx ((((11376:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.8852423230928 7.8852423287808 (-1.602057) 0.00000002161 (-0.0312555819776) (-0.9995114249447) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p376_3 : ‖exp (-((((((11376:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9976508754717:ℝ):ℂ) + ((0.0685035084547:ℝ):ℂ) * I)‖ ≤ 0.00000012144 := by
  have hl := lg_3
  refine (ecis_approx ((((11376:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.497813392931273664 12.49781339861928504 0.0685572 0.00000002143 0.9976508754717 0.0685035084547 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p376_4 : ‖exp (-((((((11376:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9980461764836):ℝ):ℂ) + ((0.0624806294732:ℝ):ℂ) * I)‖ ≤ 0.00000013604 := by
  have hl := lg_4
  refine (ecis_approx ((((11376:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.7704846461856 15.7704846575616 3.0790713 0.00000003603 (-0.9980461764836) 0.0624806294732 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p376_5 : ‖exp (-((((((11376:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8574050889337:ℝ):ℂ) + ((0.5146421217414:ℝ):ℂ) * I)‖ ≤ 0.00000013562 := by
  have hl := lg_5
  refine (ecis_approx ((((11376:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.308965685936041584 18.30896569731205296 0.5405902 0.00000003561 0.8574050889337 0.5146421217414 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p938_2 : ‖exp (-((((((11938:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4084993491423):ℝ):ℂ) + (((-0.9127586108862):ℝ):ℂ) * I)‖ ≤ 0.00000013723 := by
  have hl := lg_2
  refine (ecis_approx ((((11938:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.2747910384214 8.2747910443904 (-1.9916057) 0.00000003722 (-0.4084993491423) (-0.9127586108862) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p938_3 : ‖exp (-((((((11938:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8531183184239:ℝ):ℂ) + (((-0.5217174855892):ℝ):ℂ) * I)‖ ≤ 0.00000011536 := by
  have hl := lg_3
  refine (ecis_approx ((((11938:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.115233499016661832 13.11523350498567377 (-0.5488629) 0.00000001535 0.8531183184239 (-0.5217174855892) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p938_4 : ‖exp (-((((((11938:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6662564835724):ℝ):ℂ) + ((0.7457226683419:ℝ):ℂ) * I)‖ ≤ 0.00000014471 := by
  have hl := lg_4
  refine (ecis_approx ((((11938:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.5495820768428 16.5495820887808 2.2999738 0.0000000447 (-0.6662564835724) 0.7457226683419 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v11p938_5 : ‖exp (-((((((11938:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9345108927649:ℝ):ℂ) + (((-0.3559345323283):ℝ):ℂ) * I)‖ ≤ 0.00000012912 := by
  have hl := lg_5
  refine (ecis_approx ((((11938:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.213469792431827042 19.21346980436983898 (-0.3639139) 0.00000002911 0.9345108927649 (-0.3559345323283) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p359_2 : ‖exp (-((((((12359:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6538217486249):ℝ):ℂ) + (((-0.7566486113169):ℝ):ℂ) * I)‖ ≤ 0.00000010587 := by
  have hl := lg_2
  refine (ecis_approx ((((12359:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.5666060013277 8.5666060075072 (-2.2834207) 0.00000000586 (-0.6538217486249) (-0.7566486113169) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p359_3 : ‖exp (-((((((12359:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5306926891961:ℝ):ℂ) + (((-0.8475643159276):ℝ):ℂ) * I)‖ ≤ 0.00000014194 := by
  have hl := lg_3
  refine (ecis_approx ((((12359:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.577749272436498876 13.577749278616011235 (-1.0113787) 0.00000004193 0.5306926891961 (-0.8475643159276) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p359_4 : ‖exp (-((((((12359:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1450342349418):ℝ):ℂ) + ((0.9894266373482:ℝ):ℂ) * I)‖ ≤ 0.0000001189 := by
  have hl := lg_4
  refine (ecis_approx ((((12359:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.1332120026554 17.1332120150144 1.7163439 0.00000001889 (-0.1450342349418) 0.9894266373482 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p359_5 : ‖exp (-((((((12359:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5049371303191:ℝ):ℂ) + (((-0.8631561240153):ℝ):ℂ) * I)‖ ≤ 0.00000014418 := by
  have hl := lg_5
  refine (ecis_approx ((((12359:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.891043153347709031 19.89104316570672139 (-1.0414872) 0.00000004417 0.5049371303191 (-0.8631561240153) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p359_6 : ‖exp (-((((((12359:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9882867834269):ℝ):ℂ) + ((0.1526081036992:ℝ):ℂ) * I)‖ ≤ 0.00000015497 := by
  have hl := lg_6
  refine (ecis_approx ((((12359:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.144355273764198876 22.144355286123211235 2.9883859 0.00000005496 (-0.9882867834269) 0.1526081036992 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p359_7 : ‖exp (-((((((12359:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4684703839762:ℝ):ℂ) + ((0.8834792014174:ℝ):ℂ) * I)‖ ≤ 0.0000001094 := by
  have hl := lg_7
  refine (ecis_approx ((((12359:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.049503525749280498 24.049503538108305216 1.0832377 0.00000000939 0.4684703839762 0.8834792014174 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p359_8 : ‖exp (-((((((12359:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8434748282598:ℝ):ℂ) + (((-0.5371687017056):ℝ):ℂ) * I)‖ ≤ 0.00000012475 := by
  have hl := lg_8
  refine (ecis_approx ((((12359:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.6998180039831 25.6998180225216 (-0.5670768) 0.00000002474 0.8434748282598 (-0.5371687017056) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p359_9 : ‖exp (-((((((12359:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4367304493085):ℝ):ℂ) + (((-0.8995924158432):ℝ):ℂ) * I)‖ ≤ 0.00000012853 := by
  have hl := lg_9
  refine (ecis_approx ((((12359:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.155498544872997752 27.15549855723202247 (-2.0227573) 0.00000002852 (-0.4367304493085) (-0.8995924158432) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p359_10 : ‖exp (-((((((12359:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9832447586327):ℝ):ℂ) + ((0.1822902747675:ℝ):ℂ) * I)‖ ≤ 0.00000013733 := by
  have hl := lg_10
  refine (ecis_approx ((((12359:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.457649154675409031 28.45764917321392139 2.9582774 0.00000003732 (-0.9832447586327) 0.1822902747675 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p78_2 : ‖exp (-((((((12780:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8438612886358):ℝ):ℂ) + (((-0.5365613902173):ℝ):ℂ) * I)‖ ≤ 0.00000014296 := by
  have hl := lg_2
  refine (ecis_approx ((((12780:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.858420964234 8.858420970624 (-2.5752357) 0.00000004295 (-0.8438612886358) (-0.5365613902173) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p78_3 : ‖exp (-((((((12780:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0967503467315:ℝ):ℂ) + (((-0.9953086809665):ℝ):ℂ) * I)‖ ≤ 0.0000001379 := by
  have hl := lg_3
  refine (ecis_approx ((((12780:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.04026504585633592 14.0402650522463487 (-1.4738944) 0.00000003789 0.0967503467315 (-0.9953086809665) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p78_4 : ‖exp (-((((((12780:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4242036649179:ℝ):ℂ) + ((0.9055668118202:ℝ):ℂ) * I)‖ ≤ 0.00000011972 := by
  have hl := lg_4
  refine (ecis_approx ((((12780:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.716841928468 17.716841941248 1.132714 0.00000001971 0.4242036649179 0.9055668118202 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p78_5 : ‖exp (-((((((12780:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1477216717718):ℝ):ℂ) + (((-0.9890289721178):ℝ):ℂ) * I)‖ ≤ 0.00000010729 := by
  have hl := lg_5
  refine (ecis_approx ((((12780:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.56861651426359102 20.5686165270436038 (-1.7190606) 0.00000000728 (-0.1477216717718) (-0.9890289721178) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p78_6 : ‖exp (-((((((12780:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6156880762052):ℝ):ℂ) + ((0.7879899699903:ℝ):ℂ) * I)‖ ≤ 0.00000011864 := by
  have hl := lg_6
  refine (ecis_approx ((((12780:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.89868601009033592 22.8986860228703487 2.2340552 0.00000001863 (-0.6156880762052) 0.7879899699903 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p78_7 : ‖exp (-((((((12780:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9653514485476:ℝ):ℂ) + ((0.2609532157054:ℝ):ℂ) * I)‖ ≤ 0.00000013045 := by
  have hl := lg_7
  refine (ecis_approx ((((12780:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.86873169828269316 24.86873171106271872 0.2640095 0.00000003044 0.9653514485476 0.2609532157054 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p78_8 : ‖exp (-((((((12780:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1279231361912:ℝ):ℂ) + (((-0.9917840849837):ℝ):ℂ) * I)‖ ≤ 0.00000013603 := by
  have hl := lg_8
  refine (ecis_approx ((((12780:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.575262892702 26.575262911872 (-1.4425217) 0.00000003602 0.1279231361912 (-0.9917840849837) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p78_9 : ‖exp (-((((((12780:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9812787599366):ℝ):ℂ) + (((-0.1925928216848):ℝ):ℂ) * I)‖ ≤ 0.00000013702 := by
  have hl := lg_9
  refine (ecis_approx ((((12780:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.08053009171267184 28.0805301044926974 (-2.9477889) 0.00000003701 (-0.9812787599366) (-0.1925928216848) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v12p78_10 : ‖exp (-((((((12780:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4060181534189):ℝ):ℂ) + ((0.9138650114163:ℝ):ℂ) * I)‖ ≤ 0.00000015742 := by
  have hl := lg_10
  refine (ecis_approx ((((12780:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.42703747849759102 29.4270374976676038 1.988889 0.00000005741 (-0.4060181534189) 0.9138650114163 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p095_2 : ‖exp (-((((((13095:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.940051290922):ℝ):ℂ) + (((-0.3410330926119):ℝ):ℂ) * I)‖ ≤ 0.00000012541 := by
  have hl := lg_2
  refine (ecis_approx ((((13095:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.0767623260285 9.076762332576 (-2.793577) 0.0000000254 (-0.940051290922) (-0.3410330926119) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p095_3 : ‖exp (-((((((13095:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2465909287843):ℝ):ℂ) + (((-0.969119659196):ℝ):ℂ) * I)‖ ≤ 0.00000010891 := by
  have hl := lg_3
  refine (ecis_approx ((((13095:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.38632791670490758 14.386327923252420675 (-1.8199573) 0.0000000089 (-0.2465909287843) (-0.969119659196) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p095_4 : ‖exp (-((((((13095:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7673928639622:ℝ):ℂ) + ((0.641177192623:ℝ):ℂ) * I)‖ ≤ 0.00000014363 := by
  have hl := lg_4
  refine (ecis_approx ((((13095:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.153524652057 18.153524665152 0.6960313 0.00000004362 0.7673928639622 0.641177192623 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p095_5 : ‖exp (-((((((13095:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6093473159126):ℝ):ℂ) + (((-0.7929034295406):ℝ):ℂ) * I)‖ ≤ 0.00000014809 := by
  have hl := lg_5
  refine (ecis_approx ((((13095:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.075589456516566855 21.07558946961157995 (-2.2260335) 0.00000004808 (-0.6093473159126) (-0.7929034295406) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p095_6 : ‖exp (-((((((13095:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0986937464851):ℝ):ℂ) + ((0.99511785453:ℝ):ℂ) * I)‖ ≤ 0.00000012713 := by
  have hl := lg_6
  refine (ecis_approx ((((13095:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.46309024273340758 23.463090255828420675 1.669651 0.00000002712 (-0.0986937464851) 0.99511785453 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p095_7 : ‖exp (-((((((13095:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9397314854428:ℝ):ℂ) + (((-0.3419133446759):ℝ):ℂ) * I)‖ ≤ 0.00000013366 := by
  have hl := lg_7
  refine (ecis_approx ((((13095:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.48169339507135109 25.48169340816637728 (-0.3489522) 0.00000003365 0.9397314854428 (-0.3419133446759) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p095_8 : ‖exp (-((((((13095:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5027260979308):ℝ):ℂ) + (((-0.8644457591156):ℝ):ℂ) * I)‖ ≤ 0.00000015065 := by
  have hl := lg_8
  refine (ecis_approx ((((13095:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.2302869780855 27.230286997728 (-2.0975458) 0.00000005064 (-0.5027260979308) (-0.8644457591156) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p095_9 : ‖exp (-((((((13095:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8783858242254):ℝ):ℂ) + ((0.4779522399833:ℝ):ℂ) * I)‖ ≤ 0.00000011062 := by
  have hl := lg_9
  refine (ecis_approx ((((13095:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.77265583340981516 28.77265584650484135 2.6432707 0.00000001061 (-0.8783858242254) 0.4779522399833 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p095_10 : ‖exp (-((((((13095:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3024115243471:ℝ):ℂ) + ((0.9531774598374:ℝ):ℂ) * I)‖ ≤ 0.00000015337 := by
  have hl := lg_10
  refine (ecis_approx ((((13095:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.152351782545066855 30.15235180218757995 1.2635747 0.00000005336 0.3024115243471 0.9531774598374 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_2 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.991604068775):ℝ):ℂ) + (((-0.1293111378168):ℝ):ℂ) * I)‖ ≤ 0.00000011937 := by
  have hl := lg_2
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.295103687823 9.295103694528 (-3.0119184) 0.00000001936 (-0.991604068775) (-0.1293111378168) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_3 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5606941407093):ℝ):ℂ) + (((-0.8280229951909):ℝ):ℂ) * I)‖ ≤ 0.00000012682 := by
  have hl := lg_3
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.73239078755347924 14.73239079425849265 (-2.1660202) 0.00000002681 (-0.5606941407093) (-0.8280229951909) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_4 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.966557261009:ℝ):ℂ) + ((0.2564508943067:ℝ):ℂ) * I)‖ ≤ 0.00000014591 := by
  have hl := lg_4
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.590207375646 18.590207389056 0.2593485 0.0000000459 0.966557261009 0.2564508943067 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_5 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.917683478308):ℝ):ℂ) + (((-0.3973122619566):ℝ):ℂ) * I)‖ ≤ 0.00000012278 := by
  have hl := lg_5
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.58256239876954269 21.5825624121795561 (-2.7330065) 0.00000002277 (-0.917683478308) (-0.3973122619566) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_6 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4489140019713:ℝ):ℂ) + ((0.8935749654249:ℝ):ℂ) * I)‖ ≤ 0.00000015336 := by
  have hl := lg_6
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.02749447537647924 24.02749448878649265 1.1052467 0.00000005335 0.4489140019713 0.8935749654249 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_7 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5719510858817:ℝ):ℂ) + (((-0.8202877271779):ℝ):ℂ) * I)‖ ≤ 0.00000013687 := by
  have hl := lg_7
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.09465509186000902 26.09465510527003584 (-0.9619139) 0.00000003686 0.5719510858817 (-0.8202877271779) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_8 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9252801179358):ℝ):ℂ) + (((-0.3792844621142):ℝ):ℂ) * I)‖ ≤ 0.00000015488 := by
  have hl := lg_8
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.885311063469 27.885311083584 (-2.7525698) 0.00000005487 (-0.9252801179358) (-0.3792844621142) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_9 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3712442473345):ℝ):ℂ) + ((0.9285352490984:ℝ):ℂ) * I)‖ ≤ 0.00000015263 := by
  have hl := lg_9
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.46478157510695848 29.4647815885169853 1.951145 0.00000005262 (-0.3712442473345) 0.9285352490984 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_10 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8586017740816:ℝ):ℂ) + ((0.5126431444425:ℝ):ℂ) * I)‖ ≤ 0.00000014932 := by
  have hl := lg_10
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.87766608659254269 30.8776661067075561 0.5382604 0.00000004931 0.8586017740816 0.5126431444425 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_11 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7385703003673:ℝ):ℂ) + (((-0.674176469046):ℝ):ℂ) * I)‖ ≤ 0.00000013814 := by
  have hl := lg_11
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.15577559776852753 32.15577561788355435 (-0.7398491) 0.00000003813 0.7385703003673 (-0.674176469046) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_12 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3295956608716):ℝ):ℂ) + (((-0.9441221850653):ℝ):ℂ) * I)‖ ≤ 0.00000014743 := by
  have hl := lg_12
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.32259816319947924 33.32259818331449265 (-1.9066716) 0.00000004742 (-0.3295956608716) (-0.9441221850653) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_13 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9869794190075):ℝ):ℂ) + (((-0.160846591754):ℝ):ℂ) * I)‖ ≤ 0.00000015733 := by
  have hl := lg_13
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.395970873101597 34.39597089321662382 (-2.9800443) 0.00000005732 (-0.9869794190075) (-0.160846591754) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_14 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6732214321464):ℝ):ℂ) + ((0.7394409396828:ℝ):ℂ) * I)‖ ≤ 0.00000015674 := by
  have hl := lg_14
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.38975877968300902 35.38975879979803584 2.3093531 0.00000005673 (-0.6732214321464) 0.7394409396828 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p41_15 : ‖exp (-((((((13410:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1855560671578:ℝ):ℂ) + ((0.9826336784076:ℝ):ℂ) * I)‖ ≤ 0.00000015677 := by
  have hl := lg_15
  refine (ecis_approx ((((13410:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.31495318632302193 36.31495320643804875 1.3841586 0.00000005676 0.1855560671578 0.9826336784076 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_2 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9994251631741):ℝ):ℂ) + ((0.033901955793:ℝ):ℂ) * I)‖ ≤ 0.00000011485 := by
  have hl := lg_2
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.4586864223738 9.4586864291968 3.1076842 0.00000001484 (-0.9994251631741) 0.033901955793 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_3 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7542403312231):ℝ):ℂ) + (((-0.6565984486134):ℝ):ℂ) * I)‖ ≤ 0.00000012676 := by
  have hl := lg_3
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.991663287617805944 14.99166329444081959 (-2.4252927) 0.00000002675 (-0.7542403312231) (-0.6565984486134) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_4 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.997701315236:ℝ):ℂ) + (((-0.0677649288076):ℝ):ℂ) * I)‖ ≤ 0.00000013687 := by
  have hl := lg_4
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.9173728447476 18.9173728583936 (-0.0678169) 0.00000003686 0.997701315236 (-0.0677649288076) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_5 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9995864923695):ℝ):ℂ) + (((-0.0287548892021):ℝ):ℂ) * I)‖ ≤ 0.0000001381 := by
  have hl := lg_5
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.962389745981296014 21.96238975962730966 (-3.1128338) 0.00000003809 (-0.9995864923695) (-0.0287548892021) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_6 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7760667380934:ℝ):ℂ) + ((0.6306507892844:ℝ):ℂ) * I)‖ ≤ 0.00000011874 := by
  have hl := lg_6
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.450349709991605944 24.45034972363761959 0.6823915 0.00000001873 0.7760667380934 0.6306507892844 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_7 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1490897067693:ℝ):ℂ) + (((-0.9888236745423):ℝ):ℂ) * I)‖ ≤ 0.00000014182 := by
  have hl := lg_7
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.553889886914368612 26.553889900560395904 (-1.4211487) 0.00000004181 0.1490897067693 (-0.9888236745423) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_8 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9948304362186):ℝ):ℂ) + ((0.1015500009865:ℝ):ℂ) * I)‖ ≤ 0.00000015171 := by
  have hl := lg_8
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.3760592671214 28.3760592875904 3.0398673 0.0000000517 (-0.9948304362186) 0.1015500009865 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_9 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1377568625696:ℝ):ℂ) + ((0.9904660755497:ℝ):ℂ) * I)‖ ≤ 0.000000153 := by
  have hl := lg_9
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.983326575235611888 29.98332658888163918 1.4326 0.00000005299 0.1377568625696 0.9904660755497 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_10 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999867408392:ℝ):ℂ) + (((-0.0051495772402):ℝ):ℂ) * I)‖ ≤ 0.00000015294 := by
  have hl := lg_10
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.421076168355096014 31.42107618882410966 (-0.0051496) 0.00000005293 0.9999867408392 (-0.0051495772402) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_11 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2619516613172:ℝ):ℂ) + (((-0.9650809951155):ℝ):ℂ) * I)‖ ≤ 0.00000015395 := by
  have hl := lg_11
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.721678881964901318 32.72167890243392861 (-1.3057524) 0.00000005394 0.2619516613172 (-0.9650809951155) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_12 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7970009175884):ℝ):ℂ) + (((-0.6039780934067):ℝ):ℂ) * I)‖ ≤ 0.00000011695 := by
  have hl := lg_12
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.909036132365405944 33.90903615283441959 (-2.4931096) 0.00000001694 (-0.7970009175884) (-0.6039780934067) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_13 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9031352579191):ℝ):ℂ) + ((0.4293561526091:ℝ):ℂ) * I)‖ ≤ 0.00000012181 := by
  have hl := lg_13
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.0012989212784782 35.001298941747505492 2.6978129 0.0000000218 (-0.9031352579191) 0.4293561526091 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_14 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.115480947786):ℝ):ℂ) + ((0.9933096952602:ℝ):ℂ) * I)‖ ≤ 0.0000001338 := by
  have hl := lg_14
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.012576309288168612 36.012576329757195904 1.6865355 0.00000003379 (-0.115480947786) 0.9933096952602 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p646_15 : ‖exp (-((((((13646:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7350480363681:ℝ):ℂ) + ((0.6780150324523:ℝ):ℂ) * I)‖ ≤ 0.00000011101 := by
  have hl := lg_15
  refine (ecis_approx ((((13646:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.954053033599101958 36.95405305406812925 0.7450588 0.000000011 0.7350480363681 0.6780150324523 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_2 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9877639513568):ℝ):ℂ) + ((0.1559563272711:ℝ):ℂ) * I)‖ ≤ 0.00000014109 := by
  have hl := lg_2
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.5813734732869 9.5813734801984 2.9849971 0.00000004108 (-0.9877639513568) 0.1559563272711 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_3 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8669006833286):ℝ):ℂ) + (((-0.4984808974864):ℝ):ℂ) * I)‖ ≤ 0.00000015171 := by
  have hl := lg_3
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.186117662666050972 15.186117669577564795 (-2.6197471) 0.0000000517 (-0.8669006833286) (-0.4984808974864) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_4 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9513552808737:ℝ):ℂ) + (((-0.3080959745821):ℝ):ℂ) * I)‖ ≤ 0.00000013887 := by
  have hl := lg_4
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.1627469465738 19.1627469603968 (-0.313191) 0.00000003886 0.9513552808737 (-0.3080959745821) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_5 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9673822882259):ℝ):ℂ) + ((0.2533209587981:ℝ):ℂ) * I)‖ ≤ 0.00000014151 := by
  have hl := lg_5
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.247260256390111007 22.24726027021312483 2.885481 0.0000000415 (-0.9673822882259) 0.2533209587981 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_6 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9340344589323:ℝ):ℂ) + ((0.3571829076636:ℝ):ℂ) * I)‖ ≤ 0.00000012107 := by
  have hl := lg_6
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.767491135952950972 24.767491149775964795 0.3652501 0.00000002106 0.9340344589323 0.3571829076636 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_7 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.193549201864):ℝ):ℂ) + (((-0.9810905699562):ℝ):ℂ) * I)‖ ≤ 0.00000014553 := by
  have hl := lg_7
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.898315983205138306 26.898315997028165952 (-1.7655748) 0.00000004552 (-0.193549201864) (-0.9810905699562) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_8 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8916649348062):ℝ):ℂ) + ((0.4526959729551:ℝ):ℂ) * I)‖ ≤ 0.00000011605 := by
  have hl := lg_8
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.7441204198607 28.7441204405952 2.6718061 0.00000001604 (-0.8916649348062) 0.4526959729551 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_9 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5030335093671:ℝ):ℂ) + ((0.8642669081099:ℝ):ℂ) * I)‖ ≤ 0.00000011058 := by
  have hl := lg_9
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.372235325332101944 30.37223533915512959 1.0436912 0.00000001057 0.5030335093671 0.8642669081099 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_10 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9160383482061:ℝ):ℂ) + (((-0.4010906937538):ℝ):ℂ) * I)‖ ≤ 0.00000011453 := by
  have hl := lg_10
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.828633729677011007 31.82863375041152483 (-0.4127072) 0.00000001452 0.9160383482061 (-0.4010906937538) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_11 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1587095243012):ℝ):ℂ) + (((-0.9873253196872):ℝ):ℂ) * I)‖ ≤ 0.00000012996 := by
  have hl := lg_11
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.146106345112181659 33.146106365846709305 (-1.7301798) 0.00000002995 (-0.1587095243012) (-0.9873253196872) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_12 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9783105009076):ℝ):ℂ) + (((-0.2071438232242):ℝ):ℂ) * I)‖ ≤ 0.00000012667 := by
  have hl := lg_12
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.348864609239850972 34.348864629974364795 (-2.9329381) 0.00000002666 (-0.9783105009076) (-0.2071438232242) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_13 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6233507412634):ℝ):ℂ) + ((0.7819423593542:ℝ):ℂ) * I)‖ ≤ 0.00000013508 := by
  have hl := lg_13
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.4552949574111391 35.455294978145666746 2.2438169 0.00000003507 (-0.6233507412634) 0.7819423593542 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_14 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3441881127502:ℝ):ℂ) + ((0.938900709895:ℝ):ℂ) * I)‖ ≤ 0.00000013416 := by
  have hl := lg_14
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.479689456492038306 36.479689477226565952 1.2194224 0.00000003415 0.3441881127502 0.938900709895 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_15 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9649000257828:ℝ):ℂ) + ((0.262617478939:ℝ):ℂ) * I)‖ ≤ 0.00000012404 := by
  have hl := lg_15
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.433377919056161979 37.433377939790689625 0.2657339 0.00000002403 0.9649000257828 0.262617478939 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_16 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8101536822708:ℝ):ℂ) + (((-0.5862175458847):ℝ):ℂ) * I)‖ ≤ 0.00000014994 := by
  have hl := lg_16
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.3254938931476 38.3254939207936 (-0.6263821) 0.00000004993 0.8101536822708 (-0.5862175458847) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_17 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1061994813287:ℝ):ℂ) + (((-0.9943448446919):ℝ):ℂ) * I)‖ ≤ 0.0000001251 := by
  have hl := lg_17
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.163508040516167182 39.163508068162181005 (-1.4643962) 0.00000002509 0.1061994813287 (-0.9943448446919) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_18 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6316662543247):ℝ):ℂ) + (((-0.775240442142):ℝ):ℂ) * I)‖ ≤ 0.00000014447 := by
  have hl := lg_18
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.953608798619001944 39.95360881935352959 (-2.254497) 0.00000004446 (-0.6316662543247) (-0.775240442142) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_19 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9902544090459):ℝ):ℂ) + (((-0.1392702586903):ℝ):ℂ) * I)‖ ≤ 0.00000014485 := by
  have hl := lg_19
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.700979998238013269 40.700980018972554738 (-3.0018682) 0.00000004484 (-0.9902544090459) (-0.1392702586903) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v13p823_20 : ‖exp (-((((((13823:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8422770269779):ℝ):ℂ) + ((0.5390449051388:ℝ):ℂ) * I)‖ ≤ 0.00000014731 := by
  have hl := lg_20
  refine (ecis_approx ((((13823:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.410007202963911007 41.41000723060992483 2.5722899 0.0000000473 (-0.8422770269779) 0.5390449051388 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_2 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9612534612314):ℝ):ℂ) + ((0.2756660716035:ℝ):ℂ) * I)‖ ≤ 0.00000011686 := by
  have hl := lg_2
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.7040605242 9.7040605312 2.8623101 0.00000001685 (-0.9612534612314) 0.2756660716035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_3 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9468844694169):ℝ):ℂ) + (((-0.3215739438788):ℝ):ℂ) * I)‖ ≤ 0.00000013037 := by
  have hl := lg_3
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.380572037714296 15.38057204471431 (-2.8142014) 0.00000003036 (-0.9468844694169) (-0.3215739438788) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_4 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8480164376045:ℝ):ℂ) + (((-0.5299699251396):ℝ):ℂ) * I)‖ ≤ 0.00000014088 := by
  have hl := lg_4
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.4081210484 19.4081210624 (-0.5585651) 0.00000004087 0.8480164376045 (-0.5299699251396) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_5 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8572033072315):ℝ):ℂ) + ((0.5149781451605:ℝ):ℂ) * I)‖ ≤ 0.0000001521 := by
  have hl := lg_5
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.532130766798926 22.53213078079894 2.6006105 0.00000005209 (-0.8572033072315) 0.5149781451605 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_6 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9988429996693:ℝ):ℂ) + ((0.0480901446412:ℝ):ℂ) * I)‖ ≤ 0.00000014721 := by
  have hl := lg_6
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.084632561914296 25.08463257591431 0.0481087 0.0000000472 0.9988429996693 0.0480901446412 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_7 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5134535846096):ℝ):ℂ) + (((-0.8581173675231):ℝ):ℂ) * I)‖ ≤ 0.00000014924 := by
  have hl := lg_7
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.242742079495908 27.242742093495936 (-2.1100009) 0.00000004923 (-0.5134535846096) (-0.8581173675231) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_8 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6690640085059):ℝ):ℂ) + ((0.7432047850377:ℝ):ℂ) * I)‖ ≤ 0.00000015772 := by
  have hl := lg_8
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.1121815726 29.1121815936 2.303745 0.00000005771 (-0.6690640085059) 0.7432047850377 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_9 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.793180401478:ℝ):ℂ) + ((0.6089867409979:ℝ):ℂ) * I)‖ ≤ 0.00000015355 := by
  have hl := lg_9
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.761144075428592 30.76114408942862 0.6547825 0.00000005354 0.793180401478 0.6089867409979 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_10 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6820275759558:ℝ):ℂ) + (((-0.7313264562669):ℝ):ℂ) * I)‖ ≤ 0.00000014491 := by
  have hl := lg_10
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.236191290998926 32.23619131199894 (-0.8202648) 0.0000000449 0.6820275759558 (-0.7313264562669) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_11 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5512076862086):ℝ):ℂ) + (((-0.8343680762444):ℝ):ℂ) * I)‖ ≤ 0.00000012765 := by
  have hl := lg_11
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.570533808259462 33.57053382925949 (-2.1546073) 0.00000002764 (-0.5512076862086) (-0.8343680762444) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_12 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9733980889836):ℝ):ℂ) + ((0.2291204051926:ℝ):ℂ) * I)‖ ≤ 0.00000015698 := by
  have hl := lg_12
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.788693086114296 34.78869310711431 2.9104187 0.00000005697 (-0.9733980889836) 0.2291204051926 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_13 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2172775052817):ℝ):ℂ) + ((0.9761098737835:ℝ):ℂ) * I)‖ ≤ 0.00000014955 := by
  have hl := lg_13
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.9092909935438 35.909291014543828 1.7898208 0.00000004954 (-0.2172775052817) 0.9761098737835 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_14 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7301128792184:ℝ):ℂ) + ((0.6833265570717:ℝ):ℂ) * I)‖ ≤ 0.0000001394 := by
  have hl := lg_14
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.946802603695908 36.946802624695936 0.7523092 0.00000003939 0.7301128792184 0.6833265570717 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_15 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9772760308477:ℝ):ℂ) + (((-0.2119706572396):ℝ):ℂ) * I)‖ ≤ 0.00000013858 := by
  have hl := lg_15
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.912702804513222 37.91270282551325 (-0.213591) 0.00000003857 0.9772760308477 (-0.2119706572396) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_16 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4382636670103:ℝ):ℂ) + (((-0.8988464597353):ℝ):ℂ) * I)‖ ≤ 0.00000014629 := by
  have hl := lg_16
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.8162420968 38.8162421248 (-1.1171303) 0.00000004628 0.4382636670103 (-0.8988464597353) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_17 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3848808027154):ℝ):ℂ) + (((-0.9229662874115):ℝ):ℂ) * I)‖ ≤ 0.00000014086 := by
  have hl := lg_17
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.664986802230076 39.66498683023009 (-1.965875) 0.00000004085 (-0.3848808027154) (-0.9229662874115) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_18 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9303244229834):ℝ):ℂ) + (((-0.3667376007999):ℝ):ℂ) * I)‖ ≤ 0.00000014346 := by
  have hl := lg_18
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.465204599628592 40.46520462062862 (-2.7660928) 0.00000004345 (-0.9303244229834) (-0.3667376007999) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_19 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9281290807361):ℝ):ℂ) + ((0.3722585248665:ℝ):ℂ) * I)‖ ≤ 0.00000015286 := by
  have hl := lg_19
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.222145697412442 41.222145718412484 2.7601514 0.00000005285 (-0.9281290807361) 0.3722585248665 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14_20 : ‖exp (-((((((14000:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4539994767557):ℝ):ℂ) + ((0.8910019501106:ℝ):ℂ) * I)‖ ≤ 0.00000013507 := by
  have hl := lg_20
  refine (ecis_approx ((((14000:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.940251815198926 41.94025184319894 2.0420453 0.00000003506 (-0.4539994767557) 0.8910019501106 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_2 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9320457434291):ℝ):ℂ) + ((0.362340629784:ℝ):ℂ) * I)‖ ≤ 0.00000014472 := by
  have hl := lg_2
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.7955559519996 9.7955559590656 2.7708147 0.00000004471 (-0.9320457434291) 0.362340629784 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_3 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9834158221602):ℝ):ℂ) + (((-0.1813651575614):ℝ):ℂ) * I)‖ ≤ 0.00000015251 := by
  have hl := lg_3
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.525588859784173648 15.52558886685018778 (-2.9592182) 0.0000000525 (-0.9834158221602) (-0.1813651575614) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_4 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7374184731962:ℝ):ℂ) + (((-0.6754361519707):ℝ):ℂ) * I)‖ ≤ 0.00000011755 := by
  have hl := lg_4
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.5911119039992 19.5911119181312 (-0.741556) 0.00000001754 0.7374184731962 (-0.6754361519707) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_5 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7293479484265):ℝ):ℂ) + ((0.6841429456604:ℝ):ℂ) * I)‖ ≤ 0.0000001566 := by
  have hl := lg_5
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.744576571171601588 22.74457658530361572 2.3881647 0.00000005659 (-0.7293479484265) 0.6841429456604 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_6 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.982304478014:ℝ):ℂ) + (((-0.1872909834287):ℝ):ℂ) * I)‖ ≤ 0.00000011695 := by
  have hl := lg_6
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.321144811783773648 25.32114482591578778 (-0.1884036) 0.00000001694 0.982304478014 (-0.1872909834287) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_7 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7146087746242):ℝ):ℂ) + (((-0.6995243378209):ℝ):ℂ) * I)‖ ≤ 0.00000010963 := by
  have hl := lg_7
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.499602219102583704 27.499602233234611968 (-2.366861) 0.00000000962 (-0.7146087746242) (-0.6995243378209) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_8 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4425697883663):ℝ):ℂ) + ((0.8967340644924:ℝ):ℂ) * I)‖ ≤ 0.00000014131 := by
  have hl := lg_8
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.3866678559988 29.3866678771968 2.0292587 0.0000000413 (-0.4425697883663) 0.8967340644924 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_9 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9342133973542:ℝ):ℂ) + ((0.3567146313286:ℝ):ℂ) * I)‖ ≤ 0.00000011634 := by
  have hl := lg_9
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.051177719568347296 31.05117773370037556 0.3647488 0.00000001633 0.9342133973542 0.3567146313286 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_10 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4318927812785:ℝ):ℂ) + (((-0.9019249555698):ℝ):ℂ) * I)‖ ≤ 0.00000011274 := by
  have hl := lg_10
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.540132523171201588 32.54013254436921572 (-1.124206) 0.00000001273 0.4318927812785 (-0.9019249555698) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_11 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7835339699244):ℝ):ℂ) + (((-0.6213489502133):ℝ):ℂ) * I)‖ ≤ 0.00000015175 := by
  have hl := lg_11
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.887055984165908356 33.88705600536393662 (-2.4711295) 0.00000005174 (-0.7835339699244) (-0.6213489502133) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_12 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8476895746152):ℝ):ℂ) + ((0.5304925871454:ℝ):ℂ) * I)‖ ≤ 0.00000014192 := by
  have hl := lg_12
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.116700763783373648 35.11670078498138778 2.5824111 0.00000004191 (-0.8476895746152) 0.5304925871454 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_13 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1192642664657:ℝ):ℂ) + ((0.9928625457455:ℝ):ℂ) * I)‖ ≤ 0.00000013447 := by
  have hl := lg_13
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.2478643086257844 36.247864329823812664 1.4512475 0.00000003446 0.1192642664657 0.9928625457455 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_14 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9195141558288:ℝ):ℂ) + ((0.3930568880333:ℝ):ℂ) * I)‖ ≤ 0.00000014924 := by
  have hl := lg_14
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.295158171102183704 37.295158192300211968 0.4039537 0.00000004923 0.9195141558288 0.3930568880333 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p132_15 : ‖exp (-((((((14132:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8413319516552:ℝ):ℂ) + (((-0.5405187759218):ℝ):ℂ) * I)‖ ≤ 0.00000011214 := by
  have hl := lg_15
  refine (ecis_approx ((((14132:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.270165430955775236 38.2701654521538035 (-0.5710536) 0.00000001213 0.8413319516552 (-0.5405187759218) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_2 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8950408872819):ℝ):ℂ) + ((0.4459840916251:ℝ):ℂ) * I)‖ ≤ 0.00000013457 := by
  have hl := lg_2
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.8870513797992 9.8870513869312 2.6793192 0.00000003456 (-0.8950408872819) 0.4459840916251 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_3 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993022874536):ℝ):ℂ) + (((-0.0373488646389):ℝ):ℂ) * I)‖ ≤ 0.00000013252 := by
  have hl := lg_3
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.670605681854051296 15.67060568898606556 (-3.1042351) 0.00000003251 (-0.9993022874536) (-0.0373488646389) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_4 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6021964654941:ℝ):ℂ) + (((-0.7983479297564):ℝ):ℂ) * I)‖ ≤ 0.00000015234 := by
  have hl := lg_4
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.7741027595984 19.7741027738624 (-0.9245468) 0.00000005233 0.6021964654941 (-0.7983479297564) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_5 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5686983085977):ℝ):ℂ) + ((0.8225461894558:ℝ):ℂ) * I)‖ ≤ 0.00000015319 := by
  have hl := lg_5
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.957022375544277176 22.95702238980829144 2.1757188 0.00000005318 (-0.5686983085977) 0.8225461894558 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_6 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9110734471343:ℝ):ℂ) + (((-0.4122440708206):ℝ):ℂ) * I)‖ ≤ 0.00000014721 := by
  have hl := lg_6
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.557657061653251296 25.55765707591726556 (-0.4249158) 0.0000000472 0.9110734471343 (-0.4122440708206) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_7 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8688747958689):ℝ):ℂ) + (((-0.4950319070693):ℝ):ℂ) * I)‖ ≤ 0.00000014427 := by
  have hl := lg_7
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.756462358709259408 27.756462372973287936 (-2.6237211) 0.00000004426 (-0.8688747958689) (-0.4950319070693) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_8 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1829399825121):ℝ):ℂ) + ((0.9831240831135:ℝ):ℂ) * I)‖ ≤ 0.00000012491 := by
  have hl := lg_8
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.6611541393976 29.6611541607936 1.7547724 0.0000000249 (-0.1829399825121) 0.9831240831135 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_9 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.997210117651:ℝ):ℂ) + ((0.0746457048624:ℝ):ℂ) * I)‖ ≤ 0.00000014209 := by
  have hl := lg_9
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.341211363708102592 31.34121137797213112 0.0747152 0.00000004208 0.997210117651 0.0746457048624 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_10 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1421658296567:ℝ):ℂ) + (((-0.989842854638):ℝ):ℂ) * I)‖ ≤ 0.00000014086 := by
  have hl := lg_10
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.844073755343477176 32.84407377673949144 (-1.4281472) 0.00000004085 0.1421658296567 (-0.989842854638) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_11 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9380140425375):ℝ):ℂ) + (((-0.3465972530578):ℝ):ℂ) * I)‖ ≤ 0.00000014559 := by
  have hl := lg_11
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.203578160072354712 34.20357818146838324 (-2.7876516) 0.00000004558 (-0.9380140425375) (-0.3465972530578) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_12 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6315936890524):ℝ):ℂ) + ((0.7752995627074:ℝ):ℂ) * I)‖ ≤ 0.00000011979 := by
  have hl := lg_12
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.444708441452451296 35.44470846284846556 2.2544034 0.00000001978 (-0.6315936890524) 0.7752995627074 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_13 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4422646522082:ℝ):ℂ) + ((0.8968845953673:ℝ):ℂ) * I)‖ ≤ 0.00000011938 := by
  have hl := lg_13
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.5864376237077688 36.586437645103797328 1.1126742 0.00000001937 0.4422646522082 0.8968845953673 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_14 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9984548237305:ℝ):ℂ) + ((0.0555694607608:ℝ):ℂ) * I)‖ ≤ 0.00000011684 := by
  have hl := lg_14
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.643513738508459408 37.643513759904487936 0.0555981 0.00000001683 0.9984548237305 0.0555694607608 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p264_15 : ‖exp (-((((((14264:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5990227674049:ℝ):ℂ) + (((-0.8007319926983):ℝ):ℂ) * I)‖ ≤ 0.00000013573 := by
  have hl := lg_15
  refine (ecis_approx ((((14264:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.627628057398328472 38.627628078794357 (-0.9285162) 0.00000003572 0.5990227674049 (-0.8007319926983) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_2 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.850548540334):ℝ):ℂ) + ((0.525896549201:ℝ):ℂ) * I)‖ ≤ 0.00000010678 := by
  have hl := lg_2
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.9785468075988 9.9785468147968 2.5878238 0.00000000677 (-0.850548540334) 0.525896549201 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_3 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9942103376887):ℝ):ℂ) + ((0.1074514028324:ℝ):ℂ) * I)‖ ≤ 0.00000011763 := by
  have hl := lg_3
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.815622503923928944 15.81562251112194334 3.0339334 0.00000001762 (-0.9942103376887) 0.1074514028324 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_4 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4468656454136:ℝ):ℂ) + (((-0.8946010814598):ℝ):ℂ) * I)‖ ≤ 0.00000010807 := by
  have hl := lg_4
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.9570936151976 19.9570936295936 (-1.1075377) 0.00000000806 0.4468656454136 (-0.8946010814598) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_5 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3824779442469):ℝ):ℂ) + ((0.9239646217046:ℝ):ℂ) * I)‖ ≤ 0.00000014882 := by
  have hl := lg_5
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.169468179916952764 23.16946819431296716 1.963273 0.00000004881 (-0.3824779442469) 0.9239646217046 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_6 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7891158340362:ℝ):ℂ) + (((-0.6142444142793):ℝ):ℂ) * I)‖ ≤ 0.00000011721 := by
  have hl := lg_6
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.794169311522728944 25.79416932591874334 (-0.6614281) 0.0000000172 0.7891158340362 (-0.6142444142793) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_7 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.966129484513):ℝ):ℂ) + (((-0.2580577820938):ℝ):ℂ) * I)‖ ≤ 0.00000013042 := by
  have hl := lg_7
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.013322498315935112 28.013322512711963904 (-2.8805813) 0.00000003041 (-0.966129484513) (-0.2580577820938) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_8 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0903866992477:ℝ):ℂ) + ((0.995906744931:ℝ):ℂ) * I)‖ ≤ 0.00000011312 := by
  have hl := lg_8
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.9356404227964 29.9356404443904 1.4802861 0.00000001311 0.0903866992477 0.995906744931 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_9 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9769083934988:ℝ):ℂ) + (((-0.2136585844559):ℝ):ℂ) * I)‖ ≤ 0.00000012807 := by
  have hl := lg_9
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.631245007847857888 31.63124502224388668 (-0.2153185) 0.00000002806 0.9769083934988 (-0.2136585844559) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_10 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1605937418945):ℝ):ℂ) + (((-0.9870205925226):ℝ):ℂ) * I)‖ ≤ 0.0000001484 := by
  have hl := lg_10
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.148014987515752764 33.14801500910976716 (-1.7320885) 0.00000004839 (-0.1605937418945) (-0.9870205925226) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_11 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9992999960907):ℝ):ℂ) + (((-0.037410121799):ℝ):ℂ) * I)‖ ≤ 0.00000012169 := by
  have hl := lg_11
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.520100335978801068 34.52010035757282986 (-3.1041738) 0.00000002168 (-0.9992999960907) (-0.037410121799) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_12 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3481523029479):ℝ):ℂ) + ((0.9374379840553:ℝ):ℂ) * I)‖ ≤ 0.00000012397 := by
  have hl := lg_12
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.772716119121528944 35.77271614071554334 1.9263957 0.00000002396 (-0.3481523029479) 0.9374379840553 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_13 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7150498599324:ℝ):ℂ) + ((0.6990734566629:ℝ):ℂ) * I)‖ ≤ 0.00000011732 := by
  have hl := lg_13
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.9250109387897532 36.925010960383781992 0.7741009 0.00000001731 0.7150498599324 0.6990734566629 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_14 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9574517201032:ℝ):ℂ) + (((-0.2885934920809):ℝ):ℂ) * I)‖ ≤ 0.00000013718 := by
  have hl := lg_14
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.991869305914735112 37.991869327508763904 (-0.2927575) 0.00000003717 0.9574517201032 (-0.2885934920809) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p396_15 : ‖exp (-((((((14396:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2809822381066:ℝ):ℂ) + (((-0.9597129684799):ℝ):ℂ) * I)‖ ≤ 0.00000015925 := by
  have hl := lg_15
  refine (ecis_approx ((((14396:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.985090683840881708 38.9850907054349105 (-1.2859789) 0.00000005924 0.2809822381066 (-0.9597129684799) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_2 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7989408701887):ℝ):ℂ) + ((0.6014095824754:ℝ):ℂ) * I)‖ ≤ 0.00000012832 := by
  have hl := lg_2
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.0700422353984 10.0700422426624 2.4963284 0.00000002831 (-0.7989408701887) 0.6014095824754 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_3 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9682468868295):ℝ):ℂ) + ((0.2499959317287:ℝ):ℂ) * I)‖ ≤ 0.00000011173 := by
  have hl := lg_3
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.960639325993806592 15.96063933325782112 2.8889166 0.00000001172 (-0.9682468868295) 0.2499959317287 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_4 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.276612938949:ℝ):ℂ) + (((-0.9609814160565):ℝ):ℂ) * I)‖ ≤ 0.00000015076 := by
  have hl := lg_4
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.1400844707968 20.1400844853248 (-1.2905286) 0.00000005075 0.276612938949 (-0.9609814160565) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_5 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1790599477487):ℝ):ℂ) + ((0.9838381651021:ℝ):ℂ) * I)‖ ≤ 0.00000014444 := by
  have hl := lg_5
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.381913984289628352 23.38191399881764288 1.7508272 0.00000004443 (-0.1790599477487) 0.9838381651021 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_6 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6232220670182:ℝ):ℂ) + (((-0.7820449189027):ℝ):ℂ) * I)‖ ≤ 0.00000014722 := by
  have hl := lg_6
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.030681561392206592 26.03068157592022112 (-0.8979403) 0.00000004721 0.6232220670182 (-0.7820449189027) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_7 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999913832218):ℝ):ℂ) + (((-0.0041512413659):ℝ):ℂ) * I)‖ ≤ 0.00000012375 := by
  have hl := lg_7
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.270182637922610816 28.270182652450639872 (-3.1374414) 0.00000002374 (-0.9999913832218) (-0.0041512413659) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_8 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3569460500713:ℝ):ℂ) + ((0.9341250009171:ℝ):ℂ) * I)‖ ≤ 0.00000012972 := by
  have hl := lg_8
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.2101267061952 30.2101267279872 1.2057998 0.00000002971 0.3569460500713 0.9341250009171 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_9 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8750040715804:ℝ):ℂ) + (((-0.4841155592602):ℝ):ℂ) * I)‖ ≤ 0.00000013063 := by
  have hl := lg_9
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.921278651987613184 31.92127866651564224 (-0.5053521) 0.00000003062 0.8750040715804 (-0.4841155592602) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_10 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4486313832361):ℝ):ℂ) + (((-0.8937168913986):ℝ):ℂ) * I)‖ ≤ 0.00000011622 := by
  have hl := lg_10
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.451956219688028352 33.45195624148004288 (-2.0360297) 0.00000001621 (-0.4486313832361) (-0.8937168913986) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_11 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9613028451569):ℝ):ℂ) + ((0.2754938105579:ℝ):ℂ) * I)‖ ≤ 0.00000013121 := by
  have hl := lg_11
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.836622511885247424 34.83662253367727648 2.8624893 0.0000000312 (-0.9613028451569) 0.2754938105579 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_12 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.027588172413):ℝ):ℂ) + ((0.9996193739332:ℝ):ℂ) * I)‖ ≤ 0.0000001463 := by
  have hl := lg_12
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.100723796790606592 36.10072381858262112 1.598388 0.00000004629 (-0.027588172413) 0.9996193739332 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_13 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9066475799629:ℝ):ℂ) + ((0.4218888073265:ℝ):ℂ) * I)‖ ≤ 0.0000001326 := by
  have hl := lg_13
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.2635842538717376 37.263584275663766656 0.4355276 0.00000003259 0.9066475799629 0.4218888073265 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_14 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8014305826897:ℝ):ℂ) + (((-0.598087803863):ℝ):ℂ) * I)‖ ≤ 0.00000015205 := by
  have hl := lg_14
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.340224873321010816 38.340224895113039872 (-0.641113) 0.00000005204 0.8014305826897 (-0.598087803863) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p528_15 : ‖exp (-((((((14528:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0725812947442):ℝ):ℂ) + (((-0.9973624996223):ℝ):ℂ) * I)‖ ≤ 0.00000013281 := by
  have hl := lg_15
  refine (ecis_approx ((((14528:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.342553310283434944 39.342553332075464 (-1.6434415) 0.0000000328 (-0.0725812947442) (-0.9973624996223) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_2 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6903330387915):ℝ):ℂ) + ((0.7234917383984:ℝ):ℂ) * I)‖ ≤ 0.00000014442 := by
  have hl := lg_2
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.2336249699492 10.2336249773312 2.3327456 0.00000004441 (-0.6903330387915) 0.7234917383984 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_3 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8717916118528):ℝ):ℂ) + ((0.4898769084309:ℝ):ℂ) * I)‖ ≤ 0.00000011192 := by
  have hl := lg_3
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.219911826058133296 16.21991183344014806 2.6296441 0.00000001191 (-0.8717916118528) 0.4898769084309 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_4 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0468804840363):ℝ):ℂ) + (((-0.9989005056642):ℝ):ℂ) * I)‖ ≤ 0.00000013314 := by
  have hl := lg_4
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.4672499398984 20.4672499546624 (-1.617694) 0.00000003313 (-0.0468804840363) (-0.9989005056642) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_5 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1984698113853:ℝ):ℂ) + ((0.9801070012854:ℝ):ℂ) * I)‖ ≤ 0.00000011756 := by
  have hl := lg_5
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.761741331501381676 23.76174134626539644 1.3709999 0.00000001755 0.1984698113853 0.9801070012854 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_6 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2474046634551:ℝ):ℂ) + (((-0.9689122418984):ℝ):ℂ) * I)‖ ≤ 0.00000013273 := by
  have hl := lg_6
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.453536796007333296 26.45353681077134806 (-1.3207956) 0.00000003272 0.2474046634551 (-0.9689122418984) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_7 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8982243063558):ℝ):ℂ) + ((0.4395373651434:ℝ):ℂ) * I)‖ ≤ 0.00000011186 := by
  have hl := lg_7
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.729417432976970408 28.729417447740999936 2.6865091 0.00000001185 (-0.8982243063558) 0.4395373651434 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_8 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7550594103476:ℝ):ℂ) + ((0.6556563786356:ℝ):ℂ) * I)‖ ≤ 0.00000012607 := by
  have hl := lg_8
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.7008749098476 30.7008749319936 0.7150516 0.00000002606 0.7550594103476 0.6556563786356 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_9 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5200412352089:ℝ):ℂ) + (((-0.8541411555957):ℝ):ℂ) * I)‖ ≤ 0.000000131 := by
  have hl := lg_9
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.439823652116266592 32.43982366688029612 (-1.0238971) 0.00000003099 0.5200412352089 (-0.8541411555957) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_10 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8461095823472):ℝ):ℂ) + (((-0.5330089817149):ℝ):ℂ) * I)‖ ≤ 0.00000013446 := by
  have hl := lg_10
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.995366301450581676 33.99536632359659644 (-2.5794398) 0.00000003445 (-0.8461095823472) (-0.5330089817149) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_11 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6637263057772):ℝ):ℂ) + ((0.7479755283436:ℝ):ℂ) * I)‖ ≤ 0.00000014701 := by
  have hl := lg_11
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.402525796081621212 35.40252581822765074 2.296586 0.000000047 (-0.6637263057772) 0.7479755283436 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_12 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5302083043373:ℝ):ℂ) + ((0.8478674153497:ℝ):ℂ) * I)‖ ≤ 0.00000014504 := by
  have hl := lg_12
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.687161765956533296 36.68716178810254806 1.0119501 0.00000004503 0.5302083043373 0.8478674153497 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_13 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9856184991747:ℝ):ℂ) + (((-0.1689857215406):ℝ):ℂ) * I)‖ ≤ 0.00000014104 := by
  have hl := lg_13
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.8689123020486188 37.868912324194648328 (-0.1698005) 0.00000004103 0.9856184991747 (-0.1689857215406) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_14 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3020722693439:ℝ):ℂ) + (((-0.9532850277296):ℝ):ℂ) * I)‖ ≤ 0.00000014017 := by
  have hl := lg_14
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.963042402926170408 38.963042425072199936 (-1.2639306) 0.00000004016 0.3020722693439 (-0.9532850277296) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v14p764_15 : ‖exp (-((((((14764:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6531560991072):ℝ):ℂ) + (((-0.7572232895137):ℝ):ℂ) * I)‖ ≤ 0.00000013664 := by
  have hl := lg_15
  refine (ecis_approx ((((14764:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.981653157559514972 39.9816531797055445 (-2.2825413) 0.00000003663 (-0.6531560991072) (-0.7572232895137) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15_2 : ‖exp (-((((((15000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5632935954295):ℝ):ℂ) + ((0.826256815608:ℝ):ℂ) * I)‖ ≤ 0.00000010987 := by
  have hl := lg_2
  refine (ecis_approx ((((15000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.3972077045 10.397207712 2.1691629 0.00000000986 (-0.5632935954295) 0.826256815608 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15_3 : ‖exp (-((((((15000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7170601161939):ℝ):ℂ) + ((0.6970113268357:ℝ):ℂ) * I)‖ ≤ 0.0000001121 := by
  have hl := lg_3
  refine (ecis_approx ((((15000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.47918432612246 16.479184333622475 2.3703716 0.00000001209 (-0.7170601161939) 0.6970113268357 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15_4 : ‖exp (-((((((15000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3654006440121):ℝ):ℂ) + (((-0.9308503474528):ℝ):ℂ) * I)‖ ≤ 0.00000011255 := by
  have hl := lg_4
  refine (ecis_approx ((((15000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.794415409 20.794415424 (-1.9448595) 0.00000001254 (-0.3654006440121) (-0.9308503474528) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15_5 : ‖exp (-((((((15000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5477092431889:ℝ):ℂ) + ((0.8366687426487:ℝ):ℂ) * I)‖ ≤ 0.00000015002 := by
  have hl := lg_5
  refine (ecis_approx ((((15000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.141568678713135 24.14156869371315 0.9911725 0.00000005001 0.5477092431889 0.8366687426487 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15_6 : ‖exp (-((((((15000:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1719949813052):ℝ):ℂ) + (((-0.9850978258047):ℝ):ℂ) * I)‖ ≤ 0.00000011692 := by
  have hl := lg_6
  refine (ecis_approx ((((15000:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.87639203062246 26.876392045622475 (-1.7436508) 0.00000001691 (-0.1719949813052) (-0.9850978258047) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15_7 : ‖exp (-((((((15000:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6103306811647):ℝ):ℂ) + ((0.7921467412141:ℝ):ℂ) * I)‖ ≤ 0.00000010788 := by
  have hl := lg_7
  refine (ecis_approx ((((15000:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.18865222803133 29.18865224303136 2.2272743 0.00000000787 (-0.6103306811647) 0.7921467412141 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15_8 : ‖exp (-((((((15000:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9749492864381:ℝ):ℂ) + ((0.2224272664803:ℝ):ℂ) * I)‖ ≤ 0.00000012241 := by
  have hl := lg_8
  refine (ecis_approx ((((15000:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.1916231135 31.191623136 0.2243034 0.0000000224 0.9749492864381 0.2224272664803 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15_9 : ‖exp (-((((((15000:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0283504276599:ℝ):ℂ) + (((-0.9995980458421):ℝ):ℂ) * I)‖ ≤ 0.00000013136 := by
  have hl := lg_9
  refine (ecis_approx ((((15000:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.95836865224492 32.95836866724495 (-1.5424421) 0.00000003135 0.0283504276599 (-0.9995980458421) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15_10 : ‖exp (-((((((15000:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998243594199):ℝ):ℂ) + (((-0.0187416559615):ℝ):ℂ) * I)‖ ≤ 0.0000001527 := by
  have hl := lg_10
  refine (ecis_approx ((((15000:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.538776383213135 34.53877640571315 (-3.1228499) 0.00000005269 (-0.9998243594199) (-0.0187416559615) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]
lemma bv_b2left_m1_3_5 : (0.861638479504:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-1000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-1000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((-1000:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_b2left_vm1_2 0.3799285857134 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_b2left_vm1_3 0.39068838698905 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_b2left_vm1_4 0.34755274390249 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_b2left_vm1_5 0.29884646908153 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_b2left_vm1_5 1.0625 (by norm_num) (by norm_num) 1.85701728304685 0.55537770618228 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.41701618568647:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-1000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b2left_m0p768_3_5 : (1.117122525615:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-768:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-768:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((-768:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((-768:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((-768:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8616232840327 0.5075483389912 0.00000013487 cs_b2left_vm0p768_2 0.30178996777386 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((-768:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.6646775323363 0.7471303621238 0.0000001379 cs_b2left_vm0p768_3 0.32775955746408 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((-768:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4847892797114 0.8746309817728 0.00000013107 cs_b2left_vm0p768_4 0.30922870278338 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((-768:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3285311933469 0.9444931206727 0.00000011713 cs_b2left_vm0p768_5 0.28246929234386 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((-768:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3285311933469 0.9444931206727 0.00000011713 cs_b2left_vm0p768_5 0.652324 (by norm_num) (by norm_num) 0.34816290372374 0.10412499474997 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.22124752036518:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-768:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_0 : mainRemConst 5 (1 - 1/4:ℝ) 0.807665 ≤ 13.98004571 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 0.807665 (by norm_num) _ 0.2990697562443 1.60943791291421 13.98004571 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_0 : ∀ y ∈ Set.Icc (((-1000:ℤ):ℝ)/1000) (((-768:ℤ):ℝ)/1000), 0 < (I ^ ((3):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((3):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (3) (0) 3 (by norm_num), rot3])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((-1000:ℤ):ℝ)/1000) (((-768:ℤ):ℝ)/1000) (I ^ ((3):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.807665 0.768 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 13.98004571 rb_b2left_0 0.2990697562443 1.25 2.015565 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.861638479504 1.117122525615 (by rw [hrot]; exact bv_b2left_m1_3_5) (by rw [hrot]; exact bv_b2left_m0p768_3_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_m0p471_3_5 : (1.620141890161:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-471:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-471:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((-471:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((-471:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((-471:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9471795811637 0.3207036654399 0.00000012217 cs_b2left_vm0p471_2 0.19069146773155 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((-471:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8690851819509 0.4946624571497 0.00000011217 cs_b2left_vm0p471_3 0.21700408580462 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((-471:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7942983179468 0.607527927018 0.00000014433 cs_b2left_vm0p471_4 0.21479350744891 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((-471:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.726181259887 0.6875032929296 0.0000001435 cs_b2left_vm0p471_5 0.20561139931703 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((-471:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.726181259887 0.6875032929296 0.0000001435 cs_b2left_vm0p471_5 0.284341 (by norm_num) (by norm_num) (-2.64835013679163) (-0.79204142985956) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.82810046030211:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-471:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_1 : mainRemConst 5 (1 - 1/4:ℝ) 0.533236 ≤ 28.24703999 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 0.533236 (by norm_num) _ 0.2990697562443 1.60943791291421 28.24703999 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_1 : ∀ y ∈ Set.Icc (((-768:ℤ):ℝ)/1000) (((-471:ℤ):ℝ)/1000), 0 < (I ^ ((3):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((3):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (3) (0) 3 (by norm_num), rot3])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((-768:ℤ):ℝ)/1000) (((-471:ℤ):ℝ)/1000) (I ^ ((3):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.533236 0.471 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 28.24703999 rb_b2left_1 0.2990697562443 1.073464 1.911106 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.117122525615 1.620141890161 (by rw [hrot]; exact bv_b2left_m0p768_3_5) (by rw [hrot]; exact bv_b2left_m0p471_3_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_m0p228_3_5 : (1.97411801766:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-228:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-228:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((-228:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((-228:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((-228:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9875380283113 0.1573805662686 0.00000014291 cs_b2left_vm0p228_2 0.09357895961008 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((-228:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9687926638613 0.2478724963533 0.00000010189 cs_b2left_vm0p228_3 0.10873947229381 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((-228:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9504627458058 0.3108384931685 0.00000011446 cs_b2left_vm0p228_4 0.10989796271888 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((-228:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9334252886915 0.3587718361733 0.00000014416 cs_b2left_vm0p228_5 0.10729776247773 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((-228:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9334252886915 0.3587718361733 0.00000014416 cs_b2left_vm0p228_5 0.114484 (by norm_num) (by norm_num) (-5.19813129914264) (-1.55460386055993) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.4195141571005:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-228:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_2 : mainRemConst 5 (1 - 1/4:ℝ) 0.338354 ≤ 73.73004333 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 0.338354 (by norm_num) _ 0.2990697562443 1.60943791291421 73.73004333 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_2 : ∀ y ∈ Set.Icc (((-471:ℤ):ℝ)/1000) (((-228:ℤ):ℝ)/1000), 0 < (I ^ ((3):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((3):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (3) (0) 3 (by norm_num), rot3])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((-471:ℤ):ℝ)/1000) (((-228:ℤ):ℝ)/1000) (I ^ ((3):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.338354 0.228 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 73.73004333 rb_b2left_2 0.2990697562443 0.885631 1.812276 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.620141890161 1.97411801766 (by rw [hrot]; exact bv_b2left_m0p471_3_5) (by rw [hrot]; exact bv_b2left_m0p228_3_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_m0p228_2_5 : (1.628643438049:ℝ) ≤ (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-228:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-228:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((-228:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((-228:ℤ):ℝ)/1000)) (-1) (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((-228:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9875380283113 0.1573805662686 0.00000014291 cs_b2left_vm0p228_2 (-0.58719370977662) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((-228:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9687926638613 0.2478724963533 0.00000010189 cs_b2left_vm0p228_3 (-0.42500099431396) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((-228:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9504627458058 0.3108384931685 0.00000011446 cs_b2left_vm0p228_4 (-0.33603936687998) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((-228:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9334252886915 0.3587718361733 0.00000014416 cs_b2left_vm0p228_5 (-0.27915931667513) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((-228:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9334252886915 0.3587718361733 0.00000014416 cs_b2left_vm0p228_5 0.114484 (by norm_num) (by norm_num) (-14.23091682403487) (-4.25603682569559) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-2.62739338764569):ℝ) ≤ ∑ n ∈ Finset.range 5, (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-228:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b2left_m0p063_2_5 : (3.20615724606:ℝ) ≤ (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-63:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-63:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((-63:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((-63:ℤ):ℝ)/1000)) (-1) (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((-63:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9990466912923 0.043654422661 0.00000012766 cs_b2left_vm0p063_2 (-0.5940367926595) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((-63:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9976057640054 0.0691573540789 0.00000012585 cs_b2left_vm0p063_3 (-0.43764106226909) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((-63:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9961885914868 0.0872255134207 0.0000001448 cs_b2left_vm0p063_4 (-0.35220590538506) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((-63:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9948639700441 0.1012209519225 0.00000011156 cs_b2left_vm0p063_5 (-0.29753375838155) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((-63:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9948639700441 0.1012209519225 0.00000011156 cs_b2left_vm0p063_5 0.066469 (by norm_num) (by norm_num) (-19.68629271877269) (-5.88757476475531) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-2.6814175186952):ℝ) ≤ ∑ n ∈ Finset.range 5, (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((-63:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_3 : mainRemConst 5 (1 - 1/4:ℝ) 0.257815 ≤ 141.14874406 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 0.257815 (by norm_num) _ 0.2990697562443 1.60943791291421 141.14874406 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_3 : ∀ y ∈ Set.Icc (((-228:ℤ):ℝ)/1000) (((-63:ℤ):ℝ)/1000), 0 < (I ^ ((2):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((2):ℤ) = (((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (2) (0) 2 (by norm_num), rot2])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((-228:ℤ):ℝ)/1000) (((-63:ℤ):ℝ)/1000) (I ^ ((2):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.257815 0.063 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 141.14874406 rb_b2left_3 0.2990697562443 0.783891 1.764791 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.628643438049 3.20615724606 (by rw [hrot]; exact bv_b2left_m0p228_2_5) (by rw [hrot]; exact bv_b2left_m0p063_2_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_0p173_2_5 : (2.149746025131:ℝ) ≤ (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((173:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((173:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((173:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((173:ℤ):ℝ)/1000)) (-1) (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((173:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9928188676187 (-0.1196273217131) 0.00000013782 cs_b2left_v0p173_2 (-0.59033371258886) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((173:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9819929207077 (-0.1889177166913) 0.000000126 cs_b2left_v0p173_3 (-0.43079184322409) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((173:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9713786315532 (-0.2375364270211) 0.00000012457 cs_b2left_v0p173_4 (-0.34343425277766) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((173:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9614873624744 (-0.2748491437171) 0.00000014125 cs_b2left_v0p173_5 (-0.2875518333708) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((173:ℤ):ℝ)/1000) ((-1):ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9614873624744 (-0.2748491437171) 0.00000014125 cs_b2left_v0p173_5 0.092429 (by norm_num) (by norm_num) (-16.05597880372844) (-4.8018576670931) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-2.65211164196141):ℝ) ≤ ∑ n ∈ Finset.range 5, (((((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((173:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_4 : mainRemConst 5 (1 - 1/4:ℝ) 0.25 ≤ 152.35924526 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 0.25 (by norm_num) _ 0.2990697562443 1.60943791291421 152.35924526 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_4 : ∀ y ∈ Set.Icc (((-63:ℤ):ℝ)/1000) (((173:ℤ):ℝ)/1000), 0 < (I ^ ((2):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((2):ℤ) = (((-1):ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (2) (0) 2 (by norm_num), rot2])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((-63:ℤ):ℝ)/1000) (((173:ℤ):ℝ)/1000) (I ^ ((2):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.25 0 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 152.35924526 rb_b2left_4 0.2990697562443 0.769695 1.758531 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 3.20615724606 2.149746025131 (by rw [hrot]; exact bv_b2left_m0p063_2_5) (by rw [hrot]; exact bv_b2left_0p173_2_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_0p173_1_5 : (1.858499469128:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((173:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((173:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((173:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((173:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((173:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9928188676187 (-0.1196273217131) 0.00000013782 cs_b2left_v0p173_2 0.07113074911669 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((173:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9819929207077 (-0.1889177166913) 0.000000126 cs_b2left_v0p173_3 0.08287651056613 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((173:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9713786315532 (-0.2375364270211) 0.00000012457 cs_b2left_v0p173_4 0.08398176512055 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((173:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9614873624744 (-0.2748491437171) 0.00000014125 cs_b2left_v0p173_5 0.08219902417179 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((173:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9614873624744 (-0.2748491437171) 0.00000014125 cs_b2left_v0p173_5 0.092429 (by norm_num) (by norm_num) (-5.14365424131083) (-1.53831142015327) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.32018804897516:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((173:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b2left_0p35_1_5 : (1.865039352766:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((350:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((350:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((350:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((350:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((350:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9707163052571 (-0.2402287549567) 0.00000011329 cs_b2left_v0p35_2 0.14284080494872 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((350:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9269807324208 (-0.3751089464684) 0.00000010113 cs_b2left_v0p35_3 0.16455700112614 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((350:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8845802905839 (-0.4663879388561) 0.00000012657 cs_b2left_v0p35_4 0.16489299236509 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((350:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8454958243058 (-0.5339820325455) 0.00000013085 cs_b2left_v0p35_5 0.15969783717888 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((350:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8454958243058 (-0.5339820325455) 0.00000013085 cs_b2left_v0p35_5 0.185 (by norm_num) (by norm_num) (-4.12295356318481) (-1.23305071714783) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.63198863561883:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((350:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_5 : mainRemConst 5 (1 - 1/4:ℝ) 0.304021 ≤ 94.64999565 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 0.304021 (by norm_num) _ 0.2990697562443 1.60943791291421 94.64999565 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_5 : ∀ y ∈ Set.Icc (((173:ℤ):ℝ)/1000) (((350:ℤ):ℝ)/1000), 0 < (I ^ ((1):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((1):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (1) (0) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((173:ℤ):ℝ)/1000) (((350:ℤ):ℝ)/1000) (I ^ ((1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.304021 0.173 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 94.64999565 rb_b2left_5 0.2990697562443 0.827648 1.784657 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.858499469128 1.865039352766 (by rw [hrot]; exact bv_b2left_0p173_1_5) (by rw [hrot]; exact bv_b2left_0p35_1_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_0p665_1_5 : (1.265738916932:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((665:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((665:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((665:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((665:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((665:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8956335005951 (-0.4447927973919) 0.00000012512 cs_b2left_v0p665_2 0.26447530528338 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((665:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7447893610818 (-0.6672996385578) 0.00000012822 cs_b2left_v0p665_3 0.29273851480381 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((665:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.6043187347765 (-0.7967426603352) 0.00000015022 cs_b2left_v0p665_4 0.28169101588096 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((665:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4798819279388 (-0.8773330811258) 0.0000001121 cs_b2left_v0p665_5 0.26238375719154 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((665:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4798819279388 (-0.8773330811258) 0.0000001121 cs_b2left_v0p665_5 0.504725 (by norm_num) (by norm_num) (-0.54987279836805) (-0.16445032377324) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.10128859315969:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((665:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_6 : mainRemConst 5 (1 - 1/4:ℝ) 0.430116 ≤ 43.46368343 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 0.430116 (by norm_num) _ 0.2990697562443 1.60943791291421 43.46368343 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_6 : ∀ y ∈ Set.Icc (((350:ℤ):ℝ)/1000) (((665:ℤ):ℝ)/1000), 0 < (I ^ ((1):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((1):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (1) (0) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((350:ℤ):ℝ)/1000) (((665:ℤ):ℝ)/1000) (I ^ ((1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.430116 0.35 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 43.46368343 rb_b2left_6 0.2990697562443 1.00236 1.872092 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.865039352766 1.265738916932 (by rw [hrot]; exact bv_b2left_0p35_1_5) (by rw [hrot]; exact bv_b2left_0p665_1_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_0p98_1_5 : (0.880209279089:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((980:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((980:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((980:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((980:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((980:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7780226095568 (-0.6282362764267) 0.0000001372 cs_b2left_v0p98_2 0.37355144333507 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((980:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4742890762771 (-0.8803691680904) 0.00000014315 cs_b2left_v0p98_3 0.38621026517743 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((980:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2106382642066 (-0.9775640754713) 0.00000012663 cs_b2left_v0p98_4 0.34562104863451 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((980:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0064528284228) (-0.9999791802858) 0.00000014634 cs_b2left_v0p98_5 0.29906348593148 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((980:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0064528284228) (-0.9999791802858) 0.00000014634 cs_b2left_v0p98_5 1.0229 (by norm_num) (by norm_num) 1.75289193589084 0.52423696398948 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.40444624307849:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((980:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_7 : mainRemConst 5 (1 - 1/4:ℝ) 0.71044 ≤ 17.04724778 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 0.71044 (by norm_num) _ 0.2990697562443 1.60943791291421 17.04724778 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_7 : ∀ y ∈ Set.Icc (((665:ℤ):ℝ)/1000) (((980:ℤ):ℝ)/1000), 0 < (I ^ ((1):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((1):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (1) (0) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((665:ℤ):ℝ)/1000) (((980:ℤ):ℝ)/1000) (I ^ ((1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 0.71044 0.665 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 17.04724778 rb_b2left_7 0.2990697562443 1.234059 2.005717 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.265738916932 0.880209279089 (by rw [hrot]; exact bv_b2left_0p665_1_5) (by rw [hrot]; exact bv_b2left_0p98_1_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_1p401_1_5 : (0.57794418102:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((1401:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((1401:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((1401:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((1401:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((1401:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5643924754579 (-0.8255065921278) 0.00000010041 cs_b2left_v1p401_2 0.49084909671582 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((1401:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.0316352477163 (-0.9994994802909) 0.00000011678 cs_b2left_v1p401_3 0.43847171275971 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((1401:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.362922267293) (-0.9318194180743) 0.00000010081 cs_b2left_v1p401_4 0.32944787903903 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((1401:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6319185616215) (-0.7750347937114) 0.00000011601 cs_b2left_v1p401_5 0.23178943214095 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((1401:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6319185616215) (-0.7750347937114) 0.00000011601 cs_b2left_v1p401_5 2.025301 (by norm_num) (by norm_num) 3.05150862158625 0.91261393963518 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.49055812065551:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((1401:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_8 : mainRemConst 5 (1 - 1/4:ℝ) 1.011385 ≤ 10.28463141 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 1.011385 (by norm_num) _ 0.2990697562443 1.60943791291421 10.28463141 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_8 : ∀ y ∈ Set.Icc (((980:ℤ):ℝ)/1000) (((1401:ℤ):ℝ)/1000), 0 < (I ^ ((1):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((1):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (1) (0) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((980:ℤ):ℝ)/1000) (((1401:ℤ):ℝ)/1000) (I ^ ((1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.011385 0.98 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 10.28463141 rb_b2left_8 0.2990697562443 1.58912 2.241719 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.880209279089 0.57794418102 (by rw [hrot]; exact bv_b2left_0p98_1_5) (by rw [hrot]; exact bv_b2left_1p401_1_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_1p822_1_5 : (0.389555492667:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((1822:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((1822:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((1822:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((1822:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((1822:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3030410320485 (-0.9529775091234) 0.00000013751 cs_b2left_v1p822_2 0.56664373537956 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((1822:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4176662360097) (-0.9086005256953) 0.00000011054 cs_b2left_v1p822_3 0.39859513151455 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((1822:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8163322080195) (-0.5775826573695) 0.00000012685 cs_b2left_v1p822_4 0.20420626201256 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((1822:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9781980437302) (-0.207674232704) 0.00000012451 cs_b2left_v1p822_5 0.06210904491581 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((1822:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9781980437302) (-0.207674232704) 0.00000012451 cs_b2left_v1p822_5 3.382184 (by norm_num) (by norm_num) 2.81539227412686 0.84199868115521 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.23155417382248:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((1822:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_9 : mainRemConst 5 (1 - 1/4:ℝ) 1.42313 ≤ 7.08548957 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 1.42313 (by norm_num) _ 0.2990697562443 1.60943791291421 7.08548957 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_9 : ∀ y ∈ Set.Icc (((1401:ℤ):ℝ)/1000) (((1822:ℤ):ℝ)/1000), 0 < (I ^ ((1):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((1):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (1) (0) 1 (by norm_num), rot1])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((1401:ℤ):ℝ)/1000) (((1822:ℤ):ℝ)/1000) (I ^ ((1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.42313 1.401 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 7.08548957 rb_b2left_9 0.2990697562443 1.970326 2.526299 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.57794418102 0.389555492667 (by rw [hrot]; exact bv_b2left_1p401_1_5) (by rw [hrot]; exact bv_b2left_1p822_1_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_1p822_0_5 : (0.502899709711:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((1822:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((1822:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((1822:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((1822:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((1822:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3030410320485 (-0.9529775091234) 0.00000013751 cs_b2left_v1p822_2 0.18018919396096 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((1822:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4176662360097) (-0.9086005256953) 0.00000011054 cs_b2left_v1p822_3 (-0.18322660825966) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((1822:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8163322080195) (-0.5775826573695) 0.00000012685 cs_b2left_v1p822_4 (-0.28861706484406) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((1822:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9781980437302) (-0.207674232704) 0.00000012451 cs_b2left_v1p822_5 (-0.29254948773422) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((1822:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9781980437302) (-0.207674232704) 0.00000012451 cs_b2left_v1p822_5 3.382184 (by norm_num) (by norm_num) (-0.29124869623167) (-0.08710367658844) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.41579603312302:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((1822:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_b2left_2p384_0_5 : (0.555079201298:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((2384:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((2384:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((2384:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((2384:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((2384:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0815758252346) (-0.9966671383852) 0.00000012218 cs_b2left_v2p384_2 (-0.04850534853927) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((2384:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8665737927836) (-0.4990489570927) 0.00000010445 cs_b2left_v2p384_3 (-0.38015846215077) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((2384:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9866907844083) 0.1626077968288 0.00000015089 cs_b2left_v2p384_4 (-0.34884792564239) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((2384:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7678568407469) 0.6406214733207 0.00000012519 cs_b2left_v2p384_5 (-0.22964279563324) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((2384:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7678568407469) 0.6406214733207 0.00000012519 cs_b2left_v2p384_5 5.745956 (by norm_num) (by norm_num) (-1.8799417912548) (-0.56223373326385) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : ((-0.00715453196567):ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((2384:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_10 : mainRemConst 5 (1 - 1/4:ℝ) 1.839071 ≤ 5.71478231 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 1.839071 (by norm_num) _ 0.2990697562443 1.60943791291421 5.71478231 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_10 : ∀ y ∈ Set.Icc (((1822:ℤ):ℝ)/1000) (((2384:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((1822:ℤ):ℝ)/1000) (((2384:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.839071 1.822 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 5.71478231 rb_b2left_10 0.2990697562443 2.499192 2.957357 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.502899709711 0.555079201298 (by rw [hrot]; exact bv_b2left_1p822_0_5) (by rw [hrot]; exact bv_b2left_2p384_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_2p946_0_5 : (0.59236662437:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((2946:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((2946:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((2946:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((2946:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((2946:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4539694497322) (-0.891017249387) 0.00000010685 cs_b2left_v2p946_2 (-0.26993191334111) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((2946:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9954985581415) 0.094776686232 0.00000010554 cs_b2left_v2p946_3 (-0.43671664040013) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((2946:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5878234716107) 0.8089892250286 0.00000012087 cs_b2left_v2p946_4 (-0.20782702419229) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((2946:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.0290110557688 0.9995790907392 0.0000001187 cs_b2left_v2p946_5 0.00867629387758 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((2946:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.0290110557688 0.9995790907392 0.0000001187 cs_b2left_v2p946_5 8.741416 (by norm_num) (by norm_num) (-1.66571810765112) (-0.49816590842677) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.09420071594405:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((2946:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_11 : mainRemConst 5 (1 - 1/4:ℝ) 2.397072 ≤ 4.79993299 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 2.397072 (by norm_num) _ 0.2990697562443 1.60943791291421 4.79993299 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_11 : ∀ y ∈ Set.Icc (((2384:ℤ):ℝ)/1000) (((2946:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((2384:ℤ):ℝ)/1000) (((2946:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 2.397072 2.384 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 4.79993299 rb_b2left_11 0.2990697562443 3.03997 3.426575 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.555079201298 0.59236662437 (by rw [hrot]; exact bv_b2left_2p384_0_5) (by rw [hrot]; exact bv_b2left_2p946_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_3p508_0_5 : (0.618404392084:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((3508:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((3508:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((3508:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((3508:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((3508:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7583407864249) (-0.6518583063891) 0.00000011026 cs_b2left_v3p508_2 (-0.45091219496765) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((3508:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7568349979683) 0.6536059866729 0.00000010233 cs_b2left_v3p508_3 (-0.33201700253102) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((3508:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1501615038282 0.9886614803703 0.00000011333 cs_b2left_v3p508_4 0.05309006874682 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((3508:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8037188859011 0.5950092036648 0.0000001122 cs_b2left_v3p508_5 0.24036797773967 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((3508:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8037188859011 0.5950092036648 0.0000001122 cs_b2left_v3p508_5 12.368564 (by norm_num) (by norm_num) (-0.36070361795043) (-0.10787554309683) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.51052884898782:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((3508:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_12 : mainRemConst 5 (1 - 1/4:ℝ) 2.956588 ≤ 4.29990081 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 2.956588 (by norm_num) _ 0.2990697562443 1.60943791291421 4.29990081 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_12 : ∀ y ∈ Set.Icc (((2946:ℤ):ℝ)/1000) (((3508:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((2946:ℤ):ℝ)/1000) (((3508:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 2.956588 2.946 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 4.29990081 rb_b2left_12 0.2990697562443 3.587279 3.920277 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.59236662437 0.618404392084 (by rw [hrot]; exact bv_b2left_2p946_0_5) (by rw [hrot]; exact bv_b2left_3p508_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_4p07_0_5 : (0.640220938674:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((4070:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((4070:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((4070:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((4070:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((4070:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9490831657479) (-0.3150256248196) 0.00000012587 cs_b2left_v4p07_2 (-0.56432830156115) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((4070:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.2387097498973) 0.9710909613949 0.00000010869 cs_b2left_v4p07_3 (-0.10471994717412) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((4070:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8015177155758 0.5979710290793 0.00000014455 cs_b2left_v4p07_4 0.28337925485619 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((4070:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9645068362222 (-0.2640578778994) 0.0000001057 cs_b2left_v4p07_5 0.28845479279316 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((4070:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9645068362222 (-0.2640578778994) 0.0000001057 cs_b2left_v4p07_5 16.6274 (by norm_num) (by norm_num) 0.87793852356407 0.26256486023979 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.90278579891408:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((4070:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_13 : mainRemConst 5 (1 - 1/4:ℝ) 3.516896 ≤ 3.98695843 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 3.516896 (by norm_num) _ 0.2990697562443 1.60943791291421 3.98695843 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_13 : ∀ y ∈ Set.Icc (((3508:ℤ):ℝ)/1000) (((4070:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((3508:ℤ):ℝ)/1000) (((4070:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 3.516896 3.508 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.98695843 rb_b2left_13 0.2990697562443 4.138527 4.430283 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.618404392084 0.640220938674 (by rw [hrot]; exact bv_b2left_3p508_0_5) (by rw [hrot]; exact bv_b2left_4p07_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_4p632_0_5 : (0.672997418021:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((4632:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((4632:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((4632:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((4632:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((4632:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9976159568152) 0.0690101599304 0.0000001343 cs_b2left_v4p632_2 (-0.59318607679774) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((4632:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3675591883535 0.9300001306757 0.00000011506 cs_b2left_v4p632_3 0.16124498152881 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((4632:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.990475182804 (-0.1376913659215) 0.0000001289 cs_b2left_v4p632_4 0.35018581360574 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((4632:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3885571891595 (-0.9214246093699) 0.00000010545 cs_b2left_v4p632_5 0.11620567231195 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((4632:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3885571891595 (-0.9214246093699) 0.00000010545 cs_b2left_v4p632_5 21.517924 (by norm_num) (by norm_num) 1.20859085574507 0.36145297262677 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.03445039064876:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((4632:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_14 : mainRemConst 5 (1 - 1/4:ℝ) 4.07767 ≤ 3.77333504 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 4.07767 (by norm_num) _ 0.2990697562443 1.60943791291421 3.77333504 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_14 : ∀ y ∈ Set.Icc (((4070:ℤ):ℝ)/1000) (((4632:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((4070:ℤ):ℝ)/1000) (((4632:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 4.07767 4.07 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.77333504 rb_b2left_14 0.2990697562443 4.692327 4.951558 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.640220938674 0.672997418021 (by rw [hrot]; exact bv_b2left_4p07_0_5) (by rw [hrot]; exact bv_b2left_4p632_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_5p194_0_5 : (0.73244912728:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((5194:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((5194:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((5194:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((5194:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((5194:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8966670578027) 0.4427055311815 0.00000014991 cs_b2left_v5p194_2 (-0.53316151160082) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((5194:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8381067191938 0.545506303577 0.00000012142 cs_b2left_v5p194_3 0.36767010447134 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((5194:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.6080235515228 (-0.7939189888104) 0.00000010699 cs_b2left_v5p194_4 0.21496875037472 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((5194:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4841914843452) (-0.8749620600243) 0.00000011251 cs_b2left_v5p194_5 (-0.14480706284703) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((5194:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4841914843452) (-0.8749620600243) 0.00000011251 cs_b2left_v5p194_5 27.040136 (by norm_num) (by norm_num) 0.57585613229522 0.17222115311732 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.90467028039821:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((5194:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_15 : mainRemConst 5 (1 - 1/4:ℝ) 4.638741 ≤ 3.61847097 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 4.638741 (by norm_num) _ 0.2990697562443 1.60943791291421 3.61847097 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_15 : ∀ y ∈ Set.Icc (((4632:ℤ):ℝ)/1000) (((5194:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((4632:ℤ):ℝ)/1000) (((5194:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 4.638741 4.632 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.61847097 rb_b2left_15 0.2990697562443 5.24787 5.480889 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.672997418021 0.73244912728 (by rw [hrot]; exact bv_b2left_4p632_0_5) (by rw [hrot]; exact bv_b2left_5p194_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_5p756_0_5 : (0.8228020831:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((5756:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((5756:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((5756:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((5756:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((5756:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6613624684694) 0.7500664539105 0.00000013739 cs_b2left_v5p756_2 (-0.3932485582424) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((5756:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9991829401242 (-0.0404159889736) 0.00000012779 cs_b2left_v5p756_3 0.43833284450057 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((5756:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1251992642587) (-0.9921316163839) 0.00000013821 cs_b2left_v5p756_4 (-0.04426467324307) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((5756:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9870909690115) (-0.160160602266) 0.00000011957 cs_b2left_v5p756_5 (-0.29520909125299) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((5756:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9870909690115) (-0.160160602266) 0.00000011957 cs_b2left_v5p756_5 33.194036 (by norm_num) (by norm_num) (-0.39185360235126) (-0.1171915613386) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.70561052176211:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((5756:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_16 : mainRemConst 5 (1 - 1/4:ℝ) 5.200013 ≤ 3.5011554 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 5.200013 (by norm_num) _ 0.2990697562443 1.60943791291421 3.5011554 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_16 : ∀ y ∈ Set.Icc (((5194:ℤ):ℝ)/1000) (((5756:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((5194:ℤ):ℝ)/1000) (((5756:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 5.200013 5.194 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.5011554 rb_b2left_16 0.2990697562443 5.804657 6.016148 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.73244912728 0.8228020831 (by rw [hrot]; exact bv_b2left_5p194_0_5) (by rw [hrot]; exact bv_b2left_5p756_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_6p318_0_5 : (0.931569133717:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((6318:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((6318:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((6318:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((6318:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((6318:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.326960091583) 0.9450381465899 0.00000012206 cs_b2left_v6p318_2 (-0.19441170619355) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((6318:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7913103789505 (-0.6114146581209) 0.00000013416 cs_b2left_v6p318_3 0.34714094978392 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((6318:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7861941925788) (-0.6179795235371) 0.00000013692 cs_b2left_v6p318_4 (-0.27796167085953) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((6318:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7360019840293) 0.6769793789137 0.00000011945 cs_b2left_v6p318_5 (-0.22011596968285) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((6318:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7360019840293) 0.6769793789137 0.00000011945 cs_b2left_v6p318_5 39.979624 (by norm_num) (by norm_num) (-0.92592956956703) (-0.2769175306697) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.65465160304799:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((6318:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_17 : mainRemConst 5 (1 - 1/4:ℝ) 5.761426 ≤ 3.40925541 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 5.761426 (by norm_num) _ 0.2990697562443 1.60943791291421 3.40925541 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_17 : ∀ y ∈ Set.Icc (((5756:ℤ):ℝ)/1000) (((6318:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((5756:ℤ):ℝ)/1000) (((6318:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 5.761426 5.756 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.40925541 rb_b2left_17 0.2990697562443 6.36236 6.555885 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.8228020831 0.931569133717 (by rw [hrot]; exact bv_b2left_5p756_0_5) (by rw [hrot]; exact bv_b2left_6p318_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_6p88_0_5 : (1.037379248298:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((6880:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((6880:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((6880:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((6880:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((6880:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.0564336292417 0.9984063528897 0.00000010673 cs_b2left_v6p88_2 0.03355557324778 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((6880:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.291246079051 (-0.9566481701427) 0.00000014052 cs_b2left_v6p88_3 0.12776707035952 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((6880:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9936304907775) 0.1126873876884 0.00000011345 cs_b2left_v6p88_4 (-0.35130146912191) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((6880:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.0772813932356 0.9970093210494 0.00000012651 cs_b2left_v6p88_5 0.02311248960186 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((6880:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.0772813932356 0.9970093210494 0.00000012651 cs_b2left_v6p88_5 47.3969 (by norm_num) (by norm_num) (-0.68293627137762) (-0.20424558421122) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.83313366408725:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((6880:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_18 : mainRemConst 5 (1 - 1/4:ℝ) 6.322944 ≤ 3.33534185 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 6.322944 (by norm_num) _ 0.2990697562443 1.60943791291421 3.33534185 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_18 : ∀ y ∈ Set.Icc (((6318:ℤ):ℝ)/1000) (((6880:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((6318:ℤ):ℝ)/1000) (((6880:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 6.322944 6.318 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.33534185 rb_b2left_18 0.2990697562443 6.920759 7.099078 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.931569133717 1.037379248298 (by rw [hrot]; exact bv_b2left_6p318_0_5) (by rw [hrot]; exact bv_b2left_6p88_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_7p442_0_5 : (1.12596034931:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((7442:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((7442:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((7442:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((7442:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((7442:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.431371396539 0.9021744389241 0.00000011235 cs_b2left_v7p442_2 0.25649490018268 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((7442:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3163609758772) (-0.9486388843707) 0.00000014689 cs_b2left_v7p442_3 (-0.13878488412749) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((7442:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6278374364947) 0.7783444952727 0.00000012468 cs_b2left_v7p442_4 (-0.22197409849515) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((7442:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8315334543585 0.5554746747445 0.00000013356 cs_b2left_v7p442_5 0.24868646756013 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((7442:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8315334543585 0.5554746747445 0.00000013356 cs_b2left_v7p442_5 55.445864 (by norm_num) (by norm_num) 0.0617315372884 0.01846203580943 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.14442238512017:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((7442:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_19 : mainRemConst 5 (1 - 1/4:ℝ) 6.88454 ≤ 3.27461733 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 6.88454 (by norm_num) _ 0.2990697562443 1.60943791291421 3.27461733 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_19 : ∀ y ∈ Set.Icc (((6880:ℤ):ℝ)/1000) (((7442:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((6880:ℤ):ℝ)/1000) (((7442:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 6.88454 6.88 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.27461733 rb_b2left_19 0.2990697562443 7.479697 7.64499 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.037379248298 1.12596034931 (by rw [hrot]; exact bv_b2left_6p88_0_5) (by rw [hrot]; exact bv_b2left_7p442_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_8p004_0_5 : (1.201004354376:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((8004:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((8004:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((8004:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((8004:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((8004:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7416729437099 0.6707616898487 0.00000012796 cs_b2left_v8p004_2 0.44100129474689 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((8004:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8071516470453) (-0.590344152694) 0.00000015078 cs_b2left_v8p004_3 (-0.35409050187531) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((8004:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1001576103598 0.99497158406 0.00000015213 cs_b2left_v8p004_4 0.03541100895034 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((8004:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9506195049347 (-0.3103587550524) 0.00000014062 cs_b2left_v8p004_5 0.28430150156661 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((8004:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9506195049347 (-0.3103587550524) 0.00000014062 cs_b2left_v8p004_5 64.126516 (by norm_num) (by norm_num) 0.68752839335669 0.20561894901223 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.40662330338853:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((8004:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_20 : mainRemConst 5 (1 - 1/4:ℝ) 7.446197 ≤ 3.22384762 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 7.446197 (by norm_num) _ 0.2990697562443 1.60943791291421 3.22384762 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_20 : ∀ y ∈ Set.Icc (((7442:ℤ):ℝ)/1000) (((8004:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((7442:ℤ):ℝ)/1000) (((8004:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 7.446197 7.442 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.22384762 rb_b2left_20 0.2990697562443 8.039062 8.193078 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.12596034931 1.201004354376 (by rw [hrot]; exact bv_b2left_7p442_0_5) (by rw [hrot]; exact bv_b2left_8p004_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_8p566_0_5 : (1.278973789499:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((8566:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((8566:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((8566:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((8566:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((8566:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9408430249655 0.3388427398865 0.00000014357 cs_b2left_v8p566_2 0.55942852432753 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((8566:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9999010884417) (-0.014064589564) 0.00000014469 cs_b2left_v8p566_3 (-0.43864800948133) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((8566:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.770371259012 0.6375955797277 0.00000012147 cs_b2left_v8p566_4 0.27236732769311 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((8566:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3435757824604 (-0.939124955321) 0.00000014768 cs_b2left_v8p566_5 0.10275308134522 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((8566:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3435757824604 (-0.939124955321) 0.00000014768 cs_b2left_v8p566_5 73.438856 (by norm_num) (by norm_num) 0.72533959003299 0.21692713438551 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.49590092388453:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((8566:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_21 : mainRemConst 5 (1 - 1/4:ℝ) 8.007903 ≤ 3.18077421 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 8.007903 (by norm_num) _ 0.2990697562443 1.60943791291421 3.18077421 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_21 : ∀ y ∈ Set.Icc (((8004:ℤ):ℝ)/1000) (((8566:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((8004:ℤ):ℝ)/1000) (((8566:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 8.007903 8.004 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.18077421 rb_b2left_21 0.2990697562443 8.598771 8.742932 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.201004354376 1.278973789499 (by rw [hrot]; exact bv_b2left_8p004_0_5) (by rw [hrot]; exact bv_b2left_8p566_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_9p128_0_5 : (1.369475773284:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((9128:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((9128:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((9128:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((9128:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((9128:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9990382079191 (-0.0438481369926) 0.00000014542 cs_b2left_v9p128_2 0.59403158604117 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((9128:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.82343656755) 0.5674083354713 0.00000014578 cs_b2left_v9p128_3 (-0.3612345532416) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((9128:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9961546905257 (-0.0876118287879) 0.00000011834 cs_b2left_v9p128_4 0.35219382655117 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((9128:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5259080482827) (-0.8505414303513) 0.00000015442 cs_b2left_v9p128_5 (-0.15728323798918) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((9128:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5259080482827) (-0.8505414303513) 0.00000015442 cs_b2left_v9p128_5 83.382884 (by norm_num) (by norm_num) 0.19470991921214 0.05823184807713 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.42770762136156:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((9128:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_22 : mainRemConst 5 (1 - 1/4:ℝ) 8.569647 ≤ 3.14377287 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 8.569647 (by norm_num) _ 0.2990697562443 1.60943791291421 3.14377287 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_22 : ∀ y ∈ Set.Icc (((8566:ℤ):ℝ)/1000) (((9128:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((8566:ℤ):ℝ)/1000) (((9128:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 8.569647 8.566 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.14377287 rb_b2left_22 0.2990697562443 9.15876 9.29424 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.278973789499 1.369475773284 (by rw [hrot]; exact bv_b2left_8p566_0_5) (by rw [hrot]; exact bv_b2left_9p128_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_9p69_0_5 : (1.456078590634:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((9690:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((9690:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((9690:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((9690:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((9690:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9075385602548 (-0.4199687627081) 0.00000013009 cs_b2left_v9p69_2 0.53962557914513 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((9690:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3429176969098) 0.93936545239 0.0000001397 cs_b2left_v9p69_3 (-0.15043508444671) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((9690:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.6472525529264 (-0.762275627795) 0.00000014956 cs_b2left_v9p69_4 0.22883828177978 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((9690:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9936774399349) (-0.1122726365168) 0.00000014793 cs_b2left_v9p69_5 (-0.29717891398818) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((9690:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9936774399349) (-0.1122726365168) 0.00000014793 cs_b2left_v9p69_5 93.9586 (by norm_num) (by norm_num) (-0.45216450450352) (-0.13522872814414) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.32084986249002:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((9690:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_23 : mainRemConst 5 (1 - 1/4:ℝ) 9.131422 ≤ 3.11164571 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 9.131422 (by norm_num) _ 0.2990697562443 1.60943791291421 3.11164571 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_23 : ∀ y ∈ Set.Icc (((9128:ℤ):ℝ)/1000) (((9690:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((9128:ℤ):ℝ)/1000) (((9690:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 9.131422 9.128 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.11164571 rb_b2left_23 0.2990697562443 9.718982 9.846756 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.369475773284 1.456078590634 (by rw [hrot]; exact bv_b2left_9p128_0_5) (by rw [hrot]; exact bv_b2left_9p69_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_10p252_0_5 : (1.494954106095:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((10252:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((10252:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((10252:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((10252:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((10252:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.6800543233842 (-0.7331617265287) 0.00000011476 cs_b2left_v10p252_2 0.40436265174168 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((10252:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.264223698565 0.9644614233429 0.00000013361 cs_b2left_v10p252_3 0.11591258914897 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((10252:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.075052234493) (-0.9971796037311) 0.0000001295 cs_b2left_v10p252_4 (-0.02653501776177) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((10252:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7024272924118) 0.7117555049671 0.00000014861 cs_b2left_v10p252_5 (-0.2100748035657) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((10252:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7024272924118) 0.7117555049671 0.00000014861 cs_b2left_v10p252_5 105.166004 (by norm_num) (by norm_num) (-0.70648630334952) (-0.2112886865326) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.28366541956318:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((10252:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_24 : mainRemConst 5 (1 - 1/4:ℝ) 9.693224 ≤ 3.08349006 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 9.693224 (by norm_num) _ 0.2990697562443 1.60943791291421 3.08349006 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_24 : ∀ y ∈ Set.Icc (((9690:ℤ):ℝ)/1000) (((10252:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((9690:ℤ):ℝ)/1000) (((10252:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 9.693224 9.69 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.08349006 rb_b2left_24 0.2990697562443 10.279398 10.400289 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.456078590634 1.494954106095 (by rw [hrot]; exact bv_b2left_9p69_0_5) (by rw [hrot]; exact bv_b2left_10p252_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_10p814_0_5 : (1.436831128726:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((10814:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((10814:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((10814:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((10814:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((10814:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3506714875411 (-0.9364985359442) 0.00000010601 cs_b2left_v10p814_2 0.20851045097228 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((10814:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7738003660265 0.6334295489928 0.00000012753 cs_b2left_v10p814_3 0.33945946170053 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((10814:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7540590156454) (-0.6568066693396) 0.000000112 cs_b2left_v10p814_4 (-0.26660016128686) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((10814:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1253712519538 0.9921098977349 0.00000014211 cs_b2left_v10p814_5 0.03749470726105 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((10814:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1253712519538 0.9921098977349 0.00000014211 cs_b2left_v10p814_5 117.005096 (by norm_num) (by norm_num) (-0.39444533462896) (-0.11796667007914) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.318864458647:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((10814:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_25 : mainRemConst 5 (1 - 1/4:ℝ) 10.255047 ≤ 3.0586131 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 10.255047 (by norm_num) _ 0.2990697562443 1.60943791291421 3.0586131 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_25 : ∀ y ∈ Set.Icc (((10252:ℤ):ℝ)/1000) (((10814:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((10252:ℤ):ℝ)/1000) (((10814:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 10.255047 10.252 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.0586131 rb_b2left_25 0.2990697562443 10.839977 10.954684 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.494954106095 1.436831128726 (by rw [hrot]; exact bv_b2left_10p252_0_5) (by rw [hrot]; exact bv_b2left_10p814_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_11p376_0_5 : (1.259565481027:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((11376:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((11376:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((11376:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((11376:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((11376:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0312555819776) (-0.9995114249447) 0.00000012162 cs_b2left_v11p376_2 (-0.01858475255135) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((11376:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9976508754717 0.0685035084547 0.00000012144 cs_b2left_v11p376_3 0.43766074379449 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((11376:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9980461764836) 0.0624806294732 0.00000013604 cs_b2left_v11p376_4 (-0.35286265776186) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((11376:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8574050889337 0.5146421217414 0.00000013562 cs_b2left_v11p376_5 0.25642389039009 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((11376:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8574050889337 0.5146421217414 0.00000013562 cs_b2left_v11p376_5 129.475876 (by norm_num) (by norm_num) 0.21089308272485 0.06307174284413 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.32263722387137:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((11376:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_26 : mainRemConst 5 (1 - 1/4:ℝ) 10.816889 ≤ 3.03647405 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 10.816889 (by norm_num) _ 0.2990697562443 1.60943791291421 3.03647405 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_26 : ∀ y ∈ Set.Icc (((10814:ℤ):ℝ)/1000) (((11376:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((10814:ℤ):ℝ)/1000) (((11376:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 10.816889 10.814 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.03647405 rb_b2left_26 0.2990697562443 11.400697 11.509817 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.436831128726 1.259565481027 (by rw [hrot]; exact bv_b2left_10p814_0_5) (by rw [hrot]; exact bv_b2left_11p376_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_11p938_0_5 : (0.988529995727:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((11938:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((11938:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((11938:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((11938:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((11938:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4084993491423) (-0.9127586108862) 0.00000013723 cs_b2left_v11p938_2 (-0.24289524783447) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((11938:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8531183184239 (-0.5217174855892) 0.00000011536 cs_b2left_v11p938_3 0.37425556567634 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((11938:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6662564835724) 0.7457226683419 0.00000014471 cs_b2left_v11p938_4 (-0.23555728993451) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((11938:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9345108927649 (-0.3559345323283) 0.00000012912 cs_b2left_v11p938_5 0.27948390629086 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((11938:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9345108927649 (-0.3559345323283) 0.00000012912 cs_b2left_v11p938_5 142.578344 (by norm_num) (by norm_num) 0.62445945994614 0.18675693847054 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.17528693419822:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((11938:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_27 : mainRemConst 5 (1 - 1/4:ℝ) 11.378746 ≤ 3.01664484 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 11.378746 (by norm_num) _ 0.2990697562443 1.60943791291421 3.01664484 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_27 : ∀ y ∈ Set.Icc (((11376:ℤ):ℝ)/1000) (((11938:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((11376:ℤ):ℝ)/1000) (((11938:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 11.378746 11.376 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 3.01664484 rb_b2left_27 0.2990697562443 11.961537 12.065586 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.259565481027 0.988529995727 (by rw [hrot]; exact bv_b2left_11p376_0_5) (by rw [hrot]; exact bv_b2left_11p938_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_12p359_0_5 : (0.762645481616:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((12359:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((12359:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((12359:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6538217486249) (-0.7566486113169) 0.00000010587 cs_b2left_v12p359_2 (-0.38876480065484) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5306926891961 (-0.8475643159276) 0.00000014194 cs_b2left_v12p359_3 0.23281022343708 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1450342349418) 0.9894266373482 0.0000001189 cs_b2left_v12p359_4 (-0.05127738755328) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5049371303191 (-0.8631561240153) 0.00000014418 cs_b2left_v12p359_5 0.1510113813633 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5049371303191 (-0.8631561240153) 0.00000014418 cs_b2left_v12p359_5 152.807381 (by norm_num) (by norm_num) 0.60565781458551 0.18113393497555 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.94377941659226:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((12359:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_b2left_28 : mainRemConst 5 (1 - 1/4:ℝ) 11.940617 ≤ 2.99878211 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (1 - 1/4:ℝ) 11.940617 (by norm_num) _ 0.2990697562443 1.60943791291421 2.99878211 c5 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_b2left_28 : ∀ y ∈ Set.Icc (((11938:ℤ):ℝ)/1000) (((12359:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (1 - 1/4:ℝ) (((11938:ℤ):ℝ)/1000) (((12359:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 11.940617 11.938 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 2.99878211 rb_b2left_28 0.2990697562443 12.381736 12.482283 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.988529995727 0.762645481616 (by rw [hrot]; exact bv_b2left_11p938_0_5) (by rw [hrot]; exact bv_b2left_12p359_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_12p359_0_10 : (0.82976924815:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((12359:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((12359:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((12359:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6538217486249) (-0.7566486113169) 0.00000010587 cs_b2left_v12p359_2 (-0.38876480065484) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5306926891961 (-0.8475643159276) 0.00000014194 cs_b2left_v12p359_3 0.23281022343708 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1450342349418) 0.9894266373482 0.0000001189 cs_b2left_v12p359_4 (-0.05127738755328) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5049371303191 (-0.8631561240153) 0.00000014418 cs_b2left_v12p359_5 0.1510113813633 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9882867834269) 0.1526081036992 0.00000015497 cs_b2left_v12p359_6 (-0.25779210799556) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4684703839762 0.8834792014174 0.0000001094 cs_b2left_v12p359_7 0.10885753835394 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8434748282598 (-0.5371687017056) 0.00000012475 cs_b2left_v12p359_8 0.17731871363462 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4367304493085) (-0.8995924158432) 0.00000012853 cs_b2left_v12p359_9 (-0.08404883889282) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9832447586327) 0.1822902747675 0.00000013733 cs_b2left_v12p359_10 (-0.17484841535165) (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9832447586327) 0.1822902747675 0.00000013733 cs_b2left_v12p359_10 152.807381 (by norm_num) (by norm_num) (-0.65514418685677) (-0.11650294180934) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.71326630634079:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((12359:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma bv_b2left_12p78_0_10 : (0.640356930427:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((12780:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((12780:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((12780:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((12780:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((12780:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8438612886358) (-0.5365613902173) 0.00000014296 cs_b2left_v12p78_2 (-0.50176300926509) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((12780:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.0967503467315 (-0.9953086809665) 0.0000001379 cs_b2left_v12p78_3 0.04244347853028 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((12780:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4242036649179 0.9055668118202 0.00000011972 cs_b2left_v12p78_4 0.14997860170637 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((12780:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1477216717718) (-0.9890289721178) 0.00000010729 cs_b2left_v12p78_5 (-0.04417911645599) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((12780:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6156880762052) 0.7879899699903 0.00000011864 cs_b2left_v12p78_6 (-0.16060068331429) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((12780:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9653514485476 0.2609532157054 0.00000013045 cs_b2left_v12p78_7 0.2243168325459 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((12780:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1279231361912 (-0.9917840849837) 0.00000013603 cs_b2left_v12p78_8 0.026892498066 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((12780:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9812787599366) (-0.1925928216848) 0.00000013702 cs_b2left_v12p78_9 (-0.18884721176936) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((12780:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4060181534189) 0.9138650114163 0.00000015742 cs_b2left_v12p78_10 (-0.07220140022637) (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1 - 1/4:ℝ) (((12780:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4060181534189) 0.9138650114163 0.00000015742 cs_b2left_v12p78_10 163.3909 (by norm_num) (by norm_num) (-0.9240220613385) (-0.16431694060991) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.47603998981745:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((12780:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma rb_b2left_29 : mainRemConst 10 (1 - 1/4:ℝ) 12.361528 ≤ 8.02942061 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  exact mainRemConst_le 10 (by norm_num) (1 - 1/4:ℝ) 12.361528 (by norm_num) _ 0.1778279410039 2.30258509371421 8.02942061 c10 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 (by norm_num)
lemma pc_b2left_29 : ∀ y ∈ Set.Icc (((12359:ℤ):ℝ)/1000) (((12780:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 10 (by norm_num) (1 - 1/4:ℝ) (((12359:ℤ):ℝ)/1000) (((12780:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.30258509371421 (lg_10).2 (by norm_num) 12.361528 12.359 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 8.02942061 rb_b2left_29 0.1778279410039 12.801989 12.89926 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.82976924815 0.640356930427 (by rw [hrot]; exact bv_b2left_12p359_0_10) (by rw [hrot]; exact bv_b2left_12p78_0_10) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_13p095_0_10 : (0.495328111395:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13095:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13095:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((13095:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.940051290922) (-0.3410330926119) 0.00000012541 cs_b2left_v13p095_2 (-0.55895791638524) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.2465909287843) (-0.969119659196) 0.00000010891 cs_b2left_v13p095_3 (-0.10817735217884) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7673928639622 0.641177192623 0.00000014363 cs_b2left_v13p095_4 0.27131429818998 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6093473159126) (-0.7929034295406) 0.00000014809 cs_b2left_v13p095_5 (-0.18223739752734) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0986937464851) 0.99511785453 0.00000012713 cs_b2left_v13p095_6 (-0.02574404329046) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9397314854428 (-0.3419133446759) 0.00000013366 cs_b2left_v13p095_7 0.21836357015745 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5027260979308) (-0.8644457591156) 0.00000015065 cs_b2left_v13p095_8 (-0.10568517507143) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8783858242254) 0.4779522399833 0.00000011062 cs_b2left_v13p095_9 (-0.16904545197848) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3024115243471 0.9531774598374 0.00000015337 cs_b2left_v13p095_10 0.05377719143699 (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3024115243471 0.9531774598374 0.00000015337 cs_b2left_v13p095_10 171.541525 (by norm_num) (by norm_num) (-0.57201577810919) (-0.10172038804284) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.39360772335263:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13095:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma rb_b2left_30 : mainRemConst 10 (1 - 1/4:ℝ) 12.782444 ≤ 8.00247951 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  exact mainRemConst_le 10 (by norm_num) (1 - 1/4:ℝ) 12.782444 (by norm_num) _ 0.1778279410039 2.30258509371421 8.00247951 c10 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 (by norm_num)
lemma pc_b2left_30 : ∀ y ∈ Set.Icc (((12780:ℤ):ℝ)/1000) (((13095:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 10 (by norm_num) (1 - 1/4:ℝ) (((12780:ℤ):ℝ)/1000) (((13095:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.30258509371421 (lg_10).2 (by norm_num) 12.782444 12.78 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 8.00247951 rb_b2left_30 0.1778279410039 13.116461 13.211417 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.640356930427 0.495328111395 (by rw [hrot]; exact bv_b2left_12p78_0_10) (by rw [hrot]; exact bv_b2left_13p095_0_10) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_13p095_1_10 : (0.506759255965:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13095:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13095:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((13095:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.940051290922) (-0.3410330926119) 0.00000012541 cs_b2left_v13p095_2 0.20277941552347 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.2465909287843) (-0.969119659196) 0.00000010891 cs_b2left_v13p095_3 0.4251443518585 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7673928639622 0.641177192623 0.00000014363 cs_b2left_v13p095_4 (-0.22669042120383) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6093473159126) (-0.7929034295406) 0.00000014809 cs_b2left_v13p095_5 0.23713339110865 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0986937464851) 0.99511785453 0.00000012713 cs_b2left_v13p095_6 (-0.25957396807504) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9397314854428 (-0.3419133446759) 0.00000013366 cs_b2left_v13p095_7 0.07944971645331 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5027260979308) (-0.8644457591156) 0.00000015065 cs_b2left_v13p095_8 0.18172730333511 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8783858242254) 0.4779522399833 0.00000011062 cs_b2left_v13p095_9 (-0.09198197276023) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3024115243471 0.9531774598374 0.00000015337 cs_b2left_v13p095_10 (-0.16950161236769) (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3024115243471 0.9531774598374 0.00000015337 cs_b2left_v13p095_10 171.541525 (by norm_num) (by norm_num) (-0.72133238100235) (-0.12827305209301) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.37848620387225:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13095:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma bv_b2left_13p41_1_10 : (0.396354036513:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13410:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13410:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((13410:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.991604068775) (-0.1293111378168) 0.00000011937 cs_b2left_v13p41_2 0.07688879159258 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5606941407093) (-0.8280229951909) 0.00000012682 cs_b2left_v13p41_3 0.36324645973108 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.966557261009 0.2564508943067 0.00000014591 cs_b2left_v13p41_4 (-0.0906691347898) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.917683478308) (-0.3973122619566) 0.00000012278 cs_b2left_v13p41_5 0.1188240446164 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4489140019713 0.8935749654249 0.00000015336 cs_b2left_v13p41_6 (-0.23308677325798) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5719510858817 (-0.8202877271779) 0.00000013687 cs_b2left_v13p41_7 0.19060865260659 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9252801179358) (-0.3792844621142) 0.00000015488 cs_b2left_v13p41_8 0.07973470357879 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3712442473345) 0.9285352490984 0.00000015263 cs_b2left_v13p41_9 (-0.17869672138002) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8586017740816 0.5126431444425 0.00000014932 cs_b2left_v13p41_10 (-0.09116230139925) (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8586017740816 0.5126431444425 0.00000014932 cs_b2left_v13p41_10 179.8906 (by norm_num) (by norm_num) (-0.90349308611749) (-0.16066631521544) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.23568772129839:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13410:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma rb_b2left_31 : mainRemConst 10 (1 - 1/4:ℝ) 13.097386 ≤ 7.98349251 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  exact mainRemConst_le 10 (by norm_num) (1 - 1/4:ℝ) 13.097386 (by norm_num) _ 0.1778279410039 2.30258509371421 7.98349251 c10 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 (by norm_num)
lemma pc_b2left_31 : ∀ y ∈ Set.Icc (((13095:ℤ):ℝ)/1000) (((13410:ℤ):ℝ)/1000), 0 < (I ^ ((1):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((1):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (1) (0) 1 (by norm_num), rot1])
  refine vertical_piece 10 (by norm_num) (1 - 1/4:ℝ) (((13095:ℤ):ℝ)/1000) (((13410:ℤ):ℝ)/1000) (I ^ ((1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.30258509371421 (lg_10).2 (by norm_num) 13.097386 13.095 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 7.98349251 rb_b2left_31 0.1778279410039 13.430957 13.523706 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.506759255965 0.396354036513 (by rw [hrot]; exact bv_b2left_13p095_1_10) (by rw [hrot]; exact bv_b2left_13p41_1_10) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_13p41_1_15 : (0.380514915673:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13410:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13410:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((13410:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.991604068775) (-0.1293111378168) 0.00000011937 cs_b2left_v13p41_2 0.07688879159258 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5606941407093) (-0.8280229951909) 0.00000012682 cs_b2left_v13p41_3 0.36324645973108 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.966557261009 0.2564508943067 0.00000014591 cs_b2left_v13p41_4 (-0.0906691347898) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.917683478308) (-0.3973122619566) 0.00000012278 cs_b2left_v13p41_5 0.1188240446164 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4489140019713 0.8935749654249 0.00000015336 cs_b2left_v13p41_6 (-0.23308677325798) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5719510858817 (-0.8202877271779) 0.00000013687 cs_b2left_v13p41_7 0.19060865260659 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9252801179358) (-0.3792844621142) 0.00000015488 cs_b2left_v13p41_8 0.07973470357879 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3712442473345) 0.9285352490984 0.00000015263 cs_b2left_v13p41_9 (-0.17869672138002) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8586017740816 0.5126431444425 0.00000014932 cs_b2left_v13p41_10 (-0.09116230139925) (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7385703003673 (-0.674176469046) 0.00000013814 cs_b2left_v13p41_11 0.11161665092468 (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3295956608716) (-0.9441221850653) 0.00000014743 cs_b2left_v13p41_12 0.14643409263475 (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9869794190075) (-0.160846591754) 0.00000015733 cs_b2left_v13p41_13 0.02349383551564 (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6732214321464) 0.7394409396828 0.00000015674 cs_b2left_v13p41_14 (-0.1021662745324) (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1855560671578 0.9826336784076 0.00000015677 cs_b2left_v13p41_15 (-0.12892088255104) (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1855560671578 0.9826336784076 0.00000015677 cs_b2left_v13p41_15 179.8906 (by norm_num) (by norm_num) (-0.7192855767583) (-0.0943697723833) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.28614514329002:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13410:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma bv_b2left_13p646_1_15 : (0.27144797944:ℝ) ≤ ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13646:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13646:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((13646:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9994251631741) 0.033901955793 0.00000011485 cs_b2left_v13p646_2 (-0.020158291811) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7542403312231) (-0.6565984486134) 0.00000012676 cs_b2left_v13p646_3 0.28804399611313 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.997701315236 (-0.0677649288076) 0.00000013687 cs_b2left_v13p646_4 0.02395847195238 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9995864923695) (-0.0287548892021) 0.0000001381 cs_b2left_v13p646_5 0.00859967640296 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7760667380934 0.6306507892844 0.00000011874 cs_b2left_v13p646_6 (-0.16450366859309) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1490897067693 (-0.9888236745423) 0.00000014182 cs_b2left_v13p646_7 0.22977102599728 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9948304362186) 0.1015500009865 0.00000015171 cs_b2left_v13p646_8 (-0.02134828984275) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1377568625696 0.9904660755497 0.000000153 cs_b2left_v13p646_9 (-0.19061531455883) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9999867408392 (-0.0051495772402) 0.00000015294 cs_b2left_v13p646_10 0.00091571152065 (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2619516613172 (-0.9650809951155) 0.00000015395 cs_b2left_v13p646_11 0.1597788092289 (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7970009175884) (-0.6039780934067) 0.00000011695 cs_b2left_v13p646_12 0.09367747328017 (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9031352579191) 0.4293561526091 0.00000012181 cs_b2left_v13p646_13 (-0.06271339321224) (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.115480947786) 0.9933096952602 0.0000001338 cs_b2left_v13p646_14 (-0.13724252706867) (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7350480363681 0.6780150324523 0.00000011101 cs_b2left_v13p646_15 (-0.08895511995303) (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (0:ℝ) (1:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7350480363681 0.6780150324523 0.00000011101 cs_b2left_v13p646_15 186.275816 (by norm_num) (by norm_num) (-1.1603675228183) (-0.1522394199851) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.11920855945586:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13646:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma rb_b2left_32 : mainRemConst 15 (1 - 1/4:ℝ) 13.41233 ≤ 13.1501765 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  have c11 := sum_ub_step c10 (remTerm_ub 11 (by norm_num) (1 - 1/4:ℝ) 0.1655600260762 2.397895273518535 (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_11).2 0.95195388246736 (by norm_num))
  have c12 := sum_ub_step c11 (remTerm_ub 12 (by norm_num) (1 - 1/4:ℝ) 0.1551008098504 2.484906650508165 (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_12).2 0.95771044130855 (by norm_num))
  have c13 := sum_ub_step c12 (remTerm_ub 13 (by norm_num) (1 - 1/4:ℝ) 0.1460637632397 2.564949358181702 (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_13).2 0.96094841680103 (by norm_num))
  have c14 := sum_ub_step c13 (remTerm_ub 14 (by norm_num) (1 - 1/4:ℝ) 0.138166887162 2.639057330335424 (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_14).2 0.96228036207181 (by norm_num))
  have c15 := sum_ub_step c14 (remTerm_ub 15 (by norm_num) (1 - 1/4:ℝ) 0.1311993114177 2.708050201822375 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 0.96215485975843 (by norm_num))
  exact mainRemConst_le 15 (by norm_num) (1 - 1/4:ℝ) 13.41233 (by norm_num) _ 0.1311993114177 2.708050201822375 13.1501765 c15 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 (by norm_num)
lemma pc_b2left_32 : ∀ y ∈ Set.Icc (((13410:ℤ):ℝ)/1000) (((13646:ℤ):ℝ)/1000), 0 < (I ^ ((1):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((1):ℤ) = ((0:ℝ):ℂ) + ((1:ℝ):ℂ) * I := (by rw [I_zpow_eq (1) (0) 1 (by norm_num), rot1])
  refine vertical_piece 15 (by norm_num) (1 - 1/4:ℝ) (((13410:ℤ):ℝ)/1000) (((13646:ℤ):ℝ)/1000) (I ^ ((1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.708050201822375 (lg_15).2 (by norm_num) 13.41233 13.41 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 13.1501765 rb_b2left_32 0.1311993114177 13.666595 13.757755 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.380514915673 0.27144797944 (by rw [hrot]; exact bv_b2left_13p41_1_15) (by rw [hrot]; exact bv_b2left_13p646_1_15) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_13p646_0_15 : (0.276840356805:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13646:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13646:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((13646:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9994251631741) 0.033901955793 0.00000011485 cs_b2left_v13p646_2 (-0.59426182576996) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7542403312231) (-0.6565984486134) 0.00000012676 cs_b2left_v13p646_3 (-0.33087875542304) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.997701315236 (-0.0677649288076) 0.00000013687 cs_b2left_v13p646_4 0.35274063441013 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9995864923695) (-0.0287548892021) 0.0000001381 cs_b2left_v13p646_5 (-0.29894612991958) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7760667380934 0.6306507892844 0.00000011874 cs_b2left_v13p646_6 0.20243498317659 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1490897067693 (-0.9888236745423) 0.00000014182 cs_b2left_v13p646_7 0.03464365599145 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9948304362186) 0.1015500009865 0.00000015171 cs_b2left_v13p646_8 (-0.20913736879355) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1377568625696 0.9904660755497 0.000000153 cs_b2left_v13p646_9 0.02651129111755 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9999867408392 (-0.0051495772402) 0.00000015294 cs_b2left_v13p646_10 0.17782555595753 (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2619516613172 (-0.9650809951155) 0.00000015395 cs_b2left_v13p646_11 0.04336869839038 (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7970009175884) (-0.6039780934067) 0.00000011695 cs_b2left_v13p646_12 (-0.12361550590852) (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9031352579191) 0.4293561526091 0.00000012181 cs_b2left_v13p646_13 (-0.13191535227815) (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.115480947786) 0.9933096952602 0.0000001338 cs_b2left_v13p646_14 (-0.01595566156884) (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7350480363681 0.6780150324523 0.00000011101 cs_b2left_v13p646_15 0.09643778166591 (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7350480363681 0.6780150324523 0.00000011101 cs_b2left_v13p646_15 186.275816 (by norm_num) (by norm_num) (-0.36271802986644) (-0.04758835575722) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.2292520010479:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13646:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma bv_b2left_13p823_0_15 : (0.227016205333:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13823:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13823:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((13823:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9877639513568) 0.1559563272711 0.00000014109 cs_b2left_v13p823_2 (-0.58732804334101) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8669006833286) (-0.4984808974864) 0.00000015171 cs_b2left_v13p823_3 (-0.38030188693377) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9513552808737 (-0.3080959745821) 0.00000013887 cs_b2left_v13p823_4 0.33635483611368 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9673822882259) 0.2533209587981 0.00000014151 cs_b2left_v13p823_5 (-0.28931482745614) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9340344589323 0.3571829076636 0.00000012107 cs_b2left_v13p823_6 0.24364045657452 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.193549201864) (-0.9810905699562) 0.00000014553 cs_b2left_v13p823_7 (-0.04497469028616) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8916649348062) 0.4526959729551 0.00000011605 cs_b2left_v13p823_8 (-0.18744948621807) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5030335093671 0.8642669081099 0.00000011058 cs_b2left_v13p823_9 0.09680882273366 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9160383482061 (-0.4010906937538) 0.00000011453 cs_b2left_v13p823_10 0.16289719297537 (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1587095243012) (-0.9873253196872) 0.00000012996 cs_b2left_v13p823_11 (-0.02627597449803) (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9783105009076) (-0.2071438232242) 0.00000012667 cs_b2left_v13p823_12 (-0.15173677062254) (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6233507412634) 0.7819423593542 0.00000013508 cs_b2left_v13p823_13 (-0.09104897481749) (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3441881127502 0.938900709895 0.00000013416 cs_b2left_v13p823_14 0.04755538160035 (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9649000257828 0.262617478939 0.00000012404 cs_b2left_v13p823_15 0.12659420269556 (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9649000257828 0.262617478939 0.00000012404 cs_b2left_v13p823_15 191.137829 (by norm_num) (by norm_num) 0.21649529162412 0.02840403318626 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.25542023851993:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13823:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma rb_b2left_33 : mainRemConst 15 (1 - 1/4:ℝ) 13.648289 ≤ 13.13051608 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  have c11 := sum_ub_step c10 (remTerm_ub 11 (by norm_num) (1 - 1/4:ℝ) 0.1655600260762 2.397895273518535 (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_11).2 0.95195388246736 (by norm_num))
  have c12 := sum_ub_step c11 (remTerm_ub 12 (by norm_num) (1 - 1/4:ℝ) 0.1551008098504 2.484906650508165 (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_12).2 0.95771044130855 (by norm_num))
  have c13 := sum_ub_step c12 (remTerm_ub 13 (by norm_num) (1 - 1/4:ℝ) 0.1460637632397 2.564949358181702 (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_13).2 0.96094841680103 (by norm_num))
  have c14 := sum_ub_step c13 (remTerm_ub 14 (by norm_num) (1 - 1/4:ℝ) 0.138166887162 2.639057330335424 (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_14).2 0.96228036207181 (by norm_num))
  have c15 := sum_ub_step c14 (remTerm_ub 15 (by norm_num) (1 - 1/4:ℝ) 0.1311993114177 2.708050201822375 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 0.96215485975843 (by norm_num))
  exact mainRemConst_le 15 (by norm_num) (1 - 1/4:ℝ) 13.648289 (by norm_num) _ 0.1311993114177 2.708050201822375 13.13051608 c15 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 (by norm_num)
lemma pc_b2left_33 : ∀ y ∈ Set.Icc (((13646:ℤ):ℝ)/1000) (((13823:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 15 (by norm_num) (1 - 1/4:ℝ) (((13646:ℤ):ℝ)/1000) (((13823:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.708050201822375 (lg_15).2 (by norm_num) 13.648289 13.646 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 13.13051608 rb_b2left_33 0.1311993114177 13.843332 13.933336 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.276840356805 0.227016205333 (by rw [hrot]; exact bv_b2left_13p646_0_15) (by rw [hrot]; exact bv_b2left_13p823_0_15) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_13p823_0_20 : (0.228518252541:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 20 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13823:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 20 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13823:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((13823:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9877639513568) 0.1559563272711 0.00000014109 cs_b2left_v13p823_2 (-0.58732804334101) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8669006833286) (-0.4984808974864) 0.00000015171 cs_b2left_v13p823_3 (-0.38030188693377) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9513552808737 (-0.3080959745821) 0.00000013887 cs_b2left_v13p823_4 0.33635483611368 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9673822882259) 0.2533209587981 0.00000014151 cs_b2left_v13p823_5 (-0.28931482745614) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9340344589323 0.3571829076636 0.00000012107 cs_b2left_v13p823_6 0.24364045657452 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.193549201864) (-0.9810905699562) 0.00000014553 cs_b2left_v13p823_7 (-0.04497469028616) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8916649348062) 0.4526959729551 0.00000011605 cs_b2left_v13p823_8 (-0.18744948621807) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5030335093671 0.8642669081099 0.00000011058 cs_b2left_v13p823_9 0.09680882273366 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9160383482061 (-0.4010906937538) 0.00000011453 cs_b2left_v13p823_10 0.16289719297537 (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1587095243012) (-0.9873253196872) 0.00000012996 cs_b2left_v13p823_11 (-0.02627597449803) (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9783105009076) (-0.2071438232242) 0.00000012667 cs_b2left_v13p823_12 (-0.15173677062254) (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6233507412634) 0.7819423593542 0.00000013508 cs_b2left_v13p823_13 (-0.09104897481749) (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3441881127502 0.938900709895 0.00000013416 cs_b2left_v13p823_14 0.04755538160035 (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9649000257828 0.262617478939 0.00000012404 cs_b2left_v13p823_15 0.12659420269556 (by norm_num) (by norm_num))
  have c16 := sum_lb_step c15 (term_lb 16 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.125 0.125 (pwl_16_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_16_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8101536822708 (-0.5862175458847) 0.00000014994 cs_b2left_v13p823_16 0.10126919154135 (by norm_num) (by norm_num))
  have c17 := sum_lb_step c16 (term_lb 17 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1194437167569 0.119443716757 (pwl_17_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_17_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1061994813287 (-0.9943448446919) 0.0000001251 cs_b2left_v13p823_17 0.01268484582514 (by norm_num) (by norm_num))
  have c18 := sum_lb_step c17 (term_lb 18 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1144315079948 0.1144315079949 (pwl_18_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_18_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6316662543247) (-0.775240442142) 0.00000014447 cs_b2left_v13p823_18 (-0.07228253856379) (by norm_num) (by norm_num))
  have c19 := sum_lb_step c18 (term_lb 19 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1098840857857 0.1098840857858 (pwl_19_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_19_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9902544090459) (-0.1392702586903) 0.00000014485 cs_b2left_v13p823_19 (-0.10881321635008) (by norm_num) (by norm_num))
  have c20 := sum_lb_step c19 (term_lb 20 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.105737126344 0.1057371263441 (pwl_20_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_20_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8422770269779) 0.5390449051388 0.00000014731 cs_b2left_v13p823_20 (-0.08905996799444) (by norm_num) (by norm_num))
  have ht := tail_ub 20 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.105737126344 0.1057371263441 (pwl_20_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_20_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8422770269779) 0.5390449051388 0.00000014731 cs_b2left_v13p823_20 191.137829 (by norm_num) (by norm_num) (-1.22284105908725) (-0.12929969956333) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.09921855297811:ℝ) ≤ ∑ n ∈ Finset.range 20, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((13823:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c20
  linarith [cN, ht]
lemma bv_b2left_14_0_20 : (0.198273476836:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 20 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 20 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((14000:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9612534612314) 0.2756660716035 0.00000011686 cs_b2left_v14_2 (-0.5715647971941) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9468844694169) (-0.3215739438788) 0.00000013037 cs_b2left_v14_3 (-0.41539007168156) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8480164376045 (-0.5299699251396) 0.00000014088 cs_b2left_v14_4 0.29981903698523 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8572033072315) 0.5149781451605 0.0000001521 cs_b2left_v14_5 (-0.25636362963405) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9988429996693 0.0480901446412 0.00000014721 cs_b2left_v14_6 0.26054559105006 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5134535846096) (-0.8581173675231) 0.00000014924 cs_b2left_v14_7 (-0.11931025842803) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6690640085059) 0.7432047850377 0.00000015772 cs_b2left_v14_8 (-0.14065341473857) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.793180401478 0.6089867409979 0.00000015355 cs_b2left_v14_9 0.15264760988564 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.6820275759558 (-0.7313264562669) 0.00000014491 cs_b2left_v14_10 0.12128353377098 (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5512076862086) (-0.8343680762444) 0.00000012765 cs_b2left_v14_11 (-0.09125798003584) (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9733980889836) 0.2291204051926 0.00000015698 cs_b2left_v14_12 (-0.15097485625592) (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.2172775052817) 0.9761098737835 0.00000014955 cs_b2left_v14_13 (-0.03173639193262) (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7301128792184 0.6833265570717 0.0000001394 cs_b2left_v14_14 0.10087740453795 (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9772760308477 (-0.2119706572396) 0.00000013858 cs_b2left_v14_15 0.12821792413054 (by norm_num) (by norm_num))
  have c16 := sum_lb_step c15 (term_lb 16 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.125 0.125 (pwl_16_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_16_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4382636670103 (-0.8988464597353) 0.00000014629 cs_b2left_v14_16 0.05478294009003 (by norm_num) (by norm_num))
  have c17 := sum_lb_step c16 (term_lb 17 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1194437167569 0.119443716757 (pwl_17_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_17_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3848808027154) (-0.9229662874115) 0.00000014086 cs_b2left_v14_17 (-0.04597161040959) (by norm_num) (by norm_num))
  have c18 := sum_lb_step c17 (term_lb 18 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1144315079948 0.1144315079949 (pwl_18_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_18_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9303244229834) (-0.3667376007999) 0.00000014346 cs_b2left_v14_18 (-0.10645844306282) (by norm_num) (by norm_num))
  have c19 := sum_lb_step c18 (term_lb 19 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1098840857857 0.1098840857858 (pwl_19_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_19_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9281290807361) 0.3722585248665 0.00000015286 cs_b2left_v14_19 (-0.10198663232479) (by norm_num) (by norm_num))
  have c20 := sum_lb_step c19 (term_lb 20 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.105737126344 0.1057371263441 (pwl_20_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_20_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4539994767557) 0.8910019501106 0.00000013507 cs_b2left_v14_20 (-0.04800461431579) (by norm_num) (by norm_num))
  have ht := tail_ub 20 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.105737126344 0.1057371263441 (pwl_20_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_20_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4539994767557) 0.8910019501106 0.00000013507 cs_b2left_v14_20 196.0625 (by norm_num) (by norm_num) (-1.5110315735259) (-0.15977213639968) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.03850134043675:ℝ) ≤ ∑ n ∈ Finset.range 20, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c20
  linarith [cN, ht]
lemma rb_b2left_34 : mainRemConst 20 (1 - 1/4:ℝ) 13.82526 ≤ 18.22103847 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  have c11 := sum_ub_step c10 (remTerm_ub 11 (by norm_num) (1 - 1/4:ℝ) 0.1655600260762 2.397895273518535 (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_11).2 0.95195388246736 (by norm_num))
  have c12 := sum_ub_step c11 (remTerm_ub 12 (by norm_num) (1 - 1/4:ℝ) 0.1551008098504 2.484906650508165 (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_12).2 0.95771044130855 (by norm_num))
  have c13 := sum_ub_step c12 (remTerm_ub 13 (by norm_num) (1 - 1/4:ℝ) 0.1460637632397 2.564949358181702 (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_13).2 0.96094841680103 (by norm_num))
  have c14 := sum_ub_step c13 (remTerm_ub 14 (by norm_num) (1 - 1/4:ℝ) 0.138166887162 2.639057330335424 (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_14).2 0.96228036207181 (by norm_num))
  have c15 := sum_ub_step c14 (remTerm_ub 15 (by norm_num) (1 - 1/4:ℝ) 0.1311993114177 2.708050201822375 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 0.96215485975843 (by norm_num))
  have c16 := sum_ub_step c15 (remTerm_ub 16 (by norm_num) (1 - 1/4:ℝ) 0.125 2.7725887232 (pwh_16_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_16).2 0.96090602850198 (by norm_num))
  have c17 := sum_ub_step c16 (remTerm_ub 17 (by norm_num) (1 - 1/4:ℝ) 0.119443716757 2.833213345016435 (pwh_17_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_17).2 0.95878640297697 (by norm_num))
  have c18 := sum_ub_step c17 (remTerm_ub 18 (by norm_num) (1 - 1/4:ℝ) 0.1144315079949 2.89037175861633 (pwh_18_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_18).2 0.95598930013582 (by norm_num))
  have c19 := sum_ub_step c18 (remTerm_ub 19 (by norm_num) (1 - 1/4:ℝ) 0.1098840857858 2.944438979886606 (pwh_19_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_19).2 0.95266435580415 (by norm_num))
  have c20 := sum_ub_step c19 (remTerm_ub 20 (by norm_num) (1 - 1/4:ℝ) 0.1057371263441 2.99573227451421 (pwh_20_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_20).2 0.94892852076467 (by norm_num))
  exact mainRemConst_le 20 (by norm_num) (1 - 1/4:ℝ) 13.82526 (by norm_num) _ 0.1057371263441 2.99573227451421 18.22103847 c20 (pwh_20_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_20).2 (by norm_num)
lemma pc_b2left_34 : ∀ y ∈ Set.Icc (((13823:ℤ):ℝ)/1000) (((14000:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 20 (by norm_num) (1 - 1/4:ℝ) (((13823:ℤ):ℝ)/1000) (((14000:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.99573227451421 (lg_20).2 (by norm_num) 13.82526 13.823 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 18.22103847 rb_b2left_34 0.1057371263441 14.020075 14.108952 (pwh_20_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.228518252541 0.198273476836 (by rw [hrot]; exact bv_b2left_13p823_0_20) (by rw [hrot]; exact bv_b2left_14_0_20) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_14_0_15 : (0.189790969792:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((14000:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9612534612314) 0.2756660716035 0.00000011686 cs_b2left_v14_2 (-0.5715647971941) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9468844694169) (-0.3215739438788) 0.00000013037 cs_b2left_v14_3 (-0.41539007168156) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8480164376045 (-0.5299699251396) 0.00000014088 cs_b2left_v14_4 0.29981903698523 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8572033072315) 0.5149781451605 0.0000001521 cs_b2left_v14_5 (-0.25636362963405) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9988429996693 0.0480901446412 0.00000014721 cs_b2left_v14_6 0.26054559105006 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5134535846096) (-0.8581173675231) 0.00000014924 cs_b2left_v14_7 (-0.11931025842803) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6690640085059) 0.7432047850377 0.00000015772 cs_b2left_v14_8 (-0.14065341473857) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.793180401478 0.6089867409979 0.00000015355 cs_b2left_v14_9 0.15264760988564 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.6820275759558 (-0.7313264562669) 0.00000014491 cs_b2left_v14_10 0.12128353377098 (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5512076862086) (-0.8343680762444) 0.00000012765 cs_b2left_v14_11 (-0.09125798003584) (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9733980889836) 0.2291204051926 0.00000015698 cs_b2left_v14_12 (-0.15097485625592) (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.2172775052817) 0.9761098737835 0.00000014955 cs_b2left_v14_13 (-0.03173639193262) (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7301128792184 0.6833265570717 0.0000001394 cs_b2left_v14_14 0.10087740453795 (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9772760308477 (-0.2119706572396) 0.00000013858 cs_b2left_v14_15 0.12821792413054 (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9772760308477 (-0.2119706572396) 0.00000013858 cs_b2left_v14_15 196.0625 (by norm_num) (by norm_num) 0.7343691794284 0.09634873066739 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.28613970045971:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma bv_b2left_14p132_0_15 : (0.171847828845:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14132:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14132:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((14132:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9320457434291) 0.362340629784 0.00000014472 cs_b2left_v14p132_2 (-0.55419780084801) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9834158221602) (-0.1813651575614) 0.00000015251 cs_b2left_v14p132_3 (-0.43141606939534) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7374184731962 (-0.6754361519707) 0.00000011755 cs_b2left_v14p132_4 0.26071675992437 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7293479484265) 0.6841429456604 0.0000001566 cs_b2left_v14p132_5 (-0.21812595998752) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.982304478014 (-0.1872909834287) 0.00000011695 cs_b2left_v14p132_6 0.25623156807332 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7146087746242) (-0.6995243378209) 0.00000010963 cs_b2left_v14p132_7 (-0.16605229455846) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4425697883663) 0.8967340644924 0.00000014131 cs_b2left_v14p132_8 (-0.09303886684101) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9342133973542 0.3567146313286 0.00000011634 cs_b2left_v14p132_9 0.17978942975795 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4318927812785 (-0.9019249555698) 0.00000011274 cs_b2left_v14p132_10 0.07680258398083 (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7835339699244) (-0.6213489502133) 0.00000015175 cs_b2left_v14p132_11 (-0.12972192961601) (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8476895746152) 0.5304925871454 0.00000014192 cs_b2left_v14p132_12 (-0.13147736153647) (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1192642664657 0.9928625457455 0.00000013447 cs_b2left_v14p132_13 0.01742016793879 (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9195141558288 0.3930568880333 0.00000014924 cs_b2left_v14p132_14 0.12704638799214 (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8413319516552 (-0.5405187759218) 0.00000011214 cs_b2left_v14p132_15 0.11038215801809 (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8413319516552 (-0.5405187759218) 0.00000011214 cs_b2left_v14p132_15 199.775924 (by norm_num) (by norm_num) 1.00999725246336 0.13251094405697 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.30435877290267:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14132:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma rb_b2left_35 : mainRemConst 15 (1 - 1/4:ℝ) 14.002231 ≤ 13.10230111 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  have c11 := sum_ub_step c10 (remTerm_ub 11 (by norm_num) (1 - 1/4:ℝ) 0.1655600260762 2.397895273518535 (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_11).2 0.95195388246736 (by norm_num))
  have c12 := sum_ub_step c11 (remTerm_ub 12 (by norm_num) (1 - 1/4:ℝ) 0.1551008098504 2.484906650508165 (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_12).2 0.95771044130855 (by norm_num))
  have c13 := sum_ub_step c12 (remTerm_ub 13 (by norm_num) (1 - 1/4:ℝ) 0.1460637632397 2.564949358181702 (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_13).2 0.96094841680103 (by norm_num))
  have c14 := sum_ub_step c13 (remTerm_ub 14 (by norm_num) (1 - 1/4:ℝ) 0.138166887162 2.639057330335424 (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_14).2 0.96228036207181 (by norm_num))
  have c15 := sum_ub_step c14 (remTerm_ub 15 (by norm_num) (1 - 1/4:ℝ) 0.1311993114177 2.708050201822375 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 0.96215485975843 (by norm_num))
  exact mainRemConst_le 15 (by norm_num) (1 - 1/4:ℝ) 14.002231 (by norm_num) _ 0.1311993114177 2.708050201822375 13.10230111 c15 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 (by norm_num)
lemma pc_b2left_35 : ∀ y ∈ Set.Icc (((14000:ℤ):ℝ)/1000) (((14132:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 15 (by norm_num) (1 - 1/4:ℝ) (((14000:ℤ):ℝ)/1000) (((14132:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.708050201822375 (lg_15).2 (by norm_num) 14.002231 14 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 13.10230111 rb_b2left_35 0.1311993114177 14.151888 14.239942 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.189790969792 0.171847828845 (by rw [hrot]; exact bv_b2left_14_0_15) (by rw [hrot]; exact bv_b2left_14p132_0_15) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_14p264_0_15 : (0.163435382502:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14264:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14264:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((14264:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8950408872819) 0.4459840916251 0.00000013457 cs_b2left_v14p264_2 (-0.53219457570283) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9993022874536) (-0.0373488646389) 0.00000013252 cs_b2left_v14p264_3 (-0.43838531533601) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.6021964654941 (-0.7983479297564) 0.00000015234 cs_b2left_v14p264_4 0.21290854831835 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5686983085977) 0.8225461894558 0.00000015319 cs_b2left_v14p264_5 (-0.17008051034336) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9110734471343 (-0.4122440708206) 0.00000014721 cs_b2left_v14p264_6 0.23765112883798 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8688747958689) (-0.4950319070693) 0.00000014427 cs_b2left_v14p264_7 (-0.20189880181099) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1829399825121) 0.9831240831135 0.00000012491 cs_b2left_v14p264_8 (-0.03845842013436) (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.997210117651 0.0746457048624 0.00000014209 cs_b2left_v14p264_9 0.19191314927616 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1421658296567 (-0.989842854638) 0.00000014086 cs_b2left_v14p264_10 0.0252810317201 (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9380140425375) (-0.3465972530578) 0.00000014559 cs_b2left_v14p264_11 (-0.15529765344624) (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6315936890524) 0.7752995627074 0.00000011979 cs_b2left_v14p264_12 (-0.09796071124796) (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4422646522082 0.8968845953673 0.00000011938 cs_b2left_v14p264_13 0.06459882201229 (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9984548237305 0.0555694607608 0.00000011684 cs_b2left_v14p264_14 0.1379533788232 (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5990227674049 (-0.8007319926983) 0.00000013573 cs_b2left_v14p264_15 0.0785913567993 (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5990227674049 (-0.8007319926983) 0.00000013573 cs_b2left_v14p264_15 203.524196 (by norm_num) (by norm_num) 1.15233870993076 0.15118604526288 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.31462142776563:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14264:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma rb_b2left_36 : mainRemConst 15 (1 - 1/4:ℝ) 14.134211 ≤ 13.09215151 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  have c11 := sum_ub_step c10 (remTerm_ub 11 (by norm_num) (1 - 1/4:ℝ) 0.1655600260762 2.397895273518535 (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_11).2 0.95195388246736 (by norm_num))
  have c12 := sum_ub_step c11 (remTerm_ub 12 (by norm_num) (1 - 1/4:ℝ) 0.1551008098504 2.484906650508165 (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_12).2 0.95771044130855 (by norm_num))
  have c13 := sum_ub_step c12 (remTerm_ub 13 (by norm_num) (1 - 1/4:ℝ) 0.1460637632397 2.564949358181702 (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_13).2 0.96094841680103 (by norm_num))
  have c14 := sum_ub_step c13 (remTerm_ub 14 (by norm_num) (1 - 1/4:ℝ) 0.138166887162 2.639057330335424 (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_14).2 0.96228036207181 (by norm_num))
  have c15 := sum_ub_step c14 (remTerm_ub 15 (by norm_num) (1 - 1/4:ℝ) 0.1311993114177 2.708050201822375 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 0.96215485975843 (by norm_num))
  exact mainRemConst_le 15 (by norm_num) (1 - 1/4:ℝ) 14.134211 (by norm_num) _ 0.1311993114177 2.708050201822375 13.09215151 c15 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 (by norm_num)
lemma pc_b2left_36 : ∀ y ∈ Set.Icc (((14132:ℤ):ℝ)/1000) (((14264:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 15 (by norm_num) (1 - 1/4:ℝ) (((14132:ℤ):ℝ)/1000) (((14264:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.708050201822375 (lg_15).2 (by norm_num) 14.134211 14.132 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 13.09215151 rb_b2left_36 0.1311993114177 14.283704 14.37095 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.171847828845 0.163435382502 (by rw [hrot]; exact bv_b2left_14p132_0_15) (by rw [hrot]; exact bv_b2left_14p264_0_15) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_14p396_0_15 : (0.165399541014:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14396:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14396:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((14396:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.850548540334) 0.525896549201 0.00000010678 cs_b2left_v14p396_2 (-0.50573925140199) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9942103376887) 0.1074514028324 0.00000011763 cs_b2left_v14p396_3 (-0.43615151455028) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4468656454136 (-0.8946010814598) 0.00000010807 cs_b2left_v14p396_4 0.15799082586708 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3824779442469) 0.9239646217046 0.00000014882 cs_b2left_v14p396_5 (-0.11438763006231) (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7891158340362 (-0.6142444142793) 0.00000011721 cs_b2left_v14p396_6 0.20583880671634 (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.966129484513) (-0.2580577820938) 0.00000013042 cs_b2left_v14p396_7 (-0.22449768388751) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.0903866992477 0.995906744931 0.00000011312 cs_b2left_v14p396_8 0.01900143906544 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9769083934988 (-0.2136585844559) 0.00000012807 cs_b2left_v14p396_9 0.18800608333955 (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1605937418945) (-0.9870205925226) 0.0000001484 cs_b2left_v14p396_10 (-0.02855808084888) (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9992999960907) (-0.037410121799) 0.00000012169 cs_b2left_v14p396_11 (-0.16544415355773) (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3481523029479) 0.9374379840553 0.00000012397 cs_b2left_v14p396_12 (-0.05399872336635) (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7150498599324 0.6990734566629 0.00000011732 cs_b2left_v14p396_13 0.10444285630947 (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9574517201032 (-0.2885934920809) 0.00000013718 cs_b2left_v14p396_14 0.13228810482073 (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2809822381066 (-0.9597129684799) 0.00000015925 cs_b2left_v14p396_15 0.03686465526667 (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2809822381066 (-0.9597129684799) 0.00000015925 cs_b2left_v14p396_15 207.307316 (by norm_num) (by norm_num) 1.14525138182631 0.15025619269579 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.31565573371023:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14396:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma rb_b2left_37 : mainRemConst 15 (1 - 1/4:ℝ) 14.26619 ≤ 13.08219474 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  have c11 := sum_ub_step c10 (remTerm_ub 11 (by norm_num) (1 - 1/4:ℝ) 0.1655600260762 2.397895273518535 (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_11).2 0.95195388246736 (by norm_num))
  have c12 := sum_ub_step c11 (remTerm_ub 12 (by norm_num) (1 - 1/4:ℝ) 0.1551008098504 2.484906650508165 (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_12).2 0.95771044130855 (by norm_num))
  have c13 := sum_ub_step c12 (remTerm_ub 13 (by norm_num) (1 - 1/4:ℝ) 0.1460637632397 2.564949358181702 (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_13).2 0.96094841680103 (by norm_num))
  have c14 := sum_ub_step c13 (remTerm_ub 14 (by norm_num) (1 - 1/4:ℝ) 0.138166887162 2.639057330335424 (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_14).2 0.96228036207181 (by norm_num))
  have c15 := sum_ub_step c14 (remTerm_ub 15 (by norm_num) (1 - 1/4:ℝ) 0.1311993114177 2.708050201822375 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 0.96215485975843 (by norm_num))
  exact mainRemConst_le 15 (by norm_num) (1 - 1/4:ℝ) 14.26619 (by norm_num) _ 0.1311993114177 2.708050201822375 13.08219474 c15 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 (by norm_num)
lemma pc_b2left_37 : ∀ y ∈ Set.Icc (((14264:ℤ):ℝ)/1000) (((14396:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 15 (by norm_num) (1 - 1/4:ℝ) (((14264:ℤ):ℝ)/1000) (((14396:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.708050201822375 (lg_15).2 (by norm_num) 14.26619 14.264 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 13.08219474 rb_b2left_37 0.1311993114177 14.415524 14.501977 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.163435382502 0.165399541014 (by rw [hrot]; exact bv_b2left_14p264_0_15) (by rw [hrot]; exact bv_b2left_14p396_0_15) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_14p396_3_15 : (0.194774840666:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14396:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14396:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((14396:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.850548540334) 0.525896549201 0.00000010678 cs_b2left_v14p396_2 0.3126998955408 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9942103376887) 0.1074514028324 0.00000011763 cs_b2left_v14p396_3 0.04713794803773 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.4468656454136 (-0.8946010814598) 0.00000010807 cs_b2left_v14p396_4 (-0.31628928378707) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3824779442469) 0.9239646217046 0.00000014882 cs_b2left_v14p396_5 0.27632982968389 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7891158340362 (-0.6142444142793) 0.00000011721 cs_b2left_v14p396_6 (-0.1602241074381) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.966129484513) (-0.2580577820938) 0.00000013042 cs_b2left_v14p396_7 (-0.05996442172225) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.0903866992477 0.995906744931 0.00000011312 cs_b2left_v14p396_8 0.20936357915428 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9769083934988 (-0.2136585844559) 0.00000012807 cs_b2left_v14p396_9 (-0.04111863839719) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1605937418945) (-0.9870205925226) 0.0000001484 cs_b2left_v14p396_10 (-0.17551986608641) (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9992999960907) (-0.037410121799) 0.00000012169 cs_b2left_v14p396_11 (-0.00619364088756) (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3481523029479) 0.9374379840553 0.00000012397 cs_b2left_v14p396_12 0.14539737128356 (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7150498599324 0.6990734566629 0.00000011732 cs_b2left_v14p396_13 0.10210928272489 (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9574517201032 (-0.2885934920809) 0.00000013718 cs_b2left_v14p396_14 (-0.03987408340977) (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2809822381066 (-0.9597129684799) 0.00000015925 cs_b2left_v14p396_15 (-0.1259137015167) (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2809822381066 (-0.9597129684799) 0.00000015925 cs_b2left_v14p396_15 207.307316 (by norm_num) (by norm_num) (-0.20453367625271) (-0.02683467748606) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.1679401631801:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14396:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma bv_b2left_14p528_3_15 : (0.287435422254:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14528:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14528:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((14528:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7989408701887) 0.6014095824754 0.00000012832 cs_b2left_v14p528_2 0.35760020095571 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9682468868295) 0.2499959317287 0.00000011173 cs_b2left_v14p528_3 0.10967100068233 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.276612938949 (-0.9609814160565) 0.00000015076 cs_b2left_v14p528_4 (-0.33975829124564) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1790599477487) 0.9838381651021 0.00000014444 cs_b2left_v14p528_5 0.29423619702319 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.6232220670182 (-0.7820449189027) 0.00000014722 cs_b2left_v14p528_6 (-0.20399444565191) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9999913832218) (-0.0041512413659) 0.00000012375 cs_b2left_v14p528_7 (-0.00096464474237) (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3569460500713 0.9341250009171 0.00000012972 cs_b2left_v14p528_8 0.19637556389721 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8750040715804 (-0.4841155592602) 0.00000013063 cs_b2left_v14p528_9 (-0.09316810795903) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.4486313832361) (-0.8937168913986) 0.00000011622 cs_b2left_v14p528_10 (-0.15892785530499) (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9613028451569) 0.2754938105579 0.00000013121 cs_b2left_v14p528_11 0.04561074073663 (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.027588172413) 0.9996193739332 0.0000001463 cs_b2left_v14p528_12 0.15504175174784 (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9066475799629 0.4218888073265 0.0000001326 cs_b2left_v14p528_13 0.06162264749872 (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.8014305826897 (-0.598087803863) 0.00000015205 cs_b2left_v14p528_14 (-0.08263595111759) (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0725812947442) (-0.9973624996223) 0.00000013281 cs_b2left_v14p528_15 (-0.13085329060887) (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0725812947442) (-0.9973624996223) 0.00000013281 cs_b2left_v14p528_15 211.125284 (by norm_num) (by norm_num) (-0.59131336517859) (-0.07757990634345) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.20985551591123:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14528:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma rb_b2left_38 : mainRemConst 15 (1 - 1/4:ℝ) 14.39817 ≤ 13.07242523 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  have c11 := sum_ub_step c10 (remTerm_ub 11 (by norm_num) (1 - 1/4:ℝ) 0.1655600260762 2.397895273518535 (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_11).2 0.95195388246736 (by norm_num))
  have c12 := sum_ub_step c11 (remTerm_ub 12 (by norm_num) (1 - 1/4:ℝ) 0.1551008098504 2.484906650508165 (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_12).2 0.95771044130855 (by norm_num))
  have c13 := sum_ub_step c12 (remTerm_ub 13 (by norm_num) (1 - 1/4:ℝ) 0.1460637632397 2.564949358181702 (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_13).2 0.96094841680103 (by norm_num))
  have c14 := sum_ub_step c13 (remTerm_ub 14 (by norm_num) (1 - 1/4:ℝ) 0.138166887162 2.639057330335424 (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_14).2 0.96228036207181 (by norm_num))
  have c15 := sum_ub_step c14 (remTerm_ub 15 (by norm_num) (1 - 1/4:ℝ) 0.1311993114177 2.708050201822375 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 0.96215485975843 (by norm_num))
  exact mainRemConst_le 15 (by norm_num) (1 - 1/4:ℝ) 14.39817 (by norm_num) _ 0.1311993114177 2.708050201822375 13.07242523 c15 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 (by norm_num)
lemma pc_b2left_38 : ∀ y ∈ Set.Icc (((14396:ℤ):ℝ)/1000) (((14528:ℤ):ℝ)/1000), 0 < (I ^ ((-1):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-1):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-1) (-1) 3 (by norm_num), rot3])
  refine vertical_piece 15 (by norm_num) (1 - 1/4:ℝ) (((14396:ℤ):ℝ)/1000) (((14528:ℤ):ℝ)/1000) (I ^ ((-1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.708050201822375 (lg_15).2 (by norm_num) 14.39817 14.396 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 13.07242523 rb_b2left_38 0.1311993114177 14.547347 14.633021 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.194774840666 0.287435422254 (by rw [hrot]; exact bv_b2left_14p396_3_15) (by rw [hrot]; exact bv_b2left_14p528_3_15) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_14p764_3_15 : (0.451136456337:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 15 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14764:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 15 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14764:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((14764:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6903330387915) 0.7234917383984 0.00000014442 cs_b2left_v14p764_2 0.43019067560184 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8717916118528) 0.4898769084309 0.00000011192 cs_b2left_v14p764_3 0.21490470714545 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0468804840363) (-0.9989005056642) 0.00000013314 cs_b2left_v14p764_4 (-0.35316470771504) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1984698113853 0.9801070012854 0.00000011756 cs_b2left_v14p764_5 0.29312032680901 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2474046634551 (-0.9689122418984) 0.00000013273 cs_b2left_v14p764_6 (-0.25273830282894) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8982243063558) 0.4395373651434 0.00000011186 cs_b2left_v14p764_7 0.10213442774052 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7550594103476 0.6556563786356 0.00000012607 cs_b2left_v14p764_8 0.13783474810525 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5200412352089 (-0.8541411555957) 0.000000131 cs_b2left_v14p764_9 (-0.16437956724736) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8461095823472) (-0.5330089817149) 0.00000013446 cs_b2left_v14p764_10 (-0.0947839136657) (by norm_num) (by norm_num))
  have c11 := sum_lb_step c10 (term_lb 11 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1655600260761 0.1655600260762 (pwl_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6637263057772) 0.7479755283436 0.00000014701 cs_b2left_v14p764_11 0.12383482363787 (by norm_num) (by norm_num))
  have c12 := sum_lb_step c11 (term_lb 12 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1551008098503 0.1551008098504 (pwl_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5302083043373 0.8478674153497 0.00000014504 cs_b2left_v14p764_12 0.13150490027059 (by norm_num) (by norm_num))
  have c13 := sum_lb_step c12 (term_lb 13 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1460637632396 0.1460637632397 (pwl_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9856184991747 (-0.1689857215406) 0.00000014104 cs_b2left_v14p764_13 (-0.02468271102283) (by norm_num) (by norm_num))
  have c14 := sum_lb_step c13 (term_lb 14 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1381668871619 0.138166887162 (pwl_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.3020722693439 (-0.9532850277296) 0.00000014017 cs_b2left_v14p764_14 (-0.1317124442264) (by norm_num) (by norm_num))
  have c15 := sum_lb_step c14 (term_lb 15 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6531560991072) (-0.7572232895137) 0.00000013664 cs_b2left_v14p764_15 (-0.09934719210072) (by norm_num) (by norm_num))
  have ht := tail_ub 15 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1311993114176 0.1311993114177 (pwl_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6531560991072) (-0.7572232895137) 0.00000013664 cs_b2left_v14p764_15 218.038196 (by norm_num) (by norm_num) (-1.05504125241556) (-0.13842068583408) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.31271577050354:ℝ) ≤ ∑ n ∈ Finset.range 15, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14764:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c15
  linarith [cN, ht]
lemma rb_b2left_39 : mainRemConst 15 (1 - 1/4:ℝ) 14.53015 ≤ 13.0628378 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  have c11 := sum_ub_step c10 (remTerm_ub 11 (by norm_num) (1 - 1/4:ℝ) 0.1655600260762 2.397895273518535 (pwh_11_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_11).2 0.95195388246736 (by norm_num))
  have c12 := sum_ub_step c11 (remTerm_ub 12 (by norm_num) (1 - 1/4:ℝ) 0.1551008098504 2.484906650508165 (pwh_12_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_12).2 0.95771044130855 (by norm_num))
  have c13 := sum_ub_step c12 (remTerm_ub 13 (by norm_num) (1 - 1/4:ℝ) 0.1460637632397 2.564949358181702 (pwh_13_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_13).2 0.96094841680103 (by norm_num))
  have c14 := sum_ub_step c13 (remTerm_ub 14 (by norm_num) (1 - 1/4:ℝ) 0.138166887162 2.639057330335424 (pwh_14_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_14).2 0.96228036207181 (by norm_num))
  have c15 := sum_ub_step c14 (remTerm_ub 15 (by norm_num) (1 - 1/4:ℝ) 0.1311993114177 2.708050201822375 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 0.96215485975843 (by norm_num))
  exact mainRemConst_le 15 (by norm_num) (1 - 1/4:ℝ) 14.53015 (by norm_num) _ 0.1311993114177 2.708050201822375 13.0628378 c15 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_15).2 (by norm_num)
lemma pc_b2left_39 : ∀ y ∈ Set.Icc (((14528:ℤ):ℝ)/1000) (((14764:ℤ):ℝ)/1000), 0 < (I ^ ((-1):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-1):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-1) (-1) 3 (by norm_num), rot3])
  refine vertical_piece 15 (by norm_num) (1 - 1/4:ℝ) (((14528:ℤ):ℝ)/1000) (((14764:ℤ):ℝ)/1000) (I ^ ((-1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.708050201822375 (lg_15).2 (by norm_num) 14.53015 14.528 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 13.0628378 rb_b2left_39 0.1311993114177 14.783038 14.867354 (pwh_15_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.287435422254 0.451136456337 (by rw [hrot]; exact bv_b2left_14p528_3_15) (by rw [hrot]; exact bv_b2left_14p764_3_15) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_b2left_14p764_3_10 : (0.463479233863:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14764:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14764:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((14764:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6903330387915) 0.7234917383984 0.00000014442 cs_b2left_v14p764_2 0.43019067560184 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8717916118528) 0.4898769084309 0.00000011192 cs_b2left_v14p764_3 0.21490470714545 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.0468804840363) (-0.9989005056642) 0.00000013314 cs_b2left_v14p764_4 (-0.35316470771504) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.1984698113853 0.9801070012854 0.00000011756 cs_b2left_v14p764_5 0.29312032680901 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.2474046634551 (-0.9689122418984) 0.00000013273 cs_b2left_v14p764_6 (-0.25273830282894) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8982243063558) 0.4395373651434 0.00000011186 cs_b2left_v14p764_7 0.10213442774052 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.7550594103476 0.6556563786356 0.00000012607 cs_b2left_v14p764_8 0.13783474810525 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5200412352089 (-0.8541411555957) 0.000000131 cs_b2left_v14p764_9 (-0.16437956724736) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8461095823472) (-0.5330089817149) 0.00000013446 cs_b2left_v14p764_10 (-0.0947839136657) (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.8461095823472) (-0.5330089817149) 0.00000013446 cs_b2left_v14p764_10 218.038196 (by norm_num) (by norm_num) (-0.84554113976411) (-0.15036083991825) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.31311839394503:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((14764:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma bv_b2left_15_3_10 : (0.616549796996:ℝ) ≤ ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * eulerMaclaurinMain 10 (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((15000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 10 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((15000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (1 - 1/4:ℝ) (((15000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 1 1 (pw1_lo (1 - 1/4:ℝ)) (pw1_hi (1 - 1/4:ℝ)) 1 0 0 (cs_one (((15000:ℤ):ℝ)/1000)) 0 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (1 - 1/4:ℝ) (((15000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.5946035575013 0.5946035575014 (pwl_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.5632935954295) 0.826256815608 0.00000010987 cs_b2left_v15_2 0.49129517664111 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (1 - 1/4:ℝ) (((15000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.4386913376508 0.4386913376509 (pwl_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.7170601161939) 0.6970113268357 0.0000001121 cs_b2left_v15_3 0.30577278215001 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (1 - 1/4:ℝ) (((15000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.3535533905932 0.3535533905933 (pwl_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.3654006440121) (-0.9308503474528) 0.00000011255 cs_b2left_v15_4 (-0.32910533626933) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (1 - 1/4:ℝ) (((15000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2990697562442 0.2990697562443 (pwl_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.5477092431889 0.8366687426487 0.00000015002 cs_b2left_v15_5 0.25022227205464 (by norm_num) (by norm_num))
  have c6 := sum_lb_step c5 (term_lb 6 (by norm_num) (1 - 1/4:ℝ) (((15000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2608474300122 0.2608474300123 (pwl_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.1719949813052) (-0.9850978258047) 0.00000011692 cs_b2left_v15_6 (-0.25696026667015) (by norm_num) (by norm_num))
  have c7 := sum_lb_step c6 (term_lb 7 (by norm_num) (1 - 1/4:ℝ) (((15000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2323680802425 0.2323680802426 (pwl_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.6103306811647) 0.7921467412141 0.00000010788 cs_b2left_v15_7 0.1840695924584 (by norm_num) (by norm_num))
  have c8 := sum_lb_step c7 (term_lb 8 (by norm_num) (1 - 1/4:ℝ) (((15000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.2102241038134 0.2102241038135 (pwl_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.9749492864381 0.2224272664803 0.00000012241 cs_b2left_v15_8 0.04675954702595 (by norm_num) (by norm_num))
  have c9 := sum_lb_step c8 (term_lb 9 (by norm_num) (1 - 1/4:ℝ) (((15000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1924500897298 0.1924500897299 (pwl_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) 0.0283504276599 (-0.9995980458421) 0.00000013136 cs_b2left_v15_9 (-0.19237275889639) (by norm_num) (by norm_num))
  have c10 := sum_lb_step c9 (term_lb 10 (by norm_num) (1 - 1/4:ℝ) (((15000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9998243594199) (-0.0187416559615) 0.0000001527 cs_b2left_v15_10 (-0.00333281724497) (by norm_num) (by norm_num))
  have ht := tail_ub 10 (by norm_num) (1 - 1/4:ℝ) (((15000:ℤ):ℝ)/1000) (0:ℝ) ((-1):ℝ) (by norm_num) 0.1778279410038 0.1778279410039 (pwl_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (-0.9998243594199) (-0.0187416559615) 0.0000001527 cs_b2left_v15_10 225.0625 (by norm_num) (by norm_num) (-0.67594330266052) (-0.12020160574742) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.49634819124927:ℝ) ≤ ∑ n ∈ Finset.range 10, ((((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((1 - 1/4:ℝ):ℝ)):ℂ) + ((((((15000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c10
  linarith [cN, ht]
lemma rb_b2left_40 : mainRemConst 10 (1 - 1/4:ℝ) 14.766116 ≤ 7.89681146 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (1 - 1/4:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (1 - 1/4:ℝ) 1 0 (pw1_hi (1 - 1/4:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (1 - 1/4:ℝ) 0.5946035575014 0.6931471808 (pwh_2_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_2).2 0.28567907148591 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (1 - 1/4:ℝ) 0.4386913376509 1.098612288908165 (pwh_3_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_3).2 0.52947805432663 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (1 - 1/4:ℝ) 0.3535533905933 1.3862943616 (pwh_4_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_4).2 0.67946316883684 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (1 - 1/4:ℝ) 0.2990697562443 1.60943791291421 (pwh_5_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_5).2 0.77467751719181 (by norm_num))
  have c6 := sum_ub_step c5 (remTerm_ub 6 (by norm_num) (1 - 1/4:ℝ) 0.2608474300123 1.791759469708165 (pwh_6_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_6).2 0.83742511029917 (by norm_num))
  have c7 := sum_ub_step c6 (remTerm_ub 7 (by norm_num) (1 - 1/4:ℝ) 0.2323680802426 1.945910149535424 (pwh_7_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_7).2 0.87987714418111 (by norm_num))
  have c8 := sum_ub_step c7 (remTerm_ub 8 (by norm_num) (1 - 1/4:ℝ) 0.2102241038135 2.0794415424 (pwh_8_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_8).2 0.90902523910868 (by norm_num))
  have c9 := sum_ub_step c8 (remTerm_ub 9 (by norm_num) (1 - 1/4:ℝ) 0.1924500897299 2.19722457781633 (pwh_9_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_9).2 0.9291097436372 (by norm_num))
  have c10 := sum_ub_step c9 (remTerm_ub 10 (by norm_num) (1 - 1/4:ℝ) 0.1778279410039 2.30258509371421 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 0.94282562498861 (by norm_num))
  exact mainRemConst_le 10 (by norm_num) (1 - 1/4:ℝ) 14.766116 (by norm_num) _ 0.1778279410039 2.30258509371421 7.89681146 c10 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (lg_10).2 (by norm_num)
lemma pc_b2left_40 : ∀ y ∈ Set.Icc (((14764:ℤ):ℝ)/1000) (((15000:ℤ):ℝ)/1000), 0 < (I ^ ((-1):ℤ) * riemannZeta (((1 - 1/4:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((-1):ℤ) = ((0:ℝ):ℂ) + (((-1):ℝ):ℂ) * I := (by rw [I_zpow_eq (-1) (-1) 3 (by norm_num), rot3])
  refine vertical_piece 10 (by norm_num) (1 - 1/4:ℝ) (((14764:ℤ):ℝ)/1000) (((15000:ℤ):ℝ)/1000) (I ^ ((-1):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 2.30258509371421 (lg_10).2 (by norm_num) 14.766116 14.764 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 7.89681146 rb_b2left_40 0.1778279410039 15.018739 15.101739 (pwh_10_3_4 (1 - 1/4:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.463479233863 0.616549796996 (by rw [hrot]; exact bv_b2left_14p764_3_10) (by rw [hrot]; exact bv_b2left_15_3_10) (by rw [lt_min_iff]; constructor <;> norm_num)

def yL_b2left : List ℤ := [-1000, -768, -471, -228, -63, 173, 350, 665, 980, 1401, 1822, 2384, 2946, 3508, 4070, 4632, 5194, 5756, 6318, 6880, 7442, 8004, 8566, 9128, 9690, 10252, 10814, 11376, 11938, 12359, 12780, 13095, 13410, 13646, 13823, 14000, 14132, 14264, 14396, 14528, 14764, 15000]
def zL_b2left : List ℤ := [3, 3, 3, 2, 2, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1, -1, -1]
noncomputable def yF_b2left (k : ℕ) : ℝ := ((yL_b2left.getD k 0 : ℤ) : ℝ) / 1000
def zF_b2left (k : ℕ) : ℤ := zL_b2left.getD k 0

theorem side_b2left : I * ∫ t in (-1:ℝ)..(15:ℝ), logDeriv zetaFactor (((1 - 1/4:ℝ):ℂ) + (t:ℂ) * I) =
    log (I ^ ((-4):ℤ) * I ^ ((-1):ℤ) * zetaFactor (((1 - 1/4:ℝ):ℂ) + (((15:ℝ)):ℂ) * I)) -
      log (I ^ ((-4):ℤ) * I ^ ((3):ℤ) * zetaFactor (((1 - 1/4:ℝ):ℂ) + (((-1:ℝ)):ℂ) * I)) -
      ((((-1) - (3) : ℤ)) : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  have h := vertical_side (1 - 1/4:ℝ) (by norm_num) yF_b2left zF_b2left (-4) 40 (list_mono yL_b2left 1000 (by norm_num) 41 (by decide)) (by decide) (fun t _ => u1_left _ t (by norm_num))
    (fun k hk => by interval_cases k; exacts [pc_b2left_0, pc_b2left_1, pc_b2left_2, pc_b2left_3, pc_b2left_4, pc_b2left_5, pc_b2left_6, pc_b2left_7, pc_b2left_8, pc_b2left_9, pc_b2left_10, pc_b2left_11, pc_b2left_12, pc_b2left_13, pc_b2left_14, pc_b2left_15, pc_b2left_16, pc_b2left_17, pc_b2left_18, pc_b2left_19, pc_b2left_20, pc_b2left_21, pc_b2left_22, pc_b2left_23, pc_b2left_24, pc_b2left_25, pc_b2left_26, pc_b2left_27, pc_b2left_28, pc_b2left_29, pc_b2left_30, pc_b2left_31, pc_b2left_32, pc_b2left_33, pc_b2left_34, pc_b2left_35, pc_b2left_36, pc_b2left_37, pc_b2left_38, pc_b2left_39, pc_b2left_40])
  have e0 : yF_b2left 0 = -1 := by norm_num [yF_b2left, yL_b2left]
  have e1 : yF_b2left (40 + 1) = 15 := by norm_num [yF_b2left, yL_b2left]
  have f0 : zF_b2left 0 = 3 := rfl
  have f1 : zF_b2left 40 = -1 := rfl
  rw [e0, e1, f0, f1] at h
  exact h

theorem nz_b2left : ∀ t ∈ Set.Icc (-1:ℝ) (15:ℝ), riemannZeta (((1 - 1/4:ℝ):ℂ) + (t:ℂ) * I) ≠ 0 := by
  have h := cover yF_b2left (fun t => riemannZeta (((1 - 1/4:ℝ):ℂ) + (t:ℂ) * I) ≠ 0) 40 (list_mono yL_b2left 1000 (by norm_num) 41 (by decide))
    (fun k hk t ht => by interval_cases k; exacts [zeta_ne_of_re_pos (pc_b2left_0 t ht), zeta_ne_of_re_pos (pc_b2left_1 t ht), zeta_ne_of_re_pos (pc_b2left_2 t ht), zeta_ne_of_re_pos (pc_b2left_3 t ht), zeta_ne_of_re_pos (pc_b2left_4 t ht), zeta_ne_of_re_pos (pc_b2left_5 t ht), zeta_ne_of_re_pos (pc_b2left_6 t ht), zeta_ne_of_re_pos (pc_b2left_7 t ht), zeta_ne_of_re_pos (pc_b2left_8 t ht), zeta_ne_of_re_pos (pc_b2left_9 t ht), zeta_ne_of_re_pos (pc_b2left_10 t ht), zeta_ne_of_re_pos (pc_b2left_11 t ht), zeta_ne_of_re_pos (pc_b2left_12 t ht), zeta_ne_of_re_pos (pc_b2left_13 t ht), zeta_ne_of_re_pos (pc_b2left_14 t ht), zeta_ne_of_re_pos (pc_b2left_15 t ht), zeta_ne_of_re_pos (pc_b2left_16 t ht), zeta_ne_of_re_pos (pc_b2left_17 t ht), zeta_ne_of_re_pos (pc_b2left_18 t ht), zeta_ne_of_re_pos (pc_b2left_19 t ht), zeta_ne_of_re_pos (pc_b2left_20 t ht), zeta_ne_of_re_pos (pc_b2left_21 t ht), zeta_ne_of_re_pos (pc_b2left_22 t ht), zeta_ne_of_re_pos (pc_b2left_23 t ht), zeta_ne_of_re_pos (pc_b2left_24 t ht), zeta_ne_of_re_pos (pc_b2left_25 t ht), zeta_ne_of_re_pos (pc_b2left_26 t ht), zeta_ne_of_re_pos (pc_b2left_27 t ht), zeta_ne_of_re_pos (pc_b2left_28 t ht), zeta_ne_of_re_pos (pc_b2left_29 t ht), zeta_ne_of_re_pos (pc_b2left_30 t ht), zeta_ne_of_re_pos (pc_b2left_31 t ht), zeta_ne_of_re_pos (pc_b2left_32 t ht), zeta_ne_of_re_pos (pc_b2left_33 t ht), zeta_ne_of_re_pos (pc_b2left_34 t ht), zeta_ne_of_re_pos (pc_b2left_35 t ht), zeta_ne_of_re_pos (pc_b2left_36 t ht), zeta_ne_of_re_pos (pc_b2left_37 t ht), zeta_ne_of_re_pos (pc_b2left_38 t ht), zeta_ne_of_re_pos (pc_b2left_39 t ht), zeta_ne_of_re_pos (pc_b2left_40 t ht)])
  have e0 : yF_b2left 0 = -1 := by norm_num [yF_b2left, yL_b2left]
  have e1 : yF_b2left (40 + 1) = 15 := by norm_num [yF_b2left, yL_b2left]
  rw [e0, e1] at h
  exact h

end Cert
end ZB
end RHV6Fresh
