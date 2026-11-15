/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Base
/-!
# Certificat (V2), côté b1left (b1), angles 5

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

lemma cs_b1left_v19p765_7 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7235931910558:ℝ):ℂ) + (((-0.6902266974391):ℝ):ℂ) * I)‖ ≤ 0.00000015729 := by
  have hl := lg_7
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.46091408580261583 38.46091410556765536 (-0.7618023) 0.00000005728 0.7235931910558 (-0.6902266974391) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p765_8 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9665292882726):ℝ):ℂ) + ((0.2565562991903:ℝ):ℂ) * I)‖ ≤ 0.00000013529 := by
  have hl := lg_8
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.1001620558885 41.100162085536 2.8821351 0.00000003528 (-0.9665292882726) 0.2565562991903 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p765_9 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8503462458393:ℝ):ℂ) + ((0.5262235857381:ℝ):ℂ) * I)‖ ≤ 0.0000001303 := by
  have hl := lg_9
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.42814376077472292 43.42814378053976245 0.5541534 0.00000003029 0.8503462458393 0.5262235857381 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p765_10 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0424863344679:ℝ):ℂ) + (((-0.9990970480305):ℝ):ℂ) * I)‖ ≤ 0.00000012702 := by
  have hl := lg_10
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.510594347613840885 45.51059437726136065 (-1.5282972) 0.00000002701 0.0424863344679 (-0.9990970480305) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p765_11 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9636346701428):ℝ):ℂ) + ((0.2672231693789:ℝ):ℂ) * I)‖ ≤ 0.00000012367 := by
  have hl := lg_11
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.394400051446304745 47.394400081093844275 2.8710824 0.00000002366 (-0.9636346701428) 0.2672231693789 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p765_12 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4072982196874:ℝ):ℂ) + ((0.9132952207471:ℝ):ℂ) * I)‖ ≤ 0.00000013981 := by
  have hl := lg_12
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.11417991764636146 49.114179947293881225 1.1513025 0.0000000398 0.4072982196874 0.9132952207471 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p765_13 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.908656348364:ℝ):ℂ) + (((-0.4175447767341):ℝ):ℂ) * I)‖ ≤ 0.00000012264 := by
  have hl := lg_13
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.6962240348138005 50.69622406446134003 (-0.4307416) 0.00000002263 0.908656348364 (-0.4175447767341) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p765_14 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3190144047491):ℝ):ℂ) + (((-0.947749866558):ℝ):ℂ) * I)‖ ≤ 0.00000015302 := by
  have hl := lg_14
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.16096810443211583 52.16096813407965536 (-1.8954857) 0.00000005301 (-0.3190144047491) (-0.947749866558) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p765_15 : ‖exp (-((((((19765:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9931004571418):ℝ):ℂ) + ((0.1172667113006:ℝ):ℂ) * I)‖ ≤ 0.00000015526 := by
  have hl := lg_15
  refine (ecis_approx ((((19765:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.524612209371702345 53.524612239019241875 3.0240555 0.00000005525 (-0.9931004571418) 0.1172667113006 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_2 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.309270498384:ℝ):ℂ) + (((-0.9509741104937):ℝ):ℂ) * I)‖ ≤ 0.00000014483 := by
  have hl := lg_2
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.8227410695426 13.8227410795136 (-1.2563705) 0.00000004482 0.309270498384 (-0.9509741104937) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_3 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9965887143527):ℝ):ℂ) + (((-0.0825283824934):ℝ):ℂ) * I)‖ ≤ 0.00000014388 := by
  have hl := lg_3
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.908526255435606488 21.90852626540662643 (-3.0589703) 0.00000004387 (-0.9965887143527) (-0.0825283824934) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_4 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8087034588259):ℝ):ℂ) + (((-0.5882165550462):ℝ):ℂ) * I)‖ ≤ 0.00000013032 := by
  have hl := lg_4
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.6454821390852 27.6454821590272 (-2.5127409) 0.00000003031 (-0.8087034588259) (-0.5882165550462) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_5 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7778968839027:ℝ):ℂ) + (((-0.6283919461725):ℝ):ℂ) * I)‖ ≤ 0.00000012345 := by
  have hl := lg_5
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.095410839393155878 32.09541085933517582 (-0.6794843) 0.00000002344 0.7778968839027 (-0.6283919461725) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_6 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3866978371806):ℝ):ℂ) + ((0.9222064751002:ℝ):ℂ) * I)‖ ≤ 0.00000011811 := by
  have hl := lg_6
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.731267324978206488 35.73126734492022643 1.9678445 0.0000000181 (-0.3866978371806) 0.9222064751002 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_7 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4480366526531:ℝ):ℂ) + (((-0.8940151888415):ℝ):ℂ) * I)‖ ≤ 0.00000015897 := by
  have hl := lg_7
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.805340182093385524 38.805340202035425408 (-1.1062283) 0.00000005896 0.4480366526531 (-0.8940151888415) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_8 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8094868327734):ℝ):ℂ) + ((0.5871380310569:ℝ):ℂ) * I)‖ ≤ 0.00000014164 := by
  have hl := lg_8
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.4682232086278 41.4682232385408 2.5140739 0.00000004163 (-0.8094868327734) 0.5871380310569 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_9 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9863781497183:ℝ):ℂ) + ((0.1644936040043:ℝ):ℂ) * I)‖ ≤ 0.0000001394 := by
  have hl := lg_9
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.817052510871212976 43.81705253081325286 0.1652446 0.00000003939 0.9863781497183 0.1644936040043 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_10 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.357003915077):ℝ):ℂ) + (((-0.9341028875971):ℝ):ℂ) * I)‖ ≤ 0.00000014134 := by
  have hl := lg_10
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.918151908935755878 45.91815193884877582 (-1.9358548) 0.00000004133 (-0.357003915077) (-0.9341028875971) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_11 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7680935619918):ℝ):ℂ) + ((0.640337629683:ℝ):ℂ) * I)‖ ≤ 0.00000014286 := by
  have hl := lg_11
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.818827514593585086 47.81882754450662497 2.4466549 0.00000004285 (-0.7680935619918) 0.640337629683 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_12 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7574002495228:ℝ):ℂ) + ((0.6529508879103:ℝ):ℂ) * I)‖ ≤ 0.00000016293 := by
  have hl := lg_12
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.554008394520806488 49.55400842443382643 0.711474 0.00000006292 0.7574002495228 0.6529508879103 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_13 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6334925549765:ℝ):ℂ) + (((-0.7737487853233):ℝ):ℂ) * I)‖ ≤ 0.00000014344 := by
  have hl := lg_13
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.1502200709464614 51.150220100859501284 (-0.8847376) 0.00000004343 0.6334925549765 (-0.7737487853233) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_14 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7116207801125):ℝ):ℂ) + (((-0.7025637802267):ℝ):ℂ) * I)‖ ≤ 0.00000012413 := by
  have hl := lg_14
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.628081251635985524 52.628081281549025408 (-2.3625988) 0.00000002412 (-0.7116207801125) (-0.7025637802267) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_15 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8271034225996):ℝ):ℂ) + ((0.5620497560386:ℝ):ℂ) * I)‖ ≤ 0.00000016014 := by
  have hl := lg_15
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.003937094828762366 54.00393712474180225 2.5447307 0.00000006013 (-0.8271034225996) 0.5620497560386 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_16 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3080025755005:ℝ):ℂ) + ((0.9513855230584:ℝ):ℂ) * I)‖ ≤ 0.00000015345 := by
  have hl := lg_16
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.2909642781704 55.2909643180544 1.2577035 0.00000005344 0.3080025755005 0.9513855230584 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_17 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9988130599961:ℝ):ℂ) + ((0.0487080196802:ℝ):ℂ) * I)‖ ≤ 0.00000016172 := by
  have hl := lg_17
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.499940486433726828 56.49994052631774677 0.0487273 0.00000006171 0.9988130599961 0.0487080196802 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_18 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.461486909423:ℝ):ℂ) + (((-0.8871470184987):ℝ):ℂ) * I)‖ ≤ 0.00000014573 := by
  have hl := lg_18
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.639793580413812976 57.63979361032685286 (-1.0911258) 0.00000004572 0.461486909423 (-0.8871470184987) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_19 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5634352901888):ℝ):ℂ) + (((-0.8261601986058):ℝ):ℂ) * I)‖ ≤ 0.00000015765 := by
  have hl := lg_19
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.718002106985637026 58.718002136898696852 (-2.1693344) 0.00000005764 (-0.5634352901888) (-0.8261601986058) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p942_20 : ‖exp (-((((((19942:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9987184458092):ℝ):ℂ) + ((0.0506109220306:ℝ):ℂ) * I)‖ ≤ 0.00000014658 := by
  have hl := lg_20
  refine (ecis_approx ((((19942:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.740892978478355878 59.74089301836237582 3.0909601 0.00000004657 (-0.9987184458092) 0.0506109220306 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_2 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1905661438836:ℝ):ℂ) + (((-0.981674357822):ℝ):ℂ) * I)‖ ≤ 0.00000011617 := by
  have hl := lg_2
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.9454281204557 13.9454281305152 (-1.3790575) 0.00000001616 0.1905661438836 (-0.981674357822) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_3 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9937533100675):ℝ):ℂ) + ((0.1115990962093:ℝ):ℂ) * I)‖ ≤ 0.00000011184 := by
  have hl := lg_3
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.102980630483851516 22.102980640543371635 3.0297606 0.00000001183 (-0.9937533100675) 0.1115990962093 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_4 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9273690895602):ℝ):ℂ) + (((-0.3741477937571):ℝ):ℂ) * I)‖ ≤ 0.00000013233 := by
  have hl := lg_4
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.8908562409114 27.8908562610304 (-2.758115) 0.00000003232 (-0.9273690895602) (-0.3741477937571) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_5 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5699471437173:ℝ):ℂ) + (((-0.8216813575642):ℝ):ℂ) * I)‖ ≤ 0.00000013404 := by
  have hl := lg_5
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.380281349801970871 32.38028136992099099 (-0.9643548) 0.00000003403 0.5699471437173 (-0.8216813575642) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_6 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0798217649939):ℝ):ℂ) + ((0.9968091521615:ℝ):ℂ) * I)‖ ≤ 0.000000128 := by
  have hl := lg_6
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.048408750939551516 36.048408771058571635 1.6507031 0.00000002799 (-0.0798217649939) 0.9968091521615 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_7 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1198531122304:ℝ):ℂ) + (((-0.9927916354848):ℝ):ℂ) * I)‖ ≤ 0.00000015544 := by
  have hl := lg_7
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.149766278384155218 39.149766298503195456 (-1.4506544) 0.00000005543 0.1198531122304 (-0.9927916354848) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_8 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.544016440587):ℝ):ℂ) + ((0.8390745570941:ℝ):ℂ) * I)‖ ≤ 0.0000001413 := by
  have hl := lg_8
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.8362843613671 41.8362843915456 2.1460128 0.00000004129 (-0.544016440587) 0.8390745570941 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_9 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9750912849468:ℝ):ℂ) + (((-0.2218039359905):ℝ):ℂ) * I)‖ ≤ 0.00000013084 := by
  have hl := lg_9
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.205961260967703032 44.20596128108674327 (-0.2236641) 0.00000003083 0.9750912849468 (-0.2218039359905) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_10 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6980108896223):ℝ):ℂ) + (((-0.7160871441):ℝ):ℂ) * I)‖ ≤ 0.00000015019 := by
  have hl := lg_10
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.325709470257670871 46.32570950043619099 (-2.3434123) 0.00000005018 (-0.6980108896223) (-0.7160871441) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_11 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4362537839764):ℝ):ℂ) + ((0.899823669372:ℝ):ℂ) * I)‖ ≤ 0.0000001505 := by
  have hl := lg_11
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.243254977740865427 48.243255007919405665 2.0222275 0.00000005049 (-0.4362537839764) 0.899823669372 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_12 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9633306583666:ℝ):ℂ) + ((0.2683170562059:ℝ):ℂ) * I)‖ ≤ 0.00000014415 := by
  have hl := lg_12
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.993836871395251516 49.993836901573771635 0.2716456 0.00000004414 0.9633306583666 0.2683170562059 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_13 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2299853475498:ℝ):ℂ) + (((-0.9731940915934):ℝ):ℂ) * I)‖ ≤ 0.00000015037 := by
  have hl := lg_13
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.6042161070791223 51.604216137257662538 (-1.3387337) 0.00000005036 0.2299853475498 (-0.9731940915934) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_14 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9517581763958):ℝ):ℂ) + (((-0.3068491053525):ℝ):ℂ) * I)‖ ≤ 0.00000015861 := by
  have hl := lg_14
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.095194398839855218 53.095194429018395456 (-2.829712) 0.0000000586 (-0.9517581763958) (-0.3068491053525) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_15 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.474687963696):ℝ):ℂ) + ((0.8801541553142:ℝ):ℂ) * I)‖ ≤ 0.00000014586 := by
  have hl := lg_15
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.483261980285822387 54.483262010464362625 2.0654058 0.00000004585 (-0.474687963696) 0.8801541553142 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_16 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7200268617128:ℝ):ℂ) + ((0.6939461927355:ℝ):ℂ) * I)‖ ≤ 0.00000015746 := by
  have hl := lg_16
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.7817124818228 55.7817125220608 0.7669553 0.00000005745 0.7200268617128 0.6939461927355 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_17 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8992468876669:ℝ):ℂ) + (((-0.4374414646801):ℝ):ℂ) * I)‖ ≤ 0.00000012378 := by
  have hl := lg_17
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.001419248147635646 57.001419288385655765 (-0.4527515) 0.00000002377 0.8992468876669 (-0.4374414646801) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_18 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.031919850319):ℝ):ℂ) + (((-0.9994904317478):ℝ):ℂ) * I)‖ ≤ 0.000000147 := by
  have hl := lg_18
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.151389381423403032 58.15138941160194327 (-1.6027216) 0.00000004699 (-0.031919850319) (-0.9994904317478) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_19 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8999713418375):ℝ):ℂ) + (((-0.4359490609634):ℝ):ℂ) * I)‖ ≤ 0.00000015847 := by
  have hl := lg_19
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.239167806160065757 59.239167836338626114 (-2.6905001) 0.00000005846 (-0.8999713418375) (-0.4359490609634) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p119_20 : ‖exp (-((((((20119:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8359816270115):ℝ):ℂ) + ((0.5487574320531:ℝ):ℂ) * I)‖ ≤ 0.00000015917 := by
  have hl := lg_20
  refine (ecis_approx ((((20119:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.271137590713370871 60.27113763095139099 2.5607155 0.00000005916 (-0.8359816270115) 0.5487574320531 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_2 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1000756243614:ℝ):ℂ) + (((-0.9949798336693):ℝ):ℂ) * I)‖ ≤ 0.00000014404 := by
  have hl := lg_2
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.0369235482553 14.0369235583808 (-1.4705529) 0.00000004403 0.1000756243614 (-0.9949798336693) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_3 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9671952771636):ℝ):ℂ) + ((0.2540340441214:ℝ):ℂ) * I)‖ ≤ 0.00000013398 := by
  have hl := lg_3
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.247997452553729164 22.247997462679249415 2.8847438 0.00000003397 (-0.9671952771636) 0.2540340441214 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_4 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9799697585992):ℝ):ℂ) + (((-0.1991463580056):ℝ):ℂ) * I)‖ ≤ 0.00000013222 := by
  have hl := lg_4
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.0738470965106 28.0738471167616 (-2.9411059) 0.00000003221 (-0.9799697585992) (-0.1991463580056) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_5 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3838810541941:ℝ):ℂ) + (((-0.9233825514005):ℝ):ℂ) * I)‖ ≤ 0.00000013854 := by
  have hl := lg_5
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.592727154174646459 32.59272717442566671 (-1.1768006) 0.00000003853 0.3838810541941 (-0.9233825514005) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_6 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.155966178622:ℝ):ℂ) + ((0.9877623960883:ℝ):ℂ) * I)‖ ≤ 0.00000014228 := by
  have hl := lg_6
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.284921000809029164 36.284921021060049415 1.4141908 0.00000004227 0.155966178622 0.9877623960883 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_7 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1362927506895):ℝ):ℂ) + (((-0.9906686055937):ℝ):ℂ) * I)‖ ≤ 0.0000001251 := by
  have hl := lg_7
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.406626417990830922 39.406626438241871424 (-1.7075146) 0.00000002509 (-0.1362927506895) (-0.9906686055937) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_8 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.296217688927):ℝ):ℂ) + ((0.9551204535372:ℝ):ℂ) * I)‖ ≤ 0.0000001249 := by
  have hl := lg_8
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.1107706447659 42.1107706751424 1.8715265 0.00000002489 (-0.296217688927) 0.9551204535372 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_9 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8709333631088:ℝ):ℂ) + (((-0.4914011365717):ℝ):ℂ) * I)‖ ≤ 0.00000014516 := by
  have hl := lg_9
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.495994905107458328 44.49599492535849883 (-0.5136978) 0.00000004515 0.8709333631088 (-0.4914011365717) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_10 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8803299286364):ℝ):ℂ) + (((-0.4743619047211):ℝ):ℂ) * I)‖ ≤ 0.00000014784 := by
  have hl := lg_10
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.629650702429946459 46.62965073280646671 (-2.6473536) 0.00000004783 (-0.8803299286364) (-0.4743619047211) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_11 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1345001118777):ℝ):ℂ) + ((0.9909135784236:ℝ):ℂ) * I)‖ ≤ 0.0000001266 := by
  have hl := lg_11
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.559777153647311783 48.559777184023852285 1.7057053 0.00000002659 (-0.1345001118777) 0.9909135784236 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_12 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9984120772696:ℝ):ℂ) + (((-0.0563322639541):ℝ):ℂ) * I)‖ ≤ 0.00000012202 := by
  have hl := lg_12
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.321844549064329164 50.321844579440849415 (-0.0563621) 0.00000002201 0.9984120772696 (-0.0563322639541) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_13 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1063094019328):ℝ):ℂ) + (((-0.9943330986446):ℝ):ℂ) * I)‖ ≤ 0.00000013529 := by
  have hl := lg_13
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.9427894221611067 51.942789452537647202 (-1.677307) 0.00000003528 (-0.1063094019328) (-0.9943330986446) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_14 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993348659834):ℝ):ℂ) + ((0.036466766073:ℝ):ℂ) * I)‖ ≤ 0.00000013202 := by
  have hl := lg_14
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.443549966246130922 53.443549996622671424 3.1051178 0.00000003201 (-0.9993348659834) 0.036466766073 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_15 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1367172396615):ℝ):ℂ) + ((0.9906101132023:ℝ):ℂ) * I)‖ ≤ 0.0000001579 := by
  have hl := lg_15
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.840724606728375623 54.840724637104916125 1.7079431 0.00000005789 (-0.1367172396615) 0.9906101132023 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_16 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9206814198293:ℝ):ℂ) + ((0.3903149025865:ℝ):ℂ) * I)‖ ≤ 0.00000016892 := by
  have hl := lg_16
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.1476941930212 56.1476942335232 0.4009736 0.00000006891 0.9206814198293 0.3903149025865 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_17 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6772809895498:ℝ):ℂ) + (((-0.7357244465114):ℝ):ℂ) * I)‖ ≤ 0.00000015521 := by
  have hl := lg_17
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.375403409425804934 57.375403449927825185 (-0.8267357) 0.0000000552 0.6772809895498 (-0.7357244465114) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_18 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4017750210408):ℝ):ℂ) + (((-0.9157384083156):ℝ):ℂ) * I)‖ ≤ 0.00000011914 := by
  have hl := lg_18
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.532918453362758328 58.53291848373929883 (-1.9842507) 0.00000001913 (-0.4017750210408) (-0.9157384083156) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_19 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9980520889238):ℝ):ℂ) + (((-0.0623861142202):ℝ):ℂ) * I)‖ ≤ 0.00000011708 := by
  have hl := lg_19
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.627833751307097353 59.627833781683658106 (-3.079166) 0.00000001707 (-0.9980520889238) (-0.0623861142202) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_20 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5600800904174):ℝ):ℂ) + ((0.8284384662175:ℝ):ℂ) * I)‖ ≤ 0.00000012113 := by
  have hl := lg_20
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.666574250685246459 60.66657429118726671 2.1652788 0.00000002112 (-0.5600800904174) 0.8284384662175 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_21 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3834852571856:ℝ):ℂ) + ((0.9235469980035:ℝ):ℂ) * I)‖ ≤ 0.00000012914 := by
  have hl := lg_21
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.654623870544560086 61.654623900921120839 1.1772292 0.00000002913 0.3834852571856 0.9235469980035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_22 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9724788680672:ℝ):ℂ) + ((0.2329910967456:ℝ):ℂ) * I)‖ ≤ 0.00000016991 := by
  have hl := lg_22
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.596700701902611783 62.596700742404652285 0.2351523 0.0000000699 0.9724788680672 0.2329910967456 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_23 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7868919170064:ℝ):ℂ) + (((-0.6170908449734):ℝ):ℂ) * I)‖ ≤ 0.00000012609 := by
  have hl := lg_23
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.496893345724550866 63.496893386226611619 (-0.6650403) 0.00000002608 0.7868919170064 (-0.6170908449734) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_24 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0438672453834:ℝ):ℂ) + (((-0.999037369062):ℝ):ℂ) * I)‖ ≤ 0.00000016604 := by
  have hl := lg_24
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.358768097319629164 64.358768137821649415 (-1.526915) 0.00000006603 0.0438672453834 (-0.999037369062) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_25 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.705270743352):ℝ):ℂ) + (((-0.7089380639711):ℝ):ℂ) * I)‖ ≤ 0.00000016346 := by
  have hl := lg_25
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.185454308349292918 65.18545434885133342 (-2.3536013) 0.00000006345 (-0.705270743352) (-0.7089380639711) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_26 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999803604963):ℝ):ℂ) + ((0.0062672122628:ℝ):ℂ) * I)‖ ≤ 0.00000013196 := by
  have hl := lg_26
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 65.9797129704164067 65.979713010918447202 3.1353254 0.00000003195 (-0.9999803604963) 0.0062672122628 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_27 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7175300175321):ℝ):ℂ) + ((0.6965275830242:ℝ):ℂ) * I)‖ ≤ 0.00000012133 := by
  have hl := lg_27
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.743992357661187492 66.743992388037748245 2.371046 0.00000002132 (-0.7175300175321) 0.6965275830242 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_28 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0637252637784):ℝ):ℂ) + ((0.9979674798089:ℝ):ℂ) * I)‖ ≤ 0.00000016449 := by
  have hl := lg_28
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.480473514501430922 67.480473555003471424 1.6345648 0.00000006448 (-0.0637252637784) 0.9979674798089 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_29 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6026883729273:ℝ):ℂ) + ((0.7979766444817:ℝ):ℂ) * I)‖ ≤ 0.00000014699 := by
  have hl := lg_29
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.191107831999459692 68.191107872501520445 0.9239305 0.00000004698 0.6026883729273 0.7979766444817 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p251_30 : ‖exp (-((((((20251:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9719550225455:ℝ):ℂ) + ((0.2351668219555:ℝ):ℂ) * I)‖ ≤ 0.00000012401 := by
  have hl := lg_30
  refine (ecis_approx ((((20251:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.877648154983675623 68.877648195485716125 0.2373902 0.000000024 0.9719550225455 0.2351668219555 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_2 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.008747815221:ℝ):ℂ) + (((-0.9999617371323):ℝ):ℂ) * I)‖ ≤ 0.00000013832 := by
  have hl := lg_2
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.1284189760549 14.1284189862464 (-1.5620484) 0.00000003831 0.008747815221 (-0.9999617371323) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_3 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9203328325859):ℝ):ℂ) + ((0.3911361363017:ℝ):ℂ) * I)‖ ≤ 0.00000015411 := by
  have hl := lg_3
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.393014274623606812 22.393014284815127195 2.7397269 0.0000000541 (-0.9203328325859) 0.3911361363017 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_4 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998469493906):ℝ):ℂ) + (((-0.0174950607046):ℝ):ℂ) * I)‖ ≤ 0.00000014379 := by
  have hl := lg_4
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.2568379521098 28.2568379724928 (-3.1240967) 0.00000004378 (-0.9998469493906) (-0.0174950607046) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_5 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1805542434778:ℝ):ℂ) + (((-0.9835650284359):ℝ):ℂ) * I)‖ ≤ 0.00000014305 := by
  have hl := lg_5
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.805172958547322047 32.80517297893034243 (-1.3892464) 0.00000004304 0.1805542434778 (-0.9835650284359) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_6 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3830701764543:ℝ):ℂ) + ((0.9237192430123:ℝ):ℂ) * I)‖ ≤ 0.000000128 := by
  have hl := lg_6
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.521433250678506812 36.521433271061527195 1.1776786 0.00000002799 0.3830701764543 0.9237192430123 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_7 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3834956437498):ℝ):ℂ) + (((-0.9235426851109):ℝ):ℂ) * I)‖ ≤ 0.00000013492 := by
  have hl := lg_7
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.663486557597506626 39.663486577980547392 (-1.9643747) 0.00000003491 (-0.3834956437498) (-0.9235426851109) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_8 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0262408607708):ℝ):ℂ) + ((0.9996556493242:ℝ):ℂ) * I)‖ ≤ 0.00000012211 := by
  have hl := lg_8
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.3852569281647 42.3852569587392 1.5970402 0.0000000221 (-0.0262408607708) 0.9996556493242 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_9 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6940251228025:ℝ):ℂ) + (((-0.7199507822893):ℝ):ℂ) * I)‖ ≤ 0.00000011939 := by
  have hl := lg_9
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.786028549247213624 44.78602856963025439 (-0.8037314) 0.00000001938 0.6940251228025 (-0.7199507822893) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_10 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9819479391184):ℝ):ℂ) + (((-0.1891513799152):ℝ):ℂ) * I)‖ ≤ 0.00000011567 := by
  have hl := lg_10
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.933591934602222047 46.93359196517674243 (-2.9512948) 0.00000001566 (-0.9819479391184) (-0.1891513799152) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_11 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1806165027823:ℝ):ℂ) + ((0.9835535973818:ℝ):ℂ) * I)‖ ≤ 0.0000001279 := by
  have hl := lg_11
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.876299329553758139 48.876299360128298905 1.3891831 0.00000002789 0.1806165027823 0.9835535973818 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_12 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9270349259856:ℝ):ℂ) + (((-0.3749749938369):ℝ):ℂ) * I)‖ ≤ 0.00000013072 := by
  have hl := lg_12
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.649852226733406812 50.649852257307927195 (-0.3843698) 0.00000003071 0.9270349259856 (-0.3749749938369) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_13 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4305336738937):ℝ):ℂ) + (((-0.9025745152837):ℝ):ℂ) * I)‖ ≤ 0.00000012021 := by
  have hl := lg_13
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.2813627372430911 52.281362767817631866 (-2.0158803) 0.0000000202 (-0.4305336738937) (-0.9025745152837) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_14 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9268620940054):ℝ):ℂ) + ((0.3754019959214:ℝ):ℂ) * I)‖ ≤ 0.00000013098 := by
  have hl := lg_14
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.791905533652406626 53.791905564226947392 2.7567622 0.00000003097 (-0.9268620940054) 0.3754019959214 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_15 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2185378267555:ℝ):ℂ) + ((0.9758284778981:ℝ):ℂ) * I)‖ ≤ 0.00000013146 := by
  have hl := lg_15
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.198187233170928859 55.198187263745469625 1.3504805 0.00000003145 0.2185378267555 0.9758284778981 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_16 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9993878494313:ℝ):ℂ) + ((0.0349846596251:ℝ):ℂ) * I)‖ ≤ 0.00000016041 := by
  have hl := lg_16
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.5136759042196 56.5136759449856 0.0349918 0.0000000604 0.9993878494313 0.0349846596251 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_17 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3616867789296:ℝ):ℂ) + (((-0.932299669606):ℝ):ℂ) * I)‖ ≤ 0.00000014687 := by
  have hl := lg_17
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.749387570703974222 57.749387611469994605 (-1.2007198) 0.00000004686 0.3616867789296 (-0.932299669606) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_18 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7138520313711):ℝ):ℂ) + (((-0.700296563808):ℝ):ℂ) * I)‖ ≤ 0.00000013933 := by
  have hl := lg_18
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.914447525302113624 58.91444755587665439 (-2.3657798) 0.00000003932 (-0.7138520313711) (-0.700296563808) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_19 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9472542942109):ℝ):ℂ) + ((0.3204829198298:ℝ):ℂ) * I)‖ ≤ 0.00000015525 := by
  have hl := lg_19
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.016499696454128949 60.016499727028690098 2.8153534 0.00000005524 (-0.9472542942109) 0.3204829198298 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_20 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1977340346987):ℝ):ℂ) + ((0.9802557072116:ℝ):ℂ) * I)‖ ≤ 0.00000016115 := by
  have hl := lg_20
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.062010910657122047 61.06201095142314243 1.7698421 0.00000006114 (-0.1977340346987) 0.9802557072116 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_21 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7141745497492:ℝ):ℂ) + ((0.6999676510315:ℝ):ℂ) * I)‖ ≤ 0.00000013959 := by
  have hl := lg_21
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.056500832221113438 62.056500862795674587 0.7753522 0.00000003958 0.7141745497492 0.6999676510315 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_22 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9850959635929:ℝ):ℂ) + (((-0.1720056467471):ℝ):ℂ) * I)‖ ≤ 0.0000001662 := by
  have hl := lg_22
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.004718305608658139 63.004718346374698905 (-0.1728653) 0.00000006619 0.9850959635929 (-0.1720056467471) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_23 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4722757555688:ℝ):ℂ) + (((-0.8814508555228):ℝ):ℂ) * I)‖ ≤ 0.00000015108 := by
  have hl := lg_23
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.910778582089947178 63.910778622856008327 (-1.0789255) 0.00000005107 0.4722757555688 (-0.8814508555228) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_24 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3668511159825):ℝ):ℂ) + (((-0.9302796669281):ℝ):ℂ) * I)‖ ≤ 0.00000016902 := by
  have hl := lg_24
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.778271202788306812 64.778271243554327195 (-1.9464182) 0.00000006901 (-0.3668511159825) (-0.9302796669281) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_25 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9348003657852):ℝ):ℂ) + (((-0.3551735856721):ℝ):ℂ) * I)‖ ≤ 0.00000015472 := by
  have hl := lg_25
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.610345917094644094 65.61034595786068486 (-2.7784929) 0.00000005471 (-0.9348003657852) (-0.3551735856721) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_26 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9063062061509):ℝ):ℂ) + ((0.422621651798:ℝ):ℂ) * I)‖ ≤ 0.00000016569 := by
  have hl := lg_26
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.4097817132979911 66.409781754064031866 2.7052566 0.00000006568 (-0.9063062061509) 0.422621651798 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_27 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3571353398192):ℝ):ℂ) + ((0.9340526479004:ℝ):ℂ) * I)‖ ≤ 0.00000015512 := by
  have hl := lg_27
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.179042823870820436 67.179042854445381585 1.9359955 0.00000005511 (-0.3571353398192) 0.9340526479004 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_28 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3672796137121:ℝ):ℂ) + ((0.9301105769485:ℝ):ℂ) * I)‖ ≤ 0.00000016928 := by
  have hl := lg_28
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.920324509707306626 67.920324550473347392 1.1947138 0.00000006927 0.3672796137121 0.9301105769485 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_29 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8872499203804:ℝ):ℂ) + ((0.4612890403911:ℝ):ℂ) * I)‖ ≤ 0.00000014323 := by
  have hl := lg_29
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.635590881420423036 68.635590922186484185 0.4794475 0.00000004322 0.8872499203804 0.4612890403911 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p383_30 : ‖exp (-((((((20383:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9777028684296:ℝ):ℂ) + (((-0.2099930976595):ℝ):ℂ) * I)‖ ≤ 0.00000016976 := by
  have hl := lg_30
  refine (ecis_approx ((((20383:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.326606209225828859 69.326606249991869625 (-0.2115679) 0.00000006975 0.9777028684296 (-0.2099930976595) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_2 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0598378067057):ℝ):ℂ) + (((-0.9982081130147):ℝ):ℂ) * I)‖ ≤ 0.0000001428 := by
  have hl := lg_2
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.1970405469046 14.1970405571456 (-1.6306699) 0.00000004279 (-0.0598378067057) (-0.9982081130147) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_3 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8724375874244):ℝ):ℂ) + ((0.4887255425689:ℝ):ℂ) * I)‖ ≤ 0.00000013756 := by
  have hl := lg_3
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.501776891176015048 22.50177690141703553 2.6309643 0.00000003755 (-0.8724375874244) 0.4887255425689 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_4 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9928388607763):ℝ):ℂ) + ((0.1194612744391:ℝ):ℂ) * I)‖ ≤ 0.0000001421 := by
  have hl := lg_4
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.3940810938092 28.3940811142912 3.0218454 0.00000004209 (-0.9928388607763) 0.1194612744391 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_5 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0222136995032:ℝ):ℂ) + (((-0.9997532453332):ℝ):ℂ) * I)‖ ≤ 0.00000012409 := by
  have hl := lg_5
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.964507311826828738 32.96450733230884922 (-1.5485808) 0.00000002408 0.0222136995032 (-0.9997532453332) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_6 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5400545533994:ℝ):ℂ) + ((0.8416300133387:ℝ):ℂ) * I)‖ ≤ 0.0000001155 := by
  have hl := lg_6
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.698817438080615048 36.69881745856263553 1.0002944 0.00000001549 0.5400545533994 0.8416300133387 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_7 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5532189931833):ℝ):ℂ) + (((-0.8330358609162):ℝ):ℂ) * I)‖ ≤ 0.00000013972 := by
  have hl := lg_7
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.856131662302513404 39.856131682784554368 (-2.1570198) 0.00000003971 (-0.5532189931833) (-0.8330358609162) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_8 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1786565133987:ℝ):ℂ) + ((0.9839115052789:ℝ):ℂ) * I)‖ ≤ 0.00000012119 := by
  have hl := lg_8
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.5911216407138 42.5911216714368 1.3911755 0.00000002118 0.1786565133987 0.9839115052789 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_9 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5222947793843:ℝ):ℂ) + (((-0.8527650106729):ℝ):ℂ) * I)‖ ≤ 0.00000015259 := by
  have hl := lg_9
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.003553782352030096 45.00355380283407106 (-1.0212566) 0.00000005258 0.5222947793843 (-0.8527650106729) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_10 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9992910190016):ℝ):ℂ) + ((0.0376491532858:ℝ):ℂ) * I)‖ ≤ 0.00000013203 := by
  have hl := lg_10
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.161547858731428738 47.16154788945444922 3.1039346 0.00000003202 (-0.9992910190016) 0.0376491532858 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_11 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4068515696455:ℝ):ℂ) + ((0.9134942803745:ℝ):ℂ) * I)‖ ≤ 0.00000013478 := by
  have hl := lg_11
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.113690961483592906 49.11369099220663387 1.1517915 0.00000003477 0.4068515696455 0.9134942803745 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_12 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8078062274947:ℝ):ℂ) + (((-0.5894481307297):ℝ):ℂ) * I)‖ ≤ 0.00000015829 := by
  have hl := lg_12
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.895857984985215048 50.89585801570823553 (-0.6303755) 0.00000005828 0.8078062274947 (-0.5894481307297) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_13 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6434632192978):ℝ):ℂ) + (((-0.7654770312653):ℝ):ℂ) * I)‖ ≤ 0.0000001339 := by
  have hl := lg_13
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.5352927235545794 52.535292754277620364 (-2.2698103) 0.00000003389 (-0.6434632192978) (-0.7654770312653) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_14 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7984396790839):ℝ):ℂ) + ((0.6020748116437:ℝ):ℂ) * I)‖ ≤ 0.00000015542 := by
  have hl := lg_14
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.053172209207113404 54.053172239930154368 2.4954955 0.00000005541 (-0.7984396790839) 0.6020748116437 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_15 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4692248809068:ℝ):ℂ) + ((0.8830787117454:ℝ):ℂ) * I)‖ ≤ 0.00000016163 := by
  have hl := lg_15
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.466284203002843786 55.46628423372588475 1.0823835 0.00000006162 0.4692248809068 0.8830787117454 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_16 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9714580331426:ℝ):ℂ) + (((-0.2372114875859):ℝ):ℂ) * I)‖ ≤ 0.00000016398 := by
  have hl := lg_16
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.7881621876184 56.7881622285824 (-0.2394944) 0.00000006397 0.9714580331426 (-0.2372114875859) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_17 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0894686341387:ℝ):ℂ) + (((-0.99598964026):ℝ):ℂ) * I)‖ ≤ 0.00000016803 := by
  have hl := lg_17
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.029875691662601188 58.02987573262662167 (-1.4812079) 0.00000006802 0.0894686341387 (-0.99598964026) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_18 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8824899732069):ℝ):ℂ) + (((-0.4703312099901):ℝ):ℂ) * I)‖ ≤ 0.00000013537 := by
  have hl := lg_18
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.200594329256630096 59.20059435997967106 (-2.6519266) 0.00000003536 (-0.8824899732069) (-0.4703312099901) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_19 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8151902384266):ℝ):ℂ) + ((0.5791932968521:ℝ):ℂ) * I)‖ ≤ 0.0000001165 := by
  have hl := lg_19
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.307999155314402646 60.307999186037464092 2.5238539 0.00000001649 (-0.8151902384266) 0.5791932968521 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_20 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0973771729094:ℝ):ℂ) + ((0.9952475502085:ℝ):ℂ) * I)‖ ≤ 0.00000016617 := by
  have hl := lg_20
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.358588405636028738 61.35858844660004922 1.4732646 0.00000006616 0.0973771729094 0.9952475502085 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_21 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8897749468929:ℝ):ℂ) + ((0.4563995441297:ℝ):ℂ) * I)‖ ≤ 0.00000011833 := by
  have hl := lg_21
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.357908553478528452 62.357908584201589898 0.4739445 0.00000001832 0.8897749468929 0.4563995441297 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_22 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8875122502018:ℝ):ℂ) + (((-0.4607841205399):ℝ):ℂ) * I)‖ ≤ 0.00000016342 := by
  have hl := lg_22
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.310731508388192906 63.31073154935223387 (-0.4788785) 0.00000006341 0.8875122502018 (-0.4607841205399) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_23 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1804626727913:ℝ):ℂ) + (((-0.9835818337734):ℝ):ℂ) * I)‖ ≤ 0.00000016245 := by
  have hl := lg_23
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.221192509363994412 64.221192550328055858 (-1.3893395) 0.00000006244 0.1804626727913 (-0.9835818337734) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_24 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6367293362995):ℝ):ℂ) + (((-0.7710873830378):ℝ):ℂ) * I)‖ ≤ 0.00000013992 := by
  have hl := lg_24
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.092898531889815048 65.09289857285383553 (-2.2610455) 0.00000003991 (-0.6367293362995) (-0.7710873830378) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_25 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9990131028279):ℝ):ℂ) + (((-0.0444164360719):ℝ):ℂ) * I)‖ ≤ 0.00000014816 := by
  have hl := lg_25
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.929014623653657476 65.92901466461769844 (-3.0971616) 0.00000004815 (-0.9990131028279) (-0.0444164360719) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_26 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7256019502614):ℝ):ℂ) + ((0.6881146777598:ℝ):ℂ) * I)‖ ≤ 0.00000013246 := by
  have hl := lg_26
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.7323332704591794 66.732333311423220364 2.3827051 0.00000003245 (-0.7256019502614) 0.6881146777598 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_27 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0389015546961):ℝ):ℂ) + ((0.9992430480328:ℝ):ℂ) * I)‖ ≤ 0.00000012529 := by
  have hl := lg_27
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.505330673528045144 67.50533070425110659 1.6097077 0.00000002528 (-0.0389015546961) 0.9992430480328 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_28 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6487728408356:ℝ):ℂ) + ((0.7609821292213:ℝ):ℂ) * I)‖ ≤ 0.00000012288 := by
  have hl := lg_28
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.250212756111713404 68.250212797075754368 0.8648256 0.00000002287 0.6487728408356 0.7609821292213 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_29 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9893485200682:ℝ):ℂ) + ((0.1455661562274:ℝ):ℂ) * I)‖ ≤ 0.00000013049 := by
  have hl := lg_29
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.968953168486145544 68.96895320945020699 0.1460852 0.00000003048 0.9893485200682 0.1455661562274 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p482_30 : ‖exp (-((((((20482:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8534189467698:ℝ):ℂ) + (((-0.5212255762089):ℝ):ℂ) * I)‖ ≤ 0.00000012908 := by
  have hl := lg_30
  refine (ecis_approx ((((20482:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.663324749907443786 69.66332479087148475 (-0.5482864) 0.00000002907 0.8534189467698 (-0.5212255762089) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_2 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1109376490442):ℝ):ℂ) + (((-0.9938273683211):ℝ):ℂ) * I)‖ ≤ 0.00000013418 := by
  have hl := lg_2
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.2483334382468 14.2483334485248 (-1.6819628) 0.00000003417 (-0.1109376490442) (-0.9938273683211) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_3 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8298677805246):ℝ):ℂ) + ((0.5579600942583:ℝ):ℂ) * I)‖ ≤ 0.00000012822 := by
  have hl := lg_3
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.583074200518219184 22.58307421079623974 2.549667 0.00000002821 (-0.8298677805246) 0.5579600942583 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_4 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9753856522965):ℝ):ℂ) + ((0.2205058479873:ℝ):ℂ) * I)‖ ≤ 0.00000015942 := by
  have hl := lg_4
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.4966668764936 28.4966668970496 2.9192596 0.00000005941 (-0.9753856522965) 0.2205058479873 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_5 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0967313825107):ℝ):ℂ) + (((-0.9953105242271):ℝ):ℂ) * I)‖ ≤ 0.0000001186 := by
  have hl := lg_5
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.083605717308480204 33.08360573786450076 (-1.6676792) 0.00000001859 (-0.0967313825107) (-0.9953105242271) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_6 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.64657959273:ℝ):ℂ) + ((0.7628465312663:ℝ):ℂ) * I)‖ ≤ 0.00000011626 := by
  have hl := lg_6
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.831407638765019184 36.83140765932103974 0.8677042 0.00000001625 0.64657959273 0.7628465312663 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_7 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6670342077922):ℝ):ℂ) + (((-0.745027090525):ℝ):ℂ) * I)‖ ≤ 0.0000001298 := by
  have hl := lg_7
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.000129013294134632 40.000129033850175744 (-2.3010172) 0.00000002979 (-0.6670342077922) (-0.745027090525) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_8 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3273517379428:ℝ):ℂ) + ((0.9449025556457:ℝ):ℂ) * I)‖ ≤ 0.00000013553 := by
  have hl := lg_8
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.7450003147404 42.7450003455744 1.2372968 0.00000003552 0.3273517379428 0.9449025556457 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_9 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3773610730018:ℝ):ℂ) + (((-0.9260662074511):ℝ):ℂ) * I)‖ ≤ 0.00000014924 := by
  have hl := lg_9
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.166148401036438368 45.16614842159247948 (-1.1838513) 0.00000004923 0.3773610730018 (-0.9260662074511) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_10 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.97843568518):ℝ):ℂ) + ((0.2065517118098:ℝ):ℂ) * I)‖ ≤ 0.00000012897 := by
  have hl := lg_10
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.331939155555280204 47.33193918638930076 2.9335433 0.00000002896 (-0.97843568518) 0.2065517118098 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_11 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5617082577333:ℝ):ℂ) + ((0.8273353813262:ℝ):ℂ) * I)‖ ≤ 0.00000014584 := by
  have hl := lg_11
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.291135211612964348 49.29113524244700546 0.9743472 0.00000004583 0.5617082577333 0.8273353813262 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_12 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6864077406641:ℝ):ℂ) + (((-0.7272168958133):ℝ):ℂ) * I)‖ ≤ 0.00000015042 := by
  have hl := lg_12
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.079741077011819184 51.07974110784583974 (-0.8142586) 0.00000005041 0.6864077406641 (-0.7272168958133) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_13 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7763286096789):ℝ):ℂ) + (((-0.6303283983392):ℝ):ℂ) * I)‖ ≤ 0.00000014936 := by
  have hl := lg_13
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.7250989759490252 52.725099006783066312 (-2.4596165) 0.00000004935 (-0.7763286096789) (-0.6303283983392) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_14 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6664291005155):ℝ):ℂ) + ((0.7455684099848:ℝ):ℂ) * I)‖ ≤ 0.00000011777 := by
  have hl := lg_14
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.248462451540934632 54.248462482374975744 2.3002053 0.00000001776 (-0.6664291005155) 0.7455684099848 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_15 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6356178116613:ℝ):ℂ) + ((0.7720038843807:ℝ):ℂ) * I)‖ ≤ 0.0000001468 := by
  have hl := lg_15
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.666679917826699388 55.6666799486607405 0.8819878 0.00000004679 0.6356178116613 0.7720038843807 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_16 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9027543879797:ℝ):ℂ) + (((-0.4301563843342):ℝ):ℂ) * I)‖ ≤ 0.0000001295 := by
  have hl := lg_16
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.9933337529872 56.9933337940992 (-0.444666) 0.00000002949 0.9027543879797 (-0.4301563843342) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_17 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.119781081318):ℝ):ℂ) + (((-0.9928003286451):ℝ):ℂ) * I)‖ ≤ 0.00000015556 := by
  have hl := lg_17
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.239533479045817304 58.23953352015783786 (-1.6908657) 0.00000005555 (-0.119781081318) (-0.9928003286451) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_18 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9622134920318):ℝ):ℂ) + (((-0.2722961540515):ℝ):ℂ) * I)‖ ≤ 0.00000012535 := by
  have hl := lg_18
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.414481839283238368 59.41448187011727948 (-2.8658141) 0.00000002534 (-0.9622134920318) (-0.2722961540515) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_19 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6707125697535):ℝ):ℂ) + ((0.7417173644693:ℝ):ℂ) * I)‖ ≤ 0.0000001321 := by
  have hl := lg_19
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.525887639715011268 60.525887670549072936 2.3059654 0.00000003209 (-0.6707125697535) 0.7417173644693 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_20 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3138220989944:ℝ):ℂ) + ((0.9494818008697:ℝ):ℂ) * I)‖ ≤ 0.00000016313 := by
  have hl := lg_20
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.580272593802080204 61.58027263491410076 1.2515805 0.00000006312 0.3138220989944 0.9494818008697 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_21 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.969245583252:ℝ):ℂ) + ((0.2460955085866:ℝ):ℂ) * I)‖ ≤ 0.000000158 := by
  have hl := lg_21
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.583203213812353816 62.583203244646415484 0.2486498 0.00000005799 0.969245583252 0.2460955085866 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_22 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.759913951181:ℝ):ℂ) + (((-0.6500236817228):ℝ):ℂ) * I)‖ ≤ 0.00000012195 := by
  have hl := lg_22
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.539468649859764348 63.53946869097180546 (-0.7076156) 0.00000002194 0.759913951181 (-0.6500236817228) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_23 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0505481223921):ℝ):ℂ) + (((-0.9987216265418):ℝ):ℂ) * I)‖ ≤ 0.0000001506 := by
  have hl := lg_23
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.453219081265807496 64.453219122377869164 (-1.621366) 0.00000005059 (-0.0505481223921) (-0.9987216265418) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_24 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7988765749395):ℝ):ℂ) + (((-0.6014949858179):ℝ):ℂ) * I)‖ ≤ 0.00000015655 := by
  have hl := lg_24
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.328074515258619184 65.32807455637063974 (-2.4962215) 0.00000005654 (-0.7988765749395) (-0.6014949858179) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_25 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9812860777554):ℝ):ℂ) + ((0.1925555329529:ℝ):ℂ) * I)‖ ≤ 0.00000014437 := by
  have hl := lg_25
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.167211434616960408 66.16721147572900152 2.9478269 0.00000004436 (-0.9812860777554) 0.1925555329529 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_26 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5403134522902):ℝ):ℂ) + ((0.8414638276635:ℝ):ℂ) * I)‖ ≤ 0.00000016479 := by
  have hl := lg_26
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.9734324141958252 66.973432455307866312 2.1416059 0.00000006478 (-0.5403134522902) 0.8414638276635 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_27 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2035480944108:ℝ):ℂ) + ((0.9790649484389:ℝ):ℂ) * I)‖ ≤ 0.00000015343 := by
  have hl := lg_27
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.749222601554657552 67.74922263238871922 1.3658158 0.00000005342 0.2035480944108 0.9790649484389 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_28 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8148983684754:ℝ):ℂ) + ((0.5796038725338:ℝ):ℂ) * I)‖ ≤ 0.00000015194 := by
  have hl := lg_28
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.496795889787734632 68.496795930899775744 0.6182425 0.00000005193 0.8148983684754 0.5796038725338 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_29 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9946904466394:ℝ):ℂ) + (((-0.1029121730617):ℝ):ℂ) * I)‖ ≤ 0.00000012198 := by
  have hl := lg_29
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.218133059828200752 69.21813310094026242 (-0.1030947) 0.00000002197 0.9946904466394 (-0.1029121730617) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_30 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6967246430317:ℝ):ℂ) + (((-0.7173386730076):ℝ):ℂ) * I)‖ ≤ 0.00000012292 := by
  have hl := lg_30
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.915013356073499388 69.9150133971855405 (-0.799975) 0.00000002291 0.6967246430317 (-0.7173386730076) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_31 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0966426537661:ℝ):ℂ) + (((-0.9953191435278):ℝ):ℂ) * I)‖ ≤ 0.00000012497 := by
  have hl := lg_31
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.589040954022881828 70.589040995134943496 (-1.4740026) 0.00000002496 0.0966426537661 (-0.9953191435278) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_32 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5276506368759):ℝ):ℂ) + (((-0.8494614796428):ℝ):ℂ) * I)‖ ≤ 0.00000016366 := by
  have hl := lg_32
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.241667191234 71.241667242624 (-2.1266288) 0.00000006365 (-0.5276506368759) (-0.8494614796428) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_33 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9277637098023):ℝ):ℂ) + (((-0.373168190791):ℝ):ℂ) * I)‖ ≤ 0.00000016686 := by
  have hl := lg_33
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.874209412131183532 71.8742094532432452 (-2.7591711) 0.00000006685 (-0.9277637098023) (-0.373168190791) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_34 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9733838816476):ℝ):ℂ) + ((0.2291807554338:ℝ):ℂ) * I)‖ ≤ 0.00000016888 := by
  have hl := lg_34
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.487866917292617304 72.48786696868263786 2.9103567 0.00000006887 (-0.9733838816476) 0.2291807554338 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_35 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6770101576564):ℝ):ℂ) + ((0.7359736723619:ℝ):ℂ) * I)‖ ≤ 0.00000015557 := by
  have hl := lg_35
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.083734730602614836 73.083734771714676504 2.3144889 0.00000005556 (-0.6770101576564) 0.7359736723619 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_36 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1638696605302):ℝ):ℂ) + ((0.986481999003:ℝ):ℂ) * I)‖ ≤ 0.0000001325 := by
  have hl := lg_36
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.662815277530038368 73.66281531864207948 1.7354084 0.00000003249 (-0.1638696605302) 0.986481999003 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_37 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3881296063287:ℝ):ℂ) + ((0.9216048007097:ℝ):ℂ) * I)‖ ≤ 0.00000014591 := by
  have hl := lg_37
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.226028590940909752 74.22602863205297142 1.1721951 0.0000000459 0.3881296063287 0.9216048007097 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_38 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8115462920527:ℝ):ℂ) + ((0.5842881274298:ℝ):ℂ) * I)‖ ≤ 0.00000013293 := by
  have hl := lg_38
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.774221077961811268 74.774221119073872936 0.6240026 0.00000003292 0.8115462920527 0.5842881274298 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_39 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9959481928753:ℝ):ℂ) + ((0.0899288446964:ℝ):ℂ) * I)‖ ≤ 0.00000013144 := by
  have hl := lg_39
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.308173176467244384 75.308173217579306052 0.0900505 0.00000003143 0.9959481928753 0.0899288446964 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p556_40 : ‖exp (-((((((20556:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.908806271825:ℝ):ℂ) + (((-0.417218360444):ℝ):ℂ) * I)‖ ≤ 0.00000015412 := by
  have hl := lg_40
  refine (ecis_approx ((((20556:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.828606032048880204 75.82860608343890076 (-0.4303824) 0.00000005411 0.908806271825 (-0.417218360444) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_2 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1617456826757):ℝ):ℂ) + (((-0.986832475213):ℝ):ℂ) * I)‖ ≤ 0.00000012556 := by
  have hl := lg_2
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.299626329589 14.299626339904 (-1.7332557) 0.00000002555 (-0.1617456826757) (-0.986832475213) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_3 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7818161893787):ℝ):ℂ) + ((0.6235089782694:ℝ):ℂ) * I)‖ ≤ 0.00000011887 := by
  have hl := lg_3
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.66437150986042332 22.66437152017544395 2.4683697 0.00000001886 (-0.7818161893787) 0.6235089782694 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_4 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9476766659101):ℝ):ℂ) + ((0.319231791481:ℝ):ℂ) * I)‖ ≤ 0.00000014393 := by
  have hl := lg_4
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.599252659178 28.599252679808 2.8166739 0.00000004392 (-0.9476766659101) 0.319231791481 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_5 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2143060061889):ℝ):ℂ) + (((-0.9767665717613):ℝ):ℂ) * I)‖ ≤ 0.00000011312 := by
  have hl := lg_5
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.20270412279013167 33.2027041434201523 (-1.7867776) 0.00000001311 (-0.2143060061889) (-0.9767665717613) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_6 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7417543016463:ℝ):ℂ) + ((0.6706717199861:ℝ):ℂ) * I)‖ ≤ 0.00000011702 := by
  have hl := lg_6
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.96399783944942332 36.96399786007944395 0.735114 0.00000001701 0.7417543016463 0.6706717199861 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_7 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7670421191793):ℝ):ℂ) + (((-0.6415967482512):ℝ):ℂ) * I)‖ ≤ 0.00000014185 := by
  have hl := lg_7
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.14412636428575586 40.14412638491579712 (-2.4450145) 0.00000004184 (-0.7670421191793) (-0.6415967482512) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_8 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4683109967062:ℝ):ℂ) + ((0.8835636990982:ℝ):ℂ) * I)‖ ≤ 0.00000016151 := by
  have hl := lg_8
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.898878988767 42.898879019712 1.0834181 0.0000000615 0.4683109967062 0.8835636990982 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_9 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2224731149745:ℝ):ℂ) + (((-0.9749388253186):ℝ):ℂ) * I)‖ ≤ 0.00000013055 := by
  have hl := lg_9
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.32874301972084664 45.3287430403508879 (-1.3464459) 0.00000003054 0.2224731149745 (-0.9749388253186) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_10 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9292418997405):ℝ):ℂ) + ((0.3694719090925:ℝ):ℂ) * I)‖ ≤ 0.0000001259 := by
  have hl := lg_10
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.50233045237913167 47.5023304833241523 2.763152 0.00000002589 (-0.9292418997405) 0.3694719090925 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_11 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6989250164124:ℝ):ℂ) + ((0.7151949534448:ℝ):ℂ) * I)‖ ≤ 0.00000013527 := by
  have hl := lg_11
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.46857946174233579 49.46857949268737705 0.796903 0.00000003526 0.6989250164124 0.7151949534448 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_12 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5418650775922:ℝ):ℂ) + (((-0.8404654886942):ℝ):ℂ) * I)‖ ≤ 0.00000014256 := by
  have hl := lg_12
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.26362416903842332 51.26362419998344395 (-0.9981417) 0.00000004255 0.5418650775922 (-0.8404654886942) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_13 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8813095929843):ℝ):ℂ) + (((-0.4725393118212):ℝ):ℂ) * I)‖ ≤ 0.00000012911 := by
  have hl := lg_13
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.914905228343471 52.91490525928851226 (-2.6494228) 0.0000000291 (-0.8813095929843) (-0.4725393118212) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_14 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5090827497985):ℝ):ℂ) + ((0.8607175807726:ℝ):ℂ) * I)‖ ≤ 0.00000016022 := by
  have hl := lg_14
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.44375269387475586 54.44375272481979712 2.1049151 0.00000006021 (-0.5090827497985) 0.8607175807726 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_15 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7765706323117:ℝ):ℂ) + ((0.6300302000944:ℝ):ℂ) * I)‖ ≤ 0.00000013198 := by
  have hl := lg_15
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.86707563265055499 55.86707566359559625 0.6815921 0.00000003197 0.7765706323117 0.6300302000944 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_16 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7961820703231:ℝ):ℂ) + (((-0.6050571137472):ℝ):ℂ) * I)‖ ≤ 0.00000014628 := by
  have hl := lg_16
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.198505318356 57.198505359616 (-0.6498376) 0.00000004627 0.7961820703231 (-0.6050571137472) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_17 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3237849106378):ℝ):ℂ) + (((-0.946130715938):ℝ):ℂ) * I)‖ ≤ 0.00000014309 := by
  have hl := lg_17
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.44919126642903342 58.44919130768905405 (-1.9005235) 0.00000004308 (-0.3237849106378) (-0.946130715938) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_18 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9980853597702):ℝ):ℂ) + (((-0.0618515485981):ℝ):ℂ) * I)‖ ≤ 0.00000011565 := by
  have hl := lg_18
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.62836934930984664 59.6283693802548879 (-3.0797016) 0.00000001564 (-0.9980853597702) (-0.0618515485981) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_19 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4945183327388):ℝ):ℂ) + ((0.8691671982876:ℝ):ℂ) * I)‖ ≤ 0.0000001477 := by
  have hl := lg_19
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.74377612411561989 60.74377615506068178 2.0880769 0.00000004769 (-0.4945183327388) 0.8691671982876 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_20 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5149077441069:ℝ):ℂ) + ((0.8572455978649:ℝ):ℂ) * I)‖ ≤ 0.00000015145 := by
  have hl := lg_20
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.80195678196813167 61.8019568232281523 1.0298963 0.00000005144 0.5149077441069 0.8572455978649 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_21 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997272797134:ℝ):ℂ) + ((0.0233530768158:ℝ):ℂ) * I)‖ ≤ 0.00000013331 := by
  have hl := lg_21
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.80849787414617918 62.80849790509124107 0.0233552 0.0000000333 0.9997272797134 0.0233530768158 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_22 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5927295022494:ℝ):ℂ) + (((-0.8054015999259):ℝ):ℂ) * I)‖ ≤ 0.00000016081 := by
  have hl := lg_22
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.76820579133133579 63.76820583259137705 (-0.9363527) 0.0000000608 0.5927295022494 (-0.8054015999259) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_23 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2788498768385):ℝ):ℂ) + (((-0.9603347052906):ℝ):ℂ) * I)‖ ≤ 0.00000012265 := by
  have hl := lg_23
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.68524565316762058 64.68524569442768247 (-1.8533926) 0.00000002264 (-0.2788498768385) (-0.9603347052906) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_24 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9170429753894):ℝ):ℂ) + (((-0.398788391444):ℝ):ℂ) * I)‖ ≤ 0.00000016811 := by
  have hl := lg_24
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.56325049862742332 65.56325053988744395 (-2.7313974) 0.0000000681 (-0.9170429753894) (-0.398788391444) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_25 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9081458683788):ℝ):ℂ) + ((0.4186538923983:ℝ):ℂ) * I)‖ ≤ 0.00000013341 := by
  have hl := lg_25
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.40540824558026334 66.4054082868403046 2.7096301 0.0000000334 (-0.9081458683788) 0.4186538923983 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_26 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3237691102097):ℝ):ℂ) + ((0.946136123014:ℝ):ℂ) * I)‖ ≤ 0.00000012106 := by
  have hl := lg_26
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.214531557932471 67.21453159919251226 1.9005068 0.00000002105 (-0.3237691102097) 0.946136123014 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_27 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4339500278826:ℝ):ℂ) + ((0.9009369419114:ℝ):ℂ) * I)‖ ≤ 0.00000014941 := by
  have hl := lg_27
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.99311452958126996 67.99311456052633185 1.1219238 0.0000000494 0.4339500278826 0.9009369419114 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_28 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9317260339179:ℝ):ℂ) + ((0.3631619442061:ℝ):ℂ) * I)‖ ≤ 0.00000015553 := by
  have hl := lg_28
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.74337902346375586 68.74337906472379712 0.3716593 0.00000005552 0.9317260339179 0.3631619442061 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_29 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9385903281025:ℝ):ℂ) + (((-0.3450336157428):ℝ):ℂ) * I)‖ ≤ 0.00000012782 := by
  have hl := lg_29
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.46731295117025596 69.46731299243031785 (-0.3522746) 0.00000002781 0.9385903281025 (-0.3450336157428) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_30 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4961273147493:ℝ):ℂ) + (((-0.8682497840827):ℝ):ℂ) * I)‖ ≤ 0.00000012454 := by
  have hl := lg_30
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.16670196223955499 70.16670200349959625 (-1.0516636) 0.00000002453 0.4961273147493 (-0.8682497840827) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_31 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1566731260006):ℝ):ℂ) + (((-0.9876505108532):ℝ):ℂ) * I)‖ ≤ 0.00000016938 := by
  have hl := lg_31
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.84315600707783869 70.84315604833790058 (-1.7281176) 0.00000006937 (-0.1566731260006) (-0.9876505108532) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_32 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7258690216988):ℝ):ℂ) + (((-0.6878329472406):ℝ):ℂ) * I)‖ ≤ 0.00000013105 := by
  have hl := lg_32
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.498131647945 71.49813169952 (-2.3830933) 0.00000003104 (-0.7258690216988) (-0.6878329472406) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_33 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9923613666225):ℝ):ℂ) + (((-0.1233649772012):ℝ):ℂ) * I)‖ ≤ 0.0000001339 := by
  have hl := lg_33
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.13295097160275911 72.132951012862821 (-3.0179126) 0.00000003389 (-0.9923613666225) (-0.1233649772012) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_34 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8813017014549):ℝ):ℂ) + ((0.4725540296255:ℝ):ℂ) * I)‖ ≤ 0.00000016145 := by
  have hl := lg_34
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.74881759601803342 72.74881764759305405 2.6494061 0.00000006144 (-0.8813017014549) 0.4725540296255 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_35 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4623085167563):ℝ):ℂ) + ((0.886719141177:ℝ):ℂ) * I)‖ ≤ 0.0000001422 := by
  have hl := lg_35
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.34683048707588753 73.34683052833594942 2.0513932 0.00000004219 (-0.4623085167563) 0.886719141177 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_36 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1003988880217:ℝ):ℂ) + ((0.9949472665845:ℝ):ℂ) * I)‖ ≤ 0.00000013402 := by
  have hl := lg_36
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.92799567889884664 73.9279957201588879 1.470228 0.00000003401 0.1003988880217 0.9949472665845 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_37 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6176957247665:ℝ):ℂ) + ((0.7864171867433:ℝ):ℂ) * I)‖ ≤ 0.00000016977 := by
  have hl := lg_37
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.49323651639963846 74.49323655765970035 0.9049871 0.00000006976 0.6176957247665 0.7864171867433 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_38 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9377086229883:ℝ):ℂ) + ((0.3474227084883:ℝ):ℂ) * I)‖ ≤ 0.00000013247 := by
  have hl := lg_38
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.04340245370461989 75.04340249496468178 0.3548212 0.00000003246 0.9377086229883 0.3474227084883 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_39 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9836546112283:ℝ):ℂ) + (((-0.1800655597535):ℝ):ℂ) * I)‖ ≤ 0.00000014797 := by
  have hl := lg_39
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.57927673820389432 75.57927677946395621 (-0.1810531) 0.00000004796 0.9836546112283 (-0.1800655597535) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p63_40 : ‖exp (-((((((20630:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.762673625943:ℝ):ℂ) + (((-0.6467835343382):ℝ):ℂ) * I)‖ ≤ 0.00000017461 := by
  have hl := lg_40
  refine (ecis_approx ((((20630:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.10158311155713167 76.1015831631321523 (-0.7033595) 0.0000000746 0.762673625943 (-0.6467835343382) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_2 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1992401595819):ℝ):ℂ) + (((-0.9799506920294):ℝ):ℂ) * I)‖ ≤ 0.0000001205 := by
  have hl := lg_2
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.3377494245055 14.337749434848 (-1.7713788) 0.00000002049 (-0.1992401595819) (-0.9799506920294) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_3 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7427376104912):ℝ):ℂ) + ((0.6695825878334:ℝ):ℂ) * I)‖ ≤ 0.00000014301 := by
  have hl := lg_3
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.72479518572287234 22.724795196065393025 2.407946 0.000000043 (-0.7427376104912) 0.6695825878334 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_4 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9206067147704):ℝ):ℂ) + ((0.3904910710576:ℝ):ℂ) * I)‖ ≤ 0.00000013381 := by
  have hl := lg_4
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.675498849011 28.675498869696 2.7404277 0.0000000338 (-0.9206067147704) 0.3904910710576 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_5 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2998165702528):ℝ):ℂ) + (((-0.9539968680243):ℝ):ℂ) * I)‖ ≤ 0.00000012797 := by
  have hl := lg_5
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.291223207945413165 33.29122322863043385 (-1.8752967) 0.00000002796 (-0.2998165702528) (-0.9539968680243) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_6 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.804141080379:ℝ):ℂ) + ((0.5944384937458:ℝ):ℂ) * I)‖ ≤ 0.00000013286 := by
  have hl := lg_6
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.06254461022837234 37.062544630913393025 0.6365672 0.00000003285 0.804141080379 0.5944384937458 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_7 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8311892596445):ℝ):ℂ) + (((-0.5559895813668):ℝ):ℂ) * I)‖ ≤ 0.00000012064 := by
  have hl := lg_7
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.25115142245520407 40.25115144314024544 (-2.5520396) 0.00000002063 (-0.8311892596445) (-0.5559895813668) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_8 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5660838241616:ℝ):ℂ) + ((0.8243476839433:ℝ):ℂ) * I)‖ ≤ 0.0000001543 := by
  have hl := lg_8
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.0132482735165 43.013248304544 0.9690489 0.00000005429 0.5660838241616 0.8243476839433 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_9 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1033184226979:ℝ):ℂ) + (((-0.9946483315882):ℝ):ℂ) * I)‖ ≤ 0.00000014189 := by
  have hl := lg_9
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.44959037144574468 45.44959039213078605 (-1.4672932) 0.00000004188 0.1033184226979 (-0.9946483315882) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_10 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8751343862144):ℝ):ℂ) + ((0.4838799499599:ℝ):ℂ) * I)‖ ≤ 0.000000125 := by
  have hl := lg_10
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.628972632450913165 47.62897266347843385 2.6365098 0.00000002499 (-0.8751343862144) 0.4838799499599 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_11 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7869052459851:ℝ):ℂ) + ((0.6170738479641:ℝ):ℂ) * I)‖ ≤ 0.00000015575 := by
  have hl := lg_11
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.600463701703355105 49.600463732730896475 0.6650187 0.00000005574 0.7869052459851 0.6170738479641 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_12 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4223032161344:ℝ):ℂ) + (((-0.9064546285626):ℝ):ℂ) * I)‖ ≤ 0.00000012272 := by
  have hl := lg_12
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.40029403473387234 51.400294065761393025 (-1.1348116) 0.00000002271 0.4223032161344 (-0.9064546285626) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_13 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9389957639549):ℝ):ℂ) + (((-0.3439287064168):ℝ):ℂ) * I)‖ ≤ 0.00000011657 := by
  have hl := lg_13
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.0559774429609645 53.05597747398850587 (-2.790495) 0.00000001656 (-0.9389957639549) (-0.3439287064168) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_14 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3792360876758):ℝ):ℂ) + ((0.9252999458562:ℝ):ℂ) * I)‖ ≤ 0.00000011767 := by
  have hl := lg_14
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.58890084696070407 54.58890087798824544 1.9597669 0.00000001766 (-0.3792360876758) 0.9252999458562 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_15 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8614646838896:ℝ):ℂ) + ((0.507817485334:ℝ):ℂ) * I)‖ ≤ 0.00000016009 := by
  have hl := lg_15
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.016018393668285505 56.016018424695826875 0.5326494 0.00000006008 0.8614646838896 0.507817485334 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_16 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.695033379993:ℝ):ℂ) + (((-0.7189774688371):ℝ):ℂ) * I)‖ ≤ 0.00000016661 := by
  have hl := lg_16
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.350997698022 57.350997739392 (-0.80233) 0.0000000666 0.695033379993 (-0.7189774688371) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_17 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4666983741041):ℝ):ℂ) + (((-0.8844165464325):ℝ):ℂ) * I)‖ ≤ 0.00000016434 := by
  have hl := lg_17
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.60501800029493729 58.605018041664957975 (-2.0563503) 0.00000006433 (-0.4666983741041) (-0.8844165464325) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_18 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9952914989767):ℝ):ℂ) + ((0.0969269394109:ℝ):ℂ) * I)‖ ≤ 0.0000001552 := by
  have hl := lg_18
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.78733979595124468 59.78733982697878605 3.0445133 0.00000005519 (-0.9952914989767) 0.0969269394109 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_19 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3479058384732):ℝ):ℂ) + ((0.9375294808986:ℝ):ℂ) * I)‖ ≤ 0.00000012717 := by
  have hl := lg_19
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.905720267926883055 60.90572029895444511 1.9261328 0.00000002716 (-0.3479058384732) 0.9375294808986 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_20 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6485404066417:ℝ):ℂ) + ((0.7611802289557:ℝ):ℂ) * I)‖ ≤ 0.00000012655 := by
  have hl := lg_20
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.966722056956413165 61.96672209832643385 0.865131 0.00000002654 0.6485404066417 0.7611802289557 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_21 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9896364673231:ℝ):ℂ) + (((-0.1435954823256):ℝ):ℂ) * I)‖ ≤ 0.00000016363 := by
  have hl := lg_21
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.97594660817807641 62.975946639205638465 (-0.1440936) 0.00000006362 0.9896364673231 (-0.1435954823256) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_22 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4479188175601:ℝ):ℂ) + (((-0.8940742323071):ℝ):ℂ) * I)‖ ≤ 0.0000001456 := by
  have hl := lg_22
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.938213126208855105 63.938213167578896475 (-1.1063601) 0.00000004559 0.4479188175601 (-0.8940742323071) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_23 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4395058548806):ℝ):ℂ) + (((-0.898239724974):ℝ):ℂ) * I)‖ ≤ 0.00000013682 := by
  have hl := lg_23
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.85769783498653571 64.857697876356597765 (-2.0258448) 0.00000003681 (-0.4395058548806) (-0.898239724974) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_24 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9724206006168):ℝ):ℂ) + (((-0.2332341639069):ℝ):ℂ) * I)‖ ≤ 0.00000012883 := by
  have hl := lg_24
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.73804345923937234 65.738043500609393025 (-2.9061904) 0.00000002882 (-0.9724206006168) (-0.2332341639069) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_25 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.820220044284):ℝ):ℂ) + ((0.572048143863:ℝ):ℂ) * I)‖ ≤ 0.0000001631 := by
  have hl := lg_25
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.58244641589082633 66.5824464572608677 2.5325919 0.00000006309 (-0.820220044284) 0.572048143863 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_26 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1499475009858):ℝ):ℂ) + ((0.9886939602058:ℝ):ℂ) * I)‖ ≤ 0.00000012988 := by
  have hl := lg_26
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.3937268674664645 67.39372690883650587 1.7213115 0.00000002987 (-0.1499475009858) 0.9886939602058 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_27 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5892607254722:ℝ):ℂ) + ((0.8079429419309:ℝ):ℂ) * I)‖ ≤ 0.00000012182 := by
  have hl := lg_27
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.17438555716861702 68.174385588196179075 0.9406528 0.00000002181 0.5892607254722 0.8079429419309 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_28 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9823073809062:ℝ):ℂ) + ((0.1872757576868:ℝ):ℂ) * I)‖ ≤ 0.00000013388 := by
  have hl := lg_28
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.92665027146620407 68.92665031283624544 0.1883881 0.00000003387 0.9823073809062 0.1872757576868 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_29 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8590036783782:ℝ):ℂ) + (((-0.5119694136692):ℝ):ℂ) * I)‖ ≤ 0.00000015723 := by
  have hl := lg_29
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.65251422176232402 69.652514263132386075 (-0.5374759) 0.00000005722 0.8590036783782 (-0.5119694136692) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_30 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3259976405486:ℝ):ℂ) + (((-0.9453705825531):ℝ):ℂ) * I)‖ ≤ 0.00000016082 := by
  have hl := lg_30
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.353767818173785505 70.353767859543826875 (-1.2387295) 0.00000006081 0.3259976405486 (-0.9453705825531) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_31 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3393168565102):ℝ):ℂ) + (((-0.940672137828):ℝ):ℂ) * I)‖ ≤ 0.00000016568 := by
  have hl := lg_31
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.032025303267333655 71.03202534463739571 (-1.9169869) 0.00000006567 (-0.3393168565102) (-0.940672137828) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_32 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8430410296686):ℝ):ℂ) + (((-0.5378492560427):ℝ):ℂ) * I)‖ ≤ 0.00000015646 := by
  have hl := lg_32
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.6887471225275 71.68874717424 (-2.5737088) 0.00000005645 (-0.8430410296686) (-0.5378492560427) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_33 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9976460327117):ℝ):ℂ) + ((0.0685739956521:ℝ):ℂ) * I)‖ ≤ 0.00000014266 := by
  have hl := lg_33
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.325258887426227445 72.3252589287962895 3.0729648 0.00000004265 (-0.9976460327117) 0.0685739956521 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_34 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7736995436327):ℝ):ℂ) + ((0.6335526940533:ℝ):ℂ) * I)‖ ≤ 0.00000016137 := by
  have hl := lg_34
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.94276742480043729 72.942767476512957975 2.4554562 0.00000006136 (-0.7736995436327) 0.6335526940533 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_35 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2812079993604):ℝ):ℂ) + ((0.9596468418612:ℝ):ℂ) * I)‖ ≤ 0.00000015577 := by
  have hl := lg_35
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.542374630400617235 73.54237467177067929 1.855849 0.00000005576 (-0.2812079993604) 0.9596468418612 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_36 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2932857543063:ℝ):ℂ) + ((0.9560248251593:ℝ):ℂ) * I)‖ ≤ 0.00000016571 := by
  have hl := lg_36
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.12508922045674468 74.12508926182678605 1.2731344 0.0000000657 0.2932857543063 0.9560248251593 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_37 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7607121912733:ℝ):ℂ) + ((0.649089332872:ℝ):ℂ) * I)‖ ≤ 0.00000015677 := by
  have hl := lg_37
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.69183700153788277 74.691837042907944825 0.7063867 0.00000005676 0.7607121912733 0.649089332872 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_38 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.988049478383:ℝ):ℂ) + ((0.1541370437858:ℝ):ℂ) * I)‖ ≤ 0.00000014766 := by
  have hl := lg_38
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.243469692432383055 75.24346973380244511 0.154754 0.00000004765 0.988049478383 0.1541370437858 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_39 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9277161433722:ℝ):ℂ) + (((-0.3732864279968):ℝ):ℂ) * I)‖ ≤ 0.00000015749 := by
  have hl := lg_39
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.78077262868383684 75.780772670053898895 (-0.382549) 0.00000005748 0.9277161433722 (-0.3732864279968) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p685_40 : ‖exp (-((((((20685:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.61670379801:ℝ):ℂ) + (((-0.7871952905855):ℝ):ℂ) * I)‖ ≤ 0.00000014703 := by
  have hl := lg_40
  refine (ecis_approx ((((20685:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.304471481461913165 76.30447153317443385 (-0.9062478) 0.00000004702 0.61670379801 (-0.7871952905855) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_2 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.227005178059):ℝ):ℂ) + (((-0.9738935512331):ℝ):ℂ) * I)‖ ≤ 0.00000015492 := by
  have hl := lg_2
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.3661684588978 14.3661684692608 (-1.7997978) 0.00000005491 (-0.227005178059) (-0.9738935512331) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_3 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7118343968505):ℝ):ℂ) + ((0.7023473438653:ℝ):ℂ) * I)‖ ≤ 0.00000013919 := by
  have hl := lg_3
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.769838289547607064 22.76983829991062779 2.3629029 0.00000003918 (-0.7118343968505) 0.7023473438653 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_4 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8969372508457):ℝ):ℂ) + ((0.4421578540887:ℝ):ℂ) * I)‖ ≤ 0.00000011812 := by
  have hl := lg_4
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.7323369177956 28.7323369385216 2.6835896 0.00000001811 (-0.8969372508457) 0.4421578540887 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_5 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3620696871509):ℝ):ℂ) + (((-0.9321510294174):ℝ):ℂ) * I)‖ ≤ 0.00000014718 := by
  have hl := lg_5
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.357210162333895734 33.35721018305991646 (-1.9412836) 0.00000004717 (-0.3620696871509) (-0.9321510294174) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_6 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8456016429371:ℝ):ℂ) + ((0.5338144447859:ℝ):ℂ) * I)‖ ≤ 0.00000012611 := by
  have hl := lg_6
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.136006748445407064 37.13600676917142779 0.5631051 0.0000000261 0.8456016429371 0.5338144447859 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_7 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.872856397569):ℝ):ℂ) + (((-0.4879771604621):ℝ):ℂ) * I)‖ ≤ 0.00000011621 := by
  have hl := lg_7
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.330933738545156372 40.330933759271197824 (-2.6318219) 0.0000000162 (-0.872856397569) (-0.4879771604621) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_8 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6342240831271:ℝ):ℂ) + ((0.7731492820805:ℝ):ℂ) * I)‖ ≤ 0.00000015754 := by
  have hl := lg_8
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.0985053766934 43.0985054077824 0.8837918 0.00000005753 0.6342240831271 0.7731492820805 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_9 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0134165242595:ℝ):ℂ) + (((-0.9999099943878):ℝ):ℂ) * I)‖ ≤ 0.00000014958 := by
  have hl := lg_9
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.539676579095214128 45.53967659982125558 (-1.5573794) 0.00000004957 0.0134165242595 (-0.9999099943878) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_10 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8256241220389):ℝ):ℂ) + ((0.5642205322808:ℝ):ℂ) * I)‖ ≤ 0.00000013622 := by
  have hl := lg_10
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.723378621231695734 47.72337865232071646 2.5421038 0.00000003621 (-0.8256241220389) 0.5642205322808 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_11 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8436744892796:ℝ):ℂ) + ((0.5368550606438:ℝ):ℂ) * I)‖ ≤ 0.0000001496 := by
  have hl := lg_11
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.698777407856114958 49.69877743894515641 0.566705 0.00000004959 0.8436744892796 0.5368550606438 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_12 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3279223993401:ℝ):ℂ) + (((-0.9447046628503):ℝ):ℂ) * I)‖ ≤ 0.00000015011 := by
  have hl := lg_12
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.502175207343207064 51.50217523843222779 (-1.2366928) 0.0000000501 0.3279223993401 (-0.9447046628503) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_13 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9699101706692):ℝ):ℂ) + (((-0.2434630578983):ℝ):ℂ) * I)‖ ≤ 0.00000014025 := by
  have hl := lg_13
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.1611403665849142 53.161140397673955652 (-2.8956579) 0.00000004024 (-0.9699101706692) (-0.2434630578983) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_14 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2770948809176):ℝ):ℂ) + ((0.9608425609681:ℝ):ℂ) * I)‖ ≤ 0.00000016393 := by
  have hl := lg_14
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.697102197442956372 54.697102228531997824 1.8515656 0.00000006392 (-0.2770948809176) 0.9608425609681 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_15 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9124274569794:ℝ):ℂ) + ((0.4092384827336:ℝ):ℂ) * I)‖ ≤ 0.00000011837 := by
  have hl := lg_15
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.127048451881502798 56.12704848297054425 0.4216193 0.00000001836 0.9124274569794 0.4092384827336 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_16 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.608992869722:ℝ):ℂ) + (((-0.7931756959387):ℝ):ℂ) * I)‖ ≤ 0.00000012904 := by
  have hl := lg_16
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.4646738355912 57.4646738770432 (-0.9160061) 0.00000002903 0.608992869722 (-0.7931756959387) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_17 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5660576478774):ℝ):ℂ) + (((-0.8243656587157):ℝ):ℂ) * I)‖ ≤ 0.00000012421 := by
  have hl := lg_17
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.721179747358611084 58.72117978881063181 (-2.172512) 0.0000000242 (-0.5660576478774) (-0.8243656587157) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_18 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9768514927761):ℝ):ℂ) + ((0.2139185844088:ℝ):ℂ) * I)‖ ≤ 0.00000013382 := by
  have hl := lg_18
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.905845037993014128 59.90584506908205558 2.926008 0.00000003381 (-0.9768514927761) 0.2139185844088 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_19 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.232468037881):ℝ):ℂ) + ((0.9726040362669:ℝ):ℂ) * I)‖ ≤ 0.00000012535 := by
  have hl := lg_19
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.026442266040733778 61.026442297129795956 1.8054108 0.00000002534 (-0.232468037881) 0.9726040362669 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_20 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7369116887308:ℝ):ℂ) + ((0.6759890258073:ℝ):ℂ) * I)‖ ≤ 0.0000001498 := by
  have hl := lg_20
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.089547080129495734 62.08954712158151646 0.742306 0.00000004979 0.7369116887308 0.6759890258073 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_21 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9640586698803:ℝ):ℂ) + (((-0.2656894447068):ℝ):ℂ) * I)‖ ≤ 0.00000014372 := by
  have hl := lg_21
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.100772028092763436 63.100772059181825614 (-0.268919) 0.00000004371 0.9640586698803 (-0.2656894447068) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_22 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3313212038455:ℝ):ℂ) + (((-0.943518023083):ℝ):ℂ) * I)‖ ≤ 0.00000013643 := by
  have hl := lg_22
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.064945866753914958 64.06494590820595641 (-1.2330928) 0.00000003642 0.3313212038455 (-0.943518023083) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_23 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.551034709864):ℝ):ℂ) + (((-0.8344823236692):ℝ):ℂ) * I)‖ ≤ 0.00000016747 := by
  have hl := lg_23
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.986253097796999716 64.986253139249061894 (-2.1544) 0.00000006746 (-0.551034709864) (-0.8344823236692) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_24 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9944818614104):ℝ):ℂ) + (((-0.1049086595987):ℝ):ℂ) * I)‖ ≤ 0.00000013591 := by
  have hl := lg_24
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.868343666241007064 65.86834370769302779 (-3.0364906) 0.0000000359 (-0.9944818614104) (-0.1049086595987) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_25 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7378110109411):ℝ):ℂ) + ((0.6750073422586:ℝ):ℂ) * I)‖ ≤ 0.00000015432 := by
  have hl := lg_25
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.714420324667791468 66.71442036611983292 2.400618 0.00000005431 (-0.7378110109411) 0.6750073422586 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_26 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.016932364002):ℝ):ℂ) + ((0.9998566372481:ℝ):ℂ) * I)‖ ≤ 0.00000015351 := by
  have hl := lg_26
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.5273088254827142 67.527308866934755652 1.5877295 0.0000000535 (-0.016932364002) 0.9998566372481 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_27 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6927337852231:ℝ):ℂ) + ((0.7211933879414:ℝ):ℂ) * I)‖ ≤ 0.00000012077 := by
  have hl := lg_27
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.309514868642821192 68.30951489973188337 0.8055235 0.00000002076 0.6927337852231 0.7211933879414 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_28 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9986603518348:ℝ):ℂ) + ((0.0517445811:ℝ):ℂ) * I)‖ ≤ 0.00000012265 := by
  have hl := lg_28
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.063270656340756372 69.063270697792797824 0.0517677 0.00000002264 0.9986603518348 0.0517445811 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_29 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.780372519355:ℝ):ℂ) + (((-0.625314905496):ℝ):ℂ) * I)‖ ≤ 0.00000012824 := by
  have hl := lg_29
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.790573350749138392 69.79057339220120057 (-0.675535) 0.00000002823 0.780372519355 (-0.625314905496) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_30 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1914288637628:ℝ):ℂ) + (((-0.9815064901051):ℝ):ℂ) * I)‖ ≤ 0.00000016821 := by
  have hl := lg_30
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.493216910779302798 70.49321695223134425 (-1.3781786) 0.0000000682 0.1914288637628 (-0.9815064901051) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_31 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4679627005336):ℝ):ℂ) + (((-0.8837482169171):ℝ):ℂ) * I)‖ ≤ 0.0000001411 := by
  have hl := lg_31
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.172818778608593538 71.172818820060655716 (-2.0577804) 0.00000004109 (-0.4679627005336) (-0.8837482169171) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_32 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9107132300581):ℝ):ℂ) + (((-0.4130392384114):ℝ):ℂ) * I)‖ ≤ 0.00000016734 := by
  have hl := lg_32
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.830842294489 71.830842346304 (-2.7158039) 0.00000006733 (-0.9107132300581) (-0.4130392384114) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_33 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.977615268024):ℝ):ℂ) + ((0.2104005404376:ℝ):ℂ) * I)‖ ≤ 0.00000015272 := by
  have hl := lg_33
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.468615697403722022 72.4686157388557842 2.929608 0.00000005271 (-0.977615268024) 0.2104005404376 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_34 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.674346376435):ℝ):ℂ) + ((0.7384151708687:ℝ):ℂ) * I)‖ ≤ 0.00000017193 := by
  have hl := lg_34
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.087348206256411084 73.08734825807143181 2.3108755 0.00000007192 (-0.674346376435) 0.7384151708687 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_35 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1388335625895):ℝ):ℂ) + ((0.9903157283908:ℝ):ℂ) * I)‖ ≤ 0.00000015619 := by
  have hl := lg_35
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.688143900879052106 73.688143942331114284 1.7100798 0.00000005618 (-0.1388335625895) 0.9903157283908 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_36 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4300842770757:ℝ):ℂ) + ((0.9027887430691:ℝ):ℂ) * I)‖ ≤ 0.0000001522 := by
  have hl := lg_36
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.272013496890814128 74.27201353834285558 1.1262102 0.00000005219 0.4300842770757 0.9027887430691 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_37 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8481362421278:ℝ):ℂ) + ((0.5297781750784:ℝ):ℂ) * I)‖ ≤ 0.00000015026 := by
  have hl := lg_37
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.839884635913664892 74.83988467736572707 0.558339 0.00000005025 0.8481362421278 0.5297781750784 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_38 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999842477182:ℝ):ℂ) + ((0.005612870528:ℝ):ℂ) * I)‖ ≤ 0.00000016123 := by
  have hl := lg_38
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.392610724938533778 75.392610766390595956 0.0056129 0.00000006122 0.9999842477182 0.005612870528 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_39 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.86141105356:ℝ):ℂ) + (((-0.507908453173):ℝ):ℂ) * I)‖ ≤ 0.00000013004 := by
  have hl := lg_39
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.930978656132521264 75.930978697584583442 (-0.532755) 0.00000003003 0.86141105356 (-0.507908453173) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_40 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4910584967117:ℝ):ℂ) + (((-0.8711265997587):ℝ):ℂ) * I)‖ ≤ 0.00000014714 := by
  have hl := lg_40
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.455715539027295734 76.45571559084231646 (-1.0574919) 0.00000004713 0.4910584967117 (-0.8711265997587) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_41 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0015253262034:ℝ):ℂ) + (((-0.9999988366892):ℝ):ℂ) * I)‖ ≤ 0.00000015859 := by
  have hl := lg_41
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.96749462757532508 76.967494679390366532 (-1.569271) 0.00000005858 0.0015253262034 (-0.9999988366892) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_42 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4775995468461):ℝ):ℂ) + (((-0.8785776419002):ℝ):ℂ) * I)‖ ≤ 0.0000001423 := by
  have hl := lg_42
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.466940486990563436 77.466940528442625614 (-2.0687168) 0.00000004229 (-0.4775995468461) (-0.8785776419002) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_43 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8336111555307):ℝ):ℂ) + (((-0.5523517369488):ℝ):ℂ) * I)‖ ≤ 0.00000013163 := by
  have hl := lg_43
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.95463357631424428 77.954633617766327184 (-2.5564099) 0.00000003162 (-0.8336111555307) (-0.5523517369488) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_44 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9940977576678):ℝ):ℂ) + (((-0.1084880073528):ℝ):ℂ) * I)‖ ≤ 0.00000016052 := by
  have hl := lg_44
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.431114325651714958 78.43111437746675641 (-3.0328907) 0.00000006051 (-0.9940977576678) (-0.1084880073528) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_45 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9369248098152):ℝ):ℂ) + ((0.3495309722755:ℝ):ℂ) * I)‖ ≤ 0.00000015192 := by
  have hl := lg_45
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.896886741429109862 78.89688678288117204 2.7845222 0.00000005191 (-0.9369248098152) 0.3495309722755 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_46 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6876091433915):ℝ):ℂ) + ((0.7260810326008:ℝ):ℂ) * I)‖ ≤ 0.00000013665 := by
  have hl := lg_46
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.352421556694799716 79.352421608509861894 2.3289874 0.00000003664 (-0.6876091433915) 0.7260810326008 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_47 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.307394240841):ℝ):ℂ) + ((0.9515822511459:ℝ):ℂ) * I)‖ ≤ 0.00000012725 := by
  have hl := lg_47
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.798159166104478854 79.798159217919561758 1.8832498 0.00000002724 (-0.307394240841) 0.9515822511459 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_48 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1235827711655:ℝ):ℂ) + ((0.9923342676089:ℝ):ℂ) * I)‖ ≤ 0.00000016821 := by
  have hl := lg_48
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.234512125138807064 80.23451217695382779 1.4468968 0.0000000682 0.1235827711655 0.9923342676089 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_49 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5237565877544:ℝ):ℂ) + ((0.8518679691031:ℝ):ℂ) * I)‖ ≤ 0.00000012522 := by
  have hl := lg_49
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.661867477090312744 80.661867518542395648 1.0195415 0.00000002521 0.5237565877544 0.8518679691031 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p726_50 : ‖exp (-((((((20726:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8248722175917:ℝ):ℂ) + ((0.5653192236651:ℝ):ℂ) * I)‖ ≤ 0.00000014206 := by
  have hl := lg_50
  refine (ecis_approx ((((20726:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.080588783565591468 81.08058883538063292 0.6008202 0.00000004205 0.8248722175917 0.5653192236651 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
