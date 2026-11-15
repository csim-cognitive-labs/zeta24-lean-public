/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Base
/-!
# Certificat (V2), côté b1left (b1), angles 2

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

lemma cs_b1left_v13p984_30 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9054089339902):ℝ):ℂ) + ((0.4245405306069:ℝ):ℂ) * I)‖ ≤ 0.00000014117 := by
  have hl := lg_30
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.562344170623264032 47.562344198591292 2.7031383 0.00000004116 (-0.9054089339902) 0.4245405306069 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_31 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6239671089712):ℝ):ℂ) + ((0.7814506042662:ℝ):ℂ) * I)‖ ≤ 0.00000012353 := by
  have hl := lg_31
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.020877052979956192 48.020877080947998144 2.2446054 0.00000002352 (-0.6239671089712) 0.7814506042662 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_32 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2278171314984):ℝ):ℂ) + ((0.9737039358012:ℝ):ℂ) * I)‖ ≤ 0.00000012411 := by
  have hl := lg_32
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.464850846576 48.464850881536 1.8006316 0.0000000241 (-0.2278171314984) 0.9737039358012 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_33 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1991354542311:ℝ):ℂ) + ((0.979971974532:ℝ):ℂ) * I)‖ ≤ 0.00000013244 := by
  have hl := lg_33
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.895161725006930848 48.8951617529749728 1.3703207 0.00000003243 0.1991354542311 0.979971974532 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_34 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5793568720579:ℝ):ℂ) + ((0.8150739934504:ℝ):ℂ) * I)‖ ≤ 0.0000001356 := by
  have hl := lg_34
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.312625558057013056 49.31262559301702704 0.9528569 0.00000003559 0.5793568720579 0.8150739934504 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_35 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8538310732837:ℝ):ℂ) + ((0.5205501880657:ℝ):ℂ) * I)‖ ≤ 0.00000014787 := by
  have hl := lg_35
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.717987277327639904 49.717987305295681856 0.5474952 0.00000004786 0.8538310732837 0.5205501880657 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_36 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9882337925761:ℝ):ℂ) + ((0.1529508784241:ℝ):ℂ) * I)‖ ≤ 0.00000013662 := by
  have hl := lg_36
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.111928820829930752 50.11192884879795872 0.1535536 0.00000003661 0.9882337925761 0.1529508784241 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_37 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9737589646626:ℝ):ℂ) + (((-0.2275818066967):ℝ):ℂ) * I)‖ ≤ 0.00000014642 := by
  have hl := lg_37
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.495076075876516928 50.49507610384455888 (-0.2295936) 0.00000004641 0.9737589646626 (-0.2275818066967) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_38 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8239087366468:ℝ):ℂ) + (((-0.5667225014741):ℝ):ℂ) * I)‖ ≤ 0.00000011438 := by
  have hl := lg_38
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.868004843073456352 50.868004871041498304 (-0.6025224) 0.00000001437 0.8239087366468 (-0.5667225014741) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_39 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5687889938118:ℝ):ℂ) + (((-0.8224834834321):ℝ):ℂ) * I)‖ ≤ 0.00000011548 := by
  have hl := lg_39
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.231246044936658176 51.231246072904700128 (-0.9657636) 0.00000001547 0.5687889938118 (-0.8224834834321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p984_40 : ‖exp (-((((((13984:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2483616341096:ℝ):ℂ) + (((-0.9686673829042):ℝ):ℂ) * I)‖ ≤ 0.00000014569 := by
  have hl := lg_40
  refine (ecis_approx ((((13984:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.585290268153898656 51.58529030311391264 (-1.3198078) 0.00000004568 0.2483616341096 (-0.9686673829042) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_2 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9585331520433):ℝ):ℂ) + ((0.2849810453445:ℝ):ℂ) * I)‖ ≤ 0.00000012965 := by
  have hl := lg_2
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.7137645847242 9.7137645917312 2.852606 0.00000002964 (-0.9585331520433) 0.2849810453445 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_3 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9517182779699):ℝ):ℂ) + (((-0.3069728313223):ℝ):ℂ) * I)‖ ≤ 0.00000010462 := by
  have hl := lg_3
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.395952609752010296 15.39595261675902431 (-2.829582) 0.00000000461 (-0.9517182779699) (-0.3069728313223) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_4 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8375716113776:ℝ):ℂ) + (((-0.5463275535925):ℝ):ℂ) * I)‖ ≤ 0.00000015211 := by
  have hl := lg_4
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.4275291694484 19.4275291834624 (-0.5779733) 0.0000000521 0.8375716113776 (-0.5463275535925) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_5 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8453831066339):ℝ):ℂ) + ((0.534160465541:ℝ):ℂ) * I)‖ ≤ 0.00000013117 := by
  have hl := lg_5
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.554662897565724926 22.55466291157973894 2.5780783 0.00000003116 (-0.8453831066339) 0.534160465541 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_6 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997349594206:ℝ):ℂ) + ((0.023021965866:ℝ):ℂ) * I)‖ ≤ 0.00000013426 := by
  have hl := lg_6
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.109717194476210296 25.10971720849022431 0.023024 0.00000003425 0.9997349594206 0.023021965866 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_7 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.536637605294):ℝ):ℂ) + (((-0.8438128231879):ℝ):ℂ) * I)‖ ≤ 0.00000010716 := by
  have hl := lg_7
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.269984821575403908 27.269984835589431936 (-2.1372436) 0.00000000715 (-0.536637605294) (-0.8438128231879) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_8 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6471472356338):ℝ):ℂ) + ((0.7623650407745:ℝ):ℂ) * I)‖ ≤ 0.00000013931 := by
  have hl := lg_8
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.1412937541726 29.1412937751936 2.2746328 0.0000000393 (-0.6471472356338) 0.7623650407745 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_9 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8115353657229:ℝ):ℂ) + ((0.5843033032433:ℝ):ℂ) * I)‖ ≤ 0.00000011641 := by
  have hl := lg_9
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.791905219504020592 30.79190523351804862 0.6240213 0.0000000164 0.8115353657229 0.5843033032433 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_10 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.658102131454:ℝ):ℂ) + (((-0.7529286716388):ℝ):ℂ) * I)‖ ≤ 0.00000015362 := by
  have hl := lg_10
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.268427482289924926 32.26842750331093894 (-0.852501) 0.00000005361 0.658102131454 (-0.7529286716388) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_11 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5789020084398):ℝ):ℂ) + (((-0.815397120803):ℝ):ℂ) * I)‖ ≤ 0.00000012721 := by
  have hl := lg_11
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.604104342067721462 33.60410436308874949 (-2.1881778) 0.0000000272 (-0.5789020084398) (-0.815397120803) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_12 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9648399520353):ℝ):ℂ) + ((0.2628380997992:ℝ):ℂ) * I)‖ ≤ 0.00000015716 := by
  have hl := lg_12
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.823481779200410296 34.82348180022142431 2.8756301 0.00000005715 (-0.9648399520353) 0.2628380997992 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_13 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1820935433007):ℝ):ℂ) + ((0.9832812118044:ℝ):ℂ) * I)‖ ≤ 0.00000015856 := by
  have hl := lg_13
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.9452002845373438 35.945200305558371828 1.7539115 0.00000005855 (-0.1820935433007) 0.9832812118044 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_14 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7548555958803:ℝ):ℂ) + ((0.6558910194294:ℝ):ℂ) * I)‖ ≤ 0.00000013679 := by
  have hl := lg_14
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.983749406299603908 36.983749427320631936 0.7153624 0.00000003678 0.7548555958803 0.6558910194294 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_15 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9685393051069:ℝ):ℂ) + (((-0.2488606326098):ℝ):ℂ) * I)‖ ≤ 0.00000013577 := by
  have hl := lg_15
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.950615507317735222 37.95061552833876325 (-0.2515037) 0.00000003576 0.9685393051069 (-0.2488606326098) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_16 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4030524998889:ℝ):ℂ) + (((-0.9151768584997):ℝ):ℂ) * I)‖ ≤ 0.00000012386 := by
  have hl := lg_16
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.8550583388968 38.8550583669248 (-1.1559465) 0.00000002385 0.4030524998889 (-0.9151768584997) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_17 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4211779324339):ℝ):ℂ) + (((-0.9069780312813):ℝ):ℂ) * I)‖ ≤ 0.00000015406 := by
  have hl := lg_17
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.704651789032306076 39.70465181706032009 (-2.00554) 0.00000005405 (-0.4211779324339) (-0.9069780312813) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_18 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9443989159678):ℝ):ℂ) + (((-0.3288018967852):ℝ):ℂ) * I)‖ ≤ 0.00000013886 := by
  have hl := lg_18
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.505669804228220592 40.50566982524924862 (-2.806558) 0.00000003885 (-0.9443989159678) (-0.3288018967852) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_19 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9119996928149):ℝ):ℂ) + ((0.4101908826073:ℝ):ℂ) * I)‖ ≤ 0.00000011389 := by
  have hl := lg_19
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.263367843109854442 41.263367864130896484 2.7189293 0.00000001388 (-0.9119996928149) 0.4101908826073 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_20 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4162424014082):ℝ):ℂ) + ((0.9092536847691:ℝ):ℂ) * I)‖ ≤ 0.0000001448 := by
  have hl := lg_20
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.982192067014124926 41.98219209504213894 2.0001051 0.00000004479 (-0.4162424014082) 0.9092536847691 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_21 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2517002130609:ℝ):ℂ) + ((0.9678052504224:ℝ):ℂ) * I)‖ ≤ 0.00000011894 := by
  have hl := lg_21
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.665937431327414204 42.665937452348456246 1.3163597 0.00000001893 0.2517002130609 0.9678052504224 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_22 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.787269490878:ℝ):ℂ) + ((0.6166090728595:ℝ):ℂ) * I)‖ ≤ 0.00000012348 := by
  have hl := lg_22
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.317868926791921462 43.31786895481994949 0.6644282 0.00000002347 0.787269490878 0.6166090728595 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_23 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9991397783818:ℝ):ℂ) + ((0.0414693049761:ℝ):ℂ) * I)‖ ≤ 0.00000012281 := by
  have hl := lg_23
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.940815927459575124 43.940815955487617166 0.0414812 0.0000000228 0.9991397783818 0.0414693049761 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_24 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8499272078928:ℝ):ℂ) + (((-0.526900124581):ℝ):ℂ) * I)‖ ≤ 0.00000014171 := by
  have hl := lg_24
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.537246363924610296 44.53724639195262431 (-0.5549492) 0.0000000417 0.8499272078928 (-0.526900124581) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_25 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4293452005062:ℝ):ℂ) + (((-0.9031404646024):ℝ):ℂ) * I)‖ ≤ 0.00000015514 := by
  have hl := lg_25
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.109325795131449852 45.10932582315947788 (-1.1270287) 0.00000005513 0.4293452005062 (-0.9031404646024) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_26 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1056737031016):ℝ):ℂ) + (((-0.9944008590465):ℝ):ℂ) * I)‖ ≤ 0.00000014705 := by
  have hl := lg_26
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.6589648692615438 45.658964897289571828 (-1.6766677) 0.00000004704 (-0.1056737031016) (-0.9944008590465) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_27 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5929878014266):ℝ):ℂ) + (((-0.8052114426334):ℝ):ℂ) * I)‖ ≤ 0.00000012102 := by
  have hl := lg_27
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.187857829256030888 46.18785785027707293 (-2.2055607) 0.00000002101 (-0.5929878014266) (-0.8052114426334) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_28 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9104706191374):ℝ):ℂ) + (((-0.4135737558867):ℝ):ℂ) * I)‖ ≤ 0.00000015925 := by
  have hl := lg_28
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.697513991023803908 46.697514019051831936 (-2.7152169) 0.00000005924 (-0.9104706191374) (-0.4135737558867) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_29 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9978625770257):ℝ):ℂ) + ((0.0653473551902:ℝ):ℂ) * I)‖ ≤ 0.00000011747 := by
  have hl := lg_29
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.189283746858941688 47.18928377488698373 3.0761987 0.00000001746 (-0.9978625770257) 0.0653473551902 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_30 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.857456521264):ℝ):ℂ) + ((0.514556424567:ℝ):ℂ) * I)‖ ≤ 0.00000016265 := by
  have hl := lg_30
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.664380092041935222 47.66438012006996325 2.6011024 0.00000006264 (-0.857456521264) 0.514556424567 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_31 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5402965387581):ℝ):ℂ) + ((0.8414746877939:ℝ):ℂ) * I)‖ ≤ 0.00000013969 := by
  have hl := lg_31
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.123896669083317082 48.123896697111359124 2.1415858 0.00000003968 (-0.5402965387581) 0.8414746877939 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_32 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1255311252739):ℝ):ℂ) + ((0.9920896817259:ℝ):ℂ) * I)‖ ≤ 0.00000013383 := by
  have hl := lg_32
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.568822923621 48.568822958656 1.6966595 0.00000003382 (-0.1255311252739) 0.9920896817259 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_33 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3006468665624:ℝ):ℂ) + ((0.9537355302316:ℝ):ℂ) * I)‖ ≤ 0.00000012243 := by
  have hl := lg_33
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.000056951819731758 49.0000569798477738 1.2654255 0.00000002242 0.3006468665624 0.9537355302316 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_34 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6621844838142:ℝ):ℂ) + ((0.7493408499446:ℝ):ℂ) * I)‖ ≤ 0.00000015137 := by
  have hl := lg_34
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.418416373756506076 49.41841640879152009 0.8470661 0.00000005136 0.6621844838142 0.7493408499446 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_35 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9043958164086:ℝ):ℂ) + ((0.4266945128105:ℝ):ℂ) * I)‖ ≤ 0.00000013831 := by
  have hl := lg_35
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.824647719141128834 49.824647747169170876 0.4408347 0.0000000383 0.9043958164086 0.4266945128105 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_36 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9989399735722:ℝ):ℂ) + ((0.0460318281156:ℝ):ℂ) * I)‖ ≤ 0.00000015956 := by
  have hl := lg_36
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.219434388952420592 50.21943441698044862 0.0460481 0.00000005955 0.9989399735722 0.0460318281156 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_37 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9434458809825:ℝ):ℂ) + (((-0.3315265745868):ℝ):ℂ) * I)‖ ≤ 0.00000014423 := by
  have hl := lg_37
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.603403613224650188 50.60340364125269223 (-0.3379212) 0.00000004422 0.9434458809825 (-0.3315265745868) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_38 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7572853184365:ℝ):ℂ) + (((-0.6530841802406):ℝ):ℂ) * I)‖ ≤ 0.00000012962 := by
  have hl := lg_38
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.977132427834054442 50.977132455862096484 (-0.71165) 0.00000002961 0.7572853184365 (-0.6530841802406) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_39 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4751423711526:ℝ):ℂ) + (((-0.8799089311602):ℝ):ℂ) * I)‖ ≤ 0.00000016316 := by
  have hl := lg_39
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.341152894289354096 51.341152922317396138 (-1.0756705) 0.00000006315 0.4751423711526 (-0.8799089311602) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p014_40 : ‖exp (-((((((14014:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1398620825039:ℝ):ℂ) + (((-0.9901709942619):ℝ):ℂ) * I)‖ ≤ 0.00000012935 := by
  have hl := lg_40
  refine (ecis_approx ((((14014:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.695956651738324926 51.69595668677333894 (-1.4304742) 0.00000002934 0.1398620825039 (-0.9901709942619) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_2 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9524003384768):ℝ):ℂ) + ((0.3048501190082:ℝ):ℂ) * I)‖ ≤ 0.00000011424 := by
  have hl := lg_2
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.7345590001332 9.7345590071552 2.8318116 0.00000001423 (-0.9524003384768) 0.3048501190082 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_3 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9613169216355):ℝ):ℂ) + (((-0.2754446876228):ℝ):ℂ) * I)‖ ≤ 0.00000013597 := by
  have hl := lg_3
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.428910978404255216 15.42891098542626926 (-2.8625404) 0.00000003596 (-0.9613169216355) (-0.2754446876228) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_4 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.814132813918:ℝ):ℂ) + (((-0.5806787074639):ℝ):ℂ) * I)‖ ≤ 0.00000012129 := by
  have hl := lg_4
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.4691180002664 19.4691180143104 (-0.6195621) 0.00000002128 0.814132813918 (-0.5806787074639) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_5 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8186169916396):ℝ):ℂ) + ((0.5743398131263:ℝ):ℂ) * I)‖ ≤ 0.00000012026 := by
  have hl := lg_5
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.602946034923151196 22.60294604896716524 2.5297952 0.00000002025 (-0.8186169916396) 0.5743398131263 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_6 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9995279075752:ℝ):ℂ) + (((-0.0307239642366):ℝ):ℂ) * I)‖ ≤ 0.0000001502 := by
  have hl := lg_6
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.163469978537455216 25.16346999258146926 (-0.0307288) 0.00000005019 0.9995279075752 (-0.0307239642366) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_7 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5849549992766):ℝ):ℂ) + (((-0.8110657487593):ℝ):ℂ) * I)‖ ≤ 0.00000011137 := by
  have hl := lg_7
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.328362126031466568 27.328362140075494656 (-2.1956209) 0.00000001136 (-0.5849549992766) (-0.8110657487593) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_8 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5983603944622):ℝ):ℂ) + ((0.8012270828717:ℝ):ℂ) * I)‖ ≤ 0.00000013551 := by
  have hl := lg_8
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.2036770003996 29.2036770214656 2.2122495 0.0000000355 (-0.5983603944622) 0.8012270828717 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_9 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8482603988311:ℝ):ℂ) + ((0.5295793573912:ℝ):ℂ) * I)‖ ≤ 0.00000013497 := by
  have hl := lg_9
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.857821956808510432 30.85782197085253852 0.5581046 0.00000003496 0.8482603988311 0.5295793573912 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_10 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6045635452583:ℝ):ℂ) + (((-0.7965569155714):ℝ):ℂ) * I)‖ ≤ 0.00000012024 := by
  have hl := lg_10
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.337505035056351196 32.33750505612236524 (-0.9215785) 0.00000002023 0.6045635452583 (-0.7965569155714) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_11 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6360113324395):ℝ):ℂ) + (((-0.7716797165879):ℝ):ℂ) * I)‖ ≤ 0.00000013568 := by
  have hl := lg_11
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.676041200228277452 33.67604122129430554 (-2.2601147) 0.00000003567 (-0.6360113324395) (-0.7716797165879) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_12 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9425845467426):ℝ):ℂ) + ((0.3339676212702:ℝ):ℂ) * I)‖ ≤ 0.00000015667 := by
  have hl := lg_12
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.898028978670655216 34.89802899973666926 2.8010829 0.00000005666 (-0.9425845467426) 0.3339676212702 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_13 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1059674445004):ℝ):ℂ) + ((0.9943695996487:ℝ):ℂ) * I)‖ ≤ 0.00000014324 := by
  have hl := lg_13
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.0221487652377948 36.022148786303822888 1.6769631 0.00000004323 (-0.1059674445004) 0.9943695996487 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_14 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8043648294722:ℝ):ℂ) + ((0.5941356925047:ℝ):ℂ) * I)‖ ≤ 0.00000011693 := by
  have hl := lg_14
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.062921126164666568 37.062921147230694656 0.6361907 0.00000001692 0.8043648294722 0.5941356925047 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_15 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9451492169806:ℝ):ℂ) + (((-0.326638879561):ℝ):ℂ) * I)‖ ≤ 0.00000012977 := by
  have hl := lg_15
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.031857013327406412 38.0318570343934345 (-0.3327452) 0.00000002976 0.9451492169806 (-0.326638879561) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_16 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3256244773961:ℝ):ℂ) + (((-0.9454991801797):ℝ):ℂ) * I)‖ ≤ 0.00000014256 := by
  have hl := lg_16
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.9382360005328 38.9382360286208 (-1.2391242) 0.00000004255 0.3256244773961 (-0.9454991801797) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_17 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4966545516031):ℝ):ℂ) + (((-0.8679483028186):ℝ):ℂ) * I)‖ ≤ 0.00000015377 := by
  have hl := lg_17
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.789648189322799096 39.78964821741081314 (-2.0905364) 0.00000005376 (-0.4966545516031) (-0.8679483028186) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_18 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.969325819341):ℝ):ℂ) + (((-0.2457792824676):ℝ):ℂ) * I)‖ ≤ 0.00000013495 := by
  have hl := lg_18
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.592380956941710432 40.59238097800773852 (-2.8932691) 0.00000003494 (-0.969325819341) (-0.2457792824676) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_19 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.872257579545):ℝ):ℂ) + ((0.4890467409529:ℝ):ℂ) * I)‖ ≤ 0.00000013781 := by
  have hl := lg_19
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.351701012461452532 41.351701033527494664 2.6305961 0.0000000378 (-0.872257579545) 0.4890467409529 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_20 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3329560545852):ℝ):ℂ) + ((0.9429423448509:ℝ):ℂ) * I)‖ ≤ 0.00000011508 := by
  have hl := lg_20
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.072064035189551196 42.07206406327756524 1.9102331 0.00000001507 (-0.3329560545852) 0.9429423448509 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_21 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3389233940984:ℝ):ℂ) + ((0.9408139736063:ℝ):ℂ) * I)‖ ≤ 0.00000014584 := by
  have hl := lg_21
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.757273104435721784 42.757273125501763916 1.225024 0.00000004583 0.3389233940984 0.9408139736063 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_22 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8409840618644:ℝ):ℂ) + ((0.5410598928863:ℝ):ℂ) * I)‖ ≤ 0.00000014991 := by
  have hl := lg_22
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.410600200361477452 43.41060022844950554 0.5716969 0.0000000499 0.8409840618644 0.5410598928863 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_23 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9986178010353:ℝ):ℂ) + (((-0.0525593707677):ℝ):ℂ) * I)‖ ≤ 0.00000013175 := by
  have hl := lg_23
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.034880753906256104 44.034880781994298236 (-0.0525836) 0.00000003174 0.9986178010353 (-0.0525593707677) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_24 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7959077766845:ℝ):ℂ) + (((-0.6054178813127):ℝ):ℂ) * I)‖ ≤ 0.00000015665 := by
  have hl := lg_24
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.632587978803855216 44.63258800689186926 (-0.6502908) 0.00000005664 0.7959077766845 (-0.6054178813127) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_25 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3402675647943:ℝ):ℂ) + (((-0.940328657624):ℝ):ℂ) * I)‖ ≤ 0.00000014769 := by
  have hl := lg_25
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.205892069846302392 45.20589209793433048 (-1.2235949) 0.00000004768 0.3402675647943 (-0.940328657624) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_26 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2022102538502):ℝ):ℂ) + (((-0.9793421328815):ℝ):ℂ) * I)‖ ≤ 0.00000014322 := by
  have hl := lg_26
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.7567077653709948 45.756707793459022888 (-1.7744106) 0.00000004321 (-0.2022102538502) (-0.9793421328815) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_27 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6695772546903):ℝ):ℂ) + (((-0.7427424183269):ℝ):ℂ) * I)‖ ≤ 0.00000011506 := by
  have hl := lg_27
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.286732935212765648 46.28673295627880778 (-2.3044358) 0.00000001505 (-0.6695772546903) (-0.7427424183269) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_28 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9471996701694):ℝ):ℂ) + (((-0.320644327308):ℝ):ℂ) * I)‖ ≤ 0.00000012397 := by
  have hl := lg_28
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.797480126297866568 46.797480154385894656 (-2.815183) 0.00000002396 (-0.9471996701694) (-0.320644327308) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_29 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9861853062489):ℝ):ℂ) + ((0.1656458311246:ℝ):ℂ) * I)‖ ≤ 0.00000013572 := by
  have hl := lg_29
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.290302621727342448 47.29030264981538458 2.9751798 0.00000003571 (-0.9861853062489) 0.1656458311246 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_30 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8005845328823):ℝ):ℂ) + ((0.5992198308303:ℝ):ℂ) * I)‖ ≤ 0.00000014399 := by
  have hl := lg_30
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.766416013460606412 47.7664160415486345 2.4990664 0.00000004398 (-0.8005845328823) 0.5992198308303 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_31 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4508968504915):ℝ):ℂ) + ((0.8925760641045:ℝ):ℂ) * I)‖ ≤ 0.00000015585 := by
  have hl := lg_31
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.226916285186677972 48.226916313274720104 2.0385662 0.00000005584 (-0.4508968504915) 0.8925760641045 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_32 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0218893248104):ℝ):ℂ) + ((0.9997604000255:ℝ):ℂ) * I)‖ ≤ 0.00000015679 := by
  have hl := lg_32
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.672795000666 48.672795035776 1.5926874 0.00000005678 (-0.0218893248104) 0.9997604000255 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_33 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3988532925897:ℝ):ℂ) + ((0.9170147496035:ℝ):ℂ) * I)‖ ≤ 0.0000001493 := by
  have hl := lg_33
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.104952178632532668 49.1049522067205748 1.1605303 0.00000004929 0.3988532925897 0.9170147496035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_34 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7376080390701:ℝ):ℂ) + ((0.6752291319983:ℝ):ℂ) * I)‖ ≤ 0.00000016714 := by
  have hl := lg_34
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.524207189455999096 49.52420722456601314 0.7412753 0.00000006713 0.7376080390701 0.6752291319983 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_35 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9446814523651:ℝ):ℂ) + ((0.3279892582957:ℝ):ℂ) * I)‖ ≤ 0.00000013162 := by
  have hl := lg_35
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.931308160954617764 49.931308189042659896 0.3341743 0.00000003161 0.9446814523651 0.3279892582957 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_36 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9981120821851:ℝ):ℂ) + (((-0.0614188195604):ℝ):ℂ) * I)‖ ≤ 0.00000012774 := by
  have hl := lg_36
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.326939957074910432 50.32693998516293852 (-0.0614575) 0.00000002773 0.9981120821851 (-0.0614188195604) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_37 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9020724490822:ℝ):ℂ) + (((-0.4315846343498):ℝ):ℂ) * I)‖ ≤ 0.00000012124 := by
  have hl := lg_37
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.711731150572783448 50.71173117866082558 (-0.4462487) 0.00000002123 0.9020724490822 (-0.4315846343498) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_38 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6816524620912:ℝ):ℂ) + (((-0.7316761038363):ℝ):ℂ) * I)‖ ≤ 0.00000014486 := by
  have hl := lg_38
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.086260012594652532 51.086260040682694664 (-0.8207776) 0.00000004485 0.6816524620912 (-0.7316761038363) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_39 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3757621214278:ℝ):ℂ) + (((-0.9267161529293):ℝ):ℂ) * I)‖ ≤ 0.00000011431 := by
  have hl := lg_39
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.451059743642050016 51.451059771730092148 (-1.1855773) 0.0000000143 0.3757621214278 (-0.9267161529293) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p044_40 : ‖exp (-((((((14044:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0296513801379:ℝ):ℂ) + (((-0.9995603011603):ℝ):ℂ) * I)‖ ≤ 0.00000012213 := by
  have hl := lg_40
  refine (ecis_approx ((((14044:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.806623035322751196 51.80662307043276524 (-1.5411406) 0.00000002212 0.0296513801379 (-0.9995603011603) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_2 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9458557151078):ℝ):ℂ) + ((0.3245873780741:ℝ):ℂ) * I)‖ ≤ 0.00000010824 := by
  have hl := lg_2
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.7553534155422 9.7553534225792 2.8110172 0.00000000823 (-0.9458557151078) 0.3245873780741 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_3 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9698713990596):ℝ):ℂ) + (((-0.2436174645117):ℝ):ℂ) * I)‖ ≤ 0.00000013975 := by
  have hl := lg_3
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.461869347056500136 15.46186935409351421 (-2.8954987) 0.00000003974 (-0.9698713990596) (-0.2436174645117) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_4 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7892860722679:ℝ):ℂ) + (((-0.6140256477736):ℝ):ℂ) * I)‖ ≤ 0.00000012363 := by
  have hl := lg_4
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.5107068310844 19.5107068451584 (-0.6611509) 0.00000002362 0.7892860722679 (-0.6140256477736) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_5 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7899427788439):ℝ):ℂ) + ((0.613180565663:ℝ):ℂ) * I)‖ ≤ 0.00000015645 := by
  have hl := lg_5
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.651229172280577466 22.65122918635459154 2.481512 0.00000005644 (-0.7899427788439) 0.613180565663 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_6 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.996433560013:ℝ):ℂ) + (((-0.0843810433673):ℝ):ℂ) * I)‖ ≤ 0.00000014797 := by
  have hl := lg_6
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.217222762598700136 25.21722277667271421 (-0.0844815) 0.00000004796 0.996433560013 (-0.0843810433673) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_7 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6312794858284):ℝ):ℂ) + (((-0.7755554208162):ℝ):ℂ) * I)‖ ≤ 0.00000011586 := by
  have hl := lg_7
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.386739430487529228 27.386739444561557376 (-2.2539982) 0.00000001585 (-0.6312794858284) (-0.7755554208162) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_8 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5472457672197):ℝ):ℂ) + ((0.8369719650333:ℝ):ℂ) * I)‖ ≤ 0.00000013185 := by
  have hl := lg_8
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.2660602466266 29.2660602677376 2.1498663 0.00000003184 (-0.5472457672197) 0.8369719650333 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_9 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8813011124848:ℝ):ℂ) + ((0.4725551281417:ℝ):ℂ) * I)‖ ≤ 0.0000001418 := by
  have hl := lg_9
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.923738694113000272 30.92373870818702842 0.4921878 0.00000004179 0.8813011124848 0.4725551281417 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_10 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5481412258799:ℝ):ℂ) + (((-0.8363857940513):ℝ):ℂ) * I)‖ ≤ 0.00000014809 := by
  have hl := lg_10
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.406582587822777466 32.40658260893379154 (-0.9906561) 0.00000004808 0.5481412258799 (-0.8363857940513) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_11 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6898306969236):ℝ):ℂ) + (((-0.7239707242422):ℝ):ℂ) * I)‖ ≤ 0.00000014362 := by
  have hl := lg_11
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.747978058388833442 33.74797807949986159 (-2.3320515) 0.00000004361 (-0.6898306969236) (-0.7239707242422) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_12 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9150933558544):ℝ):ℂ) + ((0.4032420488187:ℝ):ℂ) * I)‖ ≤ 0.00000015619 := by
  have hl := lg_12
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.972576178140900136 34.97257619925191421 2.7265357 0.00000005618 (-0.9150933558544) 0.4032420488187 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_13 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0292141160728):ℝ):ℂ) + ((0.9995731766218:ℝ):ℂ) * I)‖ ≤ 0.00000012399 := by
  have hl := lg_13
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.0990972459382458 36.099097267049273948 1.6000146 0.00000002398 (-0.0292141160728) 0.9995731766218 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_14 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8488348102196:ℝ):ℂ) + ((0.5286581740212:ℝ):ℂ) * I)‖ ≤ 0.00000012408 := by
  have hl := lg_14
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.142092846029729228 37.142092867140757376 0.557019 0.00000002407 0.8488348102196 0.5286581740212 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_15 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9155244029711:ℝ):ℂ) + (((-0.4022624361837):ℝ):ℂ) * I)‖ ≤ 0.00000012376 := by
  have hl := lg_15
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.113098519337077602 38.11309854044810575 (-0.4139867) 0.00000002375 0.9155244029711 (-0.4022624361837) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_16 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2459450077523:ℝ):ℂ) + (((-0.9692837836061):ℝ):ℂ) * I)‖ ≤ 0.00000014725 := by
  have hl := lg_16
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.0214136621688 39.0214136903168 (-1.3223018) 0.00000004724 0.2459450077523 (-0.9692837836061) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_17 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.56854530517):ℝ):ℂ) + (((-0.8226519531122):ℝ):ℂ) * I)‖ ≤ 0.00000015348 := by
  have hl := lg_17
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.874644589613292116 39.87464461776130619 (-2.1755328) 0.00000005347 (-0.56854530517) (-0.8226519531122) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_18 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9869691228043):ℝ):ℂ) + (((-0.1609097581074):ℝ):ℂ) * I)‖ ≤ 0.00000013344 := by
  have hl := lg_18
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.679092109655200272 40.67909213076622842 (-2.9799803) 0.00000003343 (-0.9869691228043) (-0.1609097581074) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_19 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8257139354846):ℝ):ℂ) + ((0.5640890857711:ℝ):ℂ) * I)‖ ≤ 0.00000015268 := by
  have hl := lg_19
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.440034181813050622 41.440034202924092844 2.542263 0.00000005267 (-0.8257139354846) 0.5640890857711 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_20 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2469822391882):ℝ):ℂ) + ((0.969020006772:ℝ):ℂ) * I)‖ ≤ 0.00000014691 := by
  have hl := lg_20
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.161936003364977466 42.16193603151299154 1.8203611 0.0000000469 (-0.2469822391882) 0.969020006772 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_21 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4233210793749:ℝ):ℂ) + ((0.9059797259083:ℝ):ℂ) * I)‖ ≤ 0.00000014841 := by
  have hl := lg_21
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.848608777544029364 42.848608798655071586 1.1336884 0.0000000484 0.4233210793749 0.9059797259083 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_22 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8874720664523:ℝ):ℂ) + ((0.4608615098562:ℝ):ℂ) * I)‖ ≤ 0.00000015184 := by
  have hl := lg_22
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.503331473931033442 43.50333150207906159 0.4789657 0.00000005183 0.8874720664523 0.4608615098562 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_23 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9892663803055:ℝ):ℂ) + (((-0.1461233341981):ℝ):ℂ) * I)‖ ≤ 0.00000015826 := by
  have hl := lg_23
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.128945580352937084 44.128945608500979306 (-0.1466484) 0.00000005825 0.9892663803055 (-0.1461233341981) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_24 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7346589382016:ℝ):ℂ) + (((-0.6784366179095):ℝ):ℂ) * I)‖ ≤ 0.00000015659 := by
  have hl := lg_24
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.727929593683100136 44.72792962183111421 (-0.7456325) 0.00000005658 0.7346589382016 (-0.6784366179095) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_25 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2480192915544:ℝ):ℂ) + (((-0.9687550934146):ℝ):ℂ) * I)‖ ≤ 0.00000012247 := by
  have hl := lg_25
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.302458344561154932 45.30245837270918308 (-1.3201612) 0.00000002246 0.2480192915544 (-0.9687550934146) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_26 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2968164911862):ℝ):ℂ) + (((-0.9549345373156):ℝ):ℂ) * I)‖ ≤ 0.00000013939 := by
  have hl := lg_26
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.8544506614804458 45.854450689628473948 (-1.8721535) 0.00000003938 (-0.2968164911862) (-0.9549345373156) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_27 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7396260608218):ℝ):ℂ) + (((-0.673018045911):ℝ):ℂ) * I)‖ ≤ 0.00000011204 := by
  have hl := lg_27
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.385608041169500408 46.38560806228054263 (-2.4033109) 0.00000001203 (-0.7396260608218) (-0.673018045911) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_28 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9744710254137):ℝ):ℂ) + (((-0.2245132965693):ℝ):ℂ) * I)‖ ≤ 0.00000013948 := by
  have hl := lg_28
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.897446261571929228 46.897446289719957376 (-2.9151491) 0.00000003947 (-0.9744710254137) (-0.2245132965693) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_29 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9644527491118):ℝ):ℂ) + ((0.2642553584732:ℝ):ℂ) * I)‖ ≤ 0.00000016086 := by
  have hl := lg_29
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.391321496595743208 47.39132152474378543 2.8741609 0.00000006085 (-0.9644527491118) 0.2642553584732 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_30 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7353846794288):ℝ):ℂ) + ((0.6776498898627:ℝ):ℂ) * I)‖ ≤ 0.00000012257 := by
  have hl := lg_30
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.868451934879277602 47.86845196302730575 2.3970305 0.00000002256 (-0.7353846794288) 0.6776498898627 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_31 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3567159141949):ℝ):ℂ) + ((0.9342129075096:ℝ):ℂ) * I)‖ ≤ 0.00000015616 := by
  have hl := lg_31
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.329935901290038862 48.329935929438081084 1.9355465 0.00000005615 (-0.3567159141949) 0.9342129075096 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_32 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0819887908265:ℝ):ℂ) + ((0.9966332515919:ℝ):ℂ) * I)‖ ≤ 0.00000015547 := by
  have hl := lg_32
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.776767077711 48.776767112896 1.4887154 0.00000005546 0.0819887908265 0.9966332515919 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_33 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4926752441616:ℝ):ℂ) + ((0.8702132519046:ℝ):ℂ) * I)‖ ≤ 0.00000015201 := by
  have hl := lg_33
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.209847405445333578 49.2098474335933758 1.055635 0.000000052 0.4926752441616 0.8702132519046 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_34 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8047842668444:ℝ):ℂ) + ((0.5935674214778:ℝ):ℂ) * I)‖ ≤ 0.0000001523 := by
  have hl := lg_34
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.629998005155492116 49.62999804034050619 0.6354844 0.00000005229 0.8047842668444 0.5935674214778 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_35 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9742301829333:ℝ):ℂ) + ((0.2255560920519:ℝ):ℂ) * I)‖ ≤ 0.00000015468 := by
  have hl := lg_35
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.037968602768106694 50.037968630916148916 0.2275138 0.00000005467 0.9742301829333 0.2255560920519 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_36 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9857596622245:ℝ):ℂ) + (((-0.1681603054561):ℝ):ℂ) * I)‖ ≤ 0.00000013225 := by
  have hl := lg_36
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.434445525197400272 50.43444555334542842 (-0.1689631) 0.00000003224 0.9857596622245 (-0.1681603054561) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_37 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.85012368251:ℝ):ℂ) + (((-0.5265830650863):ℝ):ℂ) * I)‖ ≤ 0.00000015865 := by
  have hl := lg_37
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.820058687920916708 50.82005871606895893 (-0.5545762) 0.00000005864 0.85012368251 (-0.5265830650863) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_38 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5979099731712:ℝ):ℂ) + (((-0.8015632626202):ℝ):ℂ) * I)‖ ≤ 0.0000001601 := by
  have hl := lg_38
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.195387597355250622 51.195387625503292844 (-0.9299052) 0.00000006009 0.5979099731712 (-0.8015632626202) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_39 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2718474186501:ℝ):ℂ) + (((-0.9623403664885):ℝ):ℂ) * I)‖ ≤ 0.00000016372 := by
  have hl := lg_39
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.560966592994745936 51.560966621142788158 (-1.2954841) 0.00000006371 0.2718474186501 (-0.9623403664885) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p074_40 : ‖exp (-((((((14074:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0809220937582):ℝ):ℂ) + (((-0.9967204295796):ℝ):ℂ) * I)‖ ≤ 0.00000013854 := by
  have hl := lg_40
  refine (ecis_approx ((((14074:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.917289418907177466 51.91728945409219154 (-1.651807) 0.00000003853 (-0.0809220937582) (-0.9967204295796) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_2 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9362505784975):ℝ):ℂ) + ((0.3513329675557:ℝ):ℂ) * I)‖ ≤ 0.00000014265 := by
  have hl := lg_2
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.7837724499345 9.783772456992 2.7825982 0.00000004264 (-0.9362505784975) 0.3513329675557 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_3 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9798572642274):ℝ):ℂ) + (((-0.1996991272324):ℝ):ℂ) * I)‖ ≤ 0.00000014359 := by
  have hl := lg_3
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.50691245088123486 15.506912457938748975 (-2.9405418) 0.00000004358 (-0.9798572642274) (-0.1996991272324) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_4 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7531302306263:ℝ):ℂ) + (((-0.657871458354):ℝ):ℂ) * I)‖ ≤ 0.00000012168 := by
  have hl := lg_4
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.567544899869 19.567544913984 (-0.717989) 0.00000002167 0.7531302306263 (-0.657871458354) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_5 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7477910629514):ℝ):ℂ) + ((0.6639341278597:ℝ):ℂ) * I)‖ ≤ 0.00000011208 := by
  have hl := lg_5
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.717216126669060035 22.71721614078407415 2.4155251 0.00000001207 (-0.7477910629514) 0.6639341278597 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_6 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9875528019928:ℝ):ℂ) + (((-0.157287835754):ℝ):ℂ) * I)‖ ≤ 0.00000012792 := by
  have hl := lg_6
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.29068490081573486 25.290684914930748975 (-0.1579437) 0.00000002791 0.9875528019928 (-0.157287835754) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_7 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6910814105783):ℝ):ℂ) + (((-0.7227769254277):ℝ):ℂ) * I)‖ ≤ 0.00000013199 := by
  have hl := lg_7
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.46652174657748153 27.46652176069250976 (-2.3337805) 0.00000003198 (-0.6910814105783) (-0.7227769254277) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_8 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4739866823582):ℝ):ℂ) + ((0.8805320124457:ℝ):ℂ) * I)‖ ≤ 0.00000013509 := by
  have hl := lg_8
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.3513173498035 29.351317370976 2.0646092 0.00000003508 (-0.4739866823582) 0.8805320124457 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_9 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9202405589824:ℝ):ℂ) + ((0.3913531826927:ℝ):ℂ) * I)‖ ≤ 0.00000013415 := by
  have hl := lg_9
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.01382490176246972 31.01382491587749795 0.4021016 0.00000003414 0.9202405589824 0.3913531826927 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_10 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4668577857788:ℝ):ℂ) + (((-0.8843324080105):ℝ):ℂ) * I)‖ ≤ 0.00000015931 := by
  have hl := lg_10
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.500988576603560035 32.50098859777607415 (-1.0850621) 0.0000000593 0.4668577857788 (-0.8843324080105) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_11 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.757561209193):ℝ):ℂ) + (((-0.6527641337345):ℝ):ℂ) * I)‖ ≤ 0.00000014983 := by
  have hl := lg_11
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.846291764541593295 33.846291785714121525 (-2.4303652) 0.00000004982 (-0.757561209193) (-0.6527641337345) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_12 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8693364800865):ℝ):ℂ) + ((0.4942206838077:ℝ):ℂ) * I)‖ ≤ 0.00000012886 := by
  have hl := lg_12
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.07445735075023486 35.074457371922748975 2.6246545 0.00000002885 (-0.8693364800865) 0.4942206838077 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_13 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0758716449792:ℝ):ℂ) + ((0.9971175926078:ℝ):ℂ) * I)‖ ≤ 0.00000014767 := by
  have hl := lg_13
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.2042601695621955 36.20426019073472373 1.4948517 0.00000004766 0.0758716449792 0.9971175926078 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_14 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9009607760365:ℝ):ℂ) + ((0.4339005416494:ℝ):ℂ) * I)‖ ≤ 0.00000014658 := by
  have hl := lg_14
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.25029419651198153 37.25029421768450976 0.4488176 0.00000004657 0.9009607760365 0.4339005416494 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_15 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8653155712451:ℝ):ℂ) + (((-0.5012274555137):ℝ):ℂ) * I)‖ ≤ 0.00000015566 := by
  have hl := lg_15
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.224128577550294895 38.224128598722823125 (-0.5250167) 0.00000005565 0.8653155712451 (-0.5012274555137) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_16 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1344102885665:ℝ):ℂ) + (((-0.9909257663051):ℝ):ℂ) * I)‖ ≤ 0.00000014335 := by
  have hl := lg_16
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.135089799738 39.135089827968 (-1.435978) 0.00000004334 0.1344102885665 (-0.9909257663051) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_17 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6600596576723):ℝ):ℂ) + (((-0.7512131843196):ℝ):ℂ) * I)‖ ≤ 0.00000012184 := by
  have hl := lg_17
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.99080633667696591 39.990806364906980025 (-2.2916945) 0.00000002183 (-0.6600596576723) (-0.7512131843196) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_18 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9990710302385):ℝ):ℂ) + (((-0.0430938040853):ℝ):ℂ) * I)‖ ≤ 0.00000012981 := by
  have hl := lg_18
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.79759735169696972 40.79759737286949795 (-3.0984855) 0.0000000298 (-0.9990710302385) (-0.0430938040853) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_19 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7517716685468):ℝ):ℂ) + ((0.6594235045372:ℝ):ℂ) * I)‖ ≤ 0.00000015086 := by
  have hl := lg_19
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.560756179926901345 41.56075620109944369 2.421541 0.00000005085 (-0.7517716685468) 0.6594235045372 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_20 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1264007427467):ℝ):ℂ) + ((0.991979259981:ℝ):ℂ) * I)‖ ≤ 0.00000012373 := by
  have hl := lg_20
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.284761026538060035 42.28476105476807415 1.6975361 0.00000002372 (-0.1264007427467) 0.991979259981 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_21 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5328233098104:ℝ):ℂ) + ((0.8462265184469:ℝ):ℂ) * I)‖ ≤ 0.00000015281 := by
  have hl := lg_21
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.97343419745871639 42.973434218631258735 1.0088629 0.0000000528 0.5328233098104 0.8462265184469 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_22 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9386047151882:ℝ):ℂ) + ((0.3449944762261:ℝ):ℂ) * I)‖ ≤ 0.0000001358 := by
  have hl := lg_22
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.630064214476093295 43.630064242706121525 0.3522329 0.00000003579 0.9386047151882 0.3449944762261 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_23 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9623698635503:ℝ):ℂ) + (((-0.2717429773338):ℝ):ℂ) * I)‖ ≤ 0.00000012115 := by
  have hl := lg_23
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.25750084316340109 44.257500871393443435 (-0.2752037) 0.00000002114 0.9623698635503 (-0.2717429773338) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_24 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6402806916316:ℝ):ℂ) + (((-0.7681410260647):ℝ):ℂ) * I)‖ ≤ 0.00000014959 := by
  have hl := lg_24
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.85822980068473486 44.858229828914748975 (-0.8759327) 0.00000004958 0.6402806916316 (-0.7681410260647) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_25 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1183829548056:ℝ):ℂ) + (((-0.9929680135893):ℝ):ℂ) * I)‖ ≤ 0.00000013133 := by
  have hl := lg_25
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.43443225333812007 45.4344322815681483 (-1.4521351) 0.00000003132 0.1183829548056 (-0.9929680135893) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_26 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4213552385891):ℝ):ℂ) + (((-0.9068956736636):ℝ):ℂ) * I)‖ ≤ 0.00000013078 := by
  have hl := lg_26
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.9880326194966955 45.98803264772672373 (-2.0057355) 0.00000003077 (-0.4213552385891) (-0.9068956736636) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_27 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8235515075782):ℝ):ℂ) + (((-0.5672414955787):ℝ):ℂ) * I)‖ ≤ 0.00000012357 := by
  have hl := lg_27
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.52073735264370458 46.520737373816246925 (-2.5384402) 0.00000002356 (-0.8235515075782) (-0.5672414955787) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_28 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9959686119093):ℝ):ℂ) + (((-0.0897024168966):ℝ):ℂ) * I)‖ ≤ 0.00000012443 := by
  have hl := lg_28
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.03406664644648153 47.03406667467650976 (-3.0517695) 0.00000002442 (-0.9959686119093) (-0.0897024168966) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_29 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.918908880883):ℝ):ℂ) + ((0.3944698575215:ℝ):ℂ) * I)‖ ≤ 0.00000013187 := by
  have hl := lg_29
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.52938062558255758 47.529380653812599925 2.7361018 0.00000003186 (-0.918908880883) 0.3944698575215 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_30 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6340543974696):ℝ):ℂ) + ((0.7732884462051:ℝ):ℂ) * I)‖ ≤ 0.00000012997 := by
  have hl := lg_30
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.007901027484794895 48.007901055714823125 2.2575814 0.00000002996 (-0.6340543974696) 0.7732884462051 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_31 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2220893095785):ℝ):ℂ) + ((0.9750263271163:ℝ):ℂ) * I)‖ ≤ 0.00000014744 := by
  have hl := lg_31
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.470729376631298745 48.47072940486134109 1.7947531 0.00000004743 (-0.2220893095785) 0.9750263271163 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_32 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2223031797587:ℝ):ℂ) + ((0.9749775875727:ℝ):ℂ) * I)‖ ≤ 0.00000012754 := by
  have hl := lg_32
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.9188622496725 48.91886228496 1.3466202 0.00000002753 0.2223031797587 0.9749775875727 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_33 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6119455108955:ℝ):ℂ) + ((0.7908999252085:ℝ):ℂ) * I)‖ ≤ 0.00000014203 := by
  have hl := lg_33
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.353204215422828155 49.3532042436528705 0.9122782 0.00000004202 0.6119455108955 0.7908999252085 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_34 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8819071937639:ℝ):ℂ) + ((0.4714230600931:ℝ):ℂ) * I)‖ ≤ 0.00000016448 := by
  have hl := lg_34
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.77457878661146591 49.774578821898980025 0.4909037 0.00000006447 0.8819071937639 0.4714230600931 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_35 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9966607702513:ℝ):ℂ) + ((0.0816535917285:ℝ):ℂ) * I)‖ ≤ 0.00000014405 := by
  have hl := lg_35
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.183737873246541565 50.18373790147658391 0.0817446 0.00000004404 0.9966607702513 0.0816535917285 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_36 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9505210734476:ℝ):ℂ) + (((-0.3106600858366):ℝ):ℂ) * I)‖ ≤ 0.00000015582 := by
  have hl := lg_36
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.58136980163146972 50.58136982986149795 (-0.3158874) 0.00000005581 0.9505210734476 (-0.3106600858366) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_37 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7631491935238:ℝ):ℂ) + (((-0.6462223366799):ℝ):ℂ) * I)‖ ≤ 0.00000013515 := by
  have hl := lg_37
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.96810632229669883 50.968106350526741175 (-0.7026239) 0.00000003514 0.7631491935238 (-0.6462223366799) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_38 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4721693610106:ℝ):ℂ) + (((-0.8815078527857):ℝ):ℂ) * I)‖ ≤ 0.00000012759 := by
  have hl := lg_38
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.344528629861401345 51.34452865809144369 (-1.0790462) 0.00000002758 0.4721693610106 (-0.8815078527857) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_39 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1247800314412:ℝ):ℂ) + (((-0.9921844303119):ℝ):ℂ) * I)‖ ≤ 0.00000013701 := by
  have hl := lg_39
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.71117262044343036 51.711172648673472705 (-1.4456902) 0.000000037 0.1247800314412 (-0.9921844303119) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p115_40 : ‖exp (-((((((14115:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2301722417394):ℝ):ℂ) + (((-0.9731499057862):ℝ):ℂ) * I)‖ ≤ 0.00000015434 := by
  have hl := lg_40
  refine (ecis_approx ((((14115:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.068533476472560035 52.06853351176007415 (-1.803051) 0.00000005433 (-0.2301722417394) (-0.9731499057862) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_2 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9258893019904):ℝ):ℂ) + ((0.3777949183184:ℝ):ℂ) * I)‖ ≤ 0.00000013005 := by
  have hl := lg_2
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.8121914843268 9.8121914914048 2.7541791 0.00000003004 (-0.9258893019904) 0.3777949183184 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_3 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9878554518398):ℝ):ℂ) + (((-0.1553756927113):ℝ):ℂ) * I)‖ ≤ 0.00000014744 := by
  have hl := lg_3
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.551955554705969584 15.55195556178398374 (-2.9855849) 0.00000004743 (-0.9878554518398) (-0.1553756927113) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_4 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7145420042862:ℝ):ℂ) + (((-0.6995925414916):ℝ):ℂ) * I)‖ ≤ 0.0000001529 := by
  have hl := lg_4
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.6243829686536 19.6243829828096 (-0.7748271) 0.00000005289 0.7145420042862 (-0.6995925414916) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_5 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7023843722778):ℝ):ℂ) + ((0.7117978600388:ℝ):ℂ) * I)‖ ≤ 0.00000014768 := by
  have hl := lg_5
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.783203081057542604 22.78320309521355676 2.3495381 0.00000004767 (-0.7023843722778) 0.7117978600388 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_6 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9733449421929:ℝ):ℂ) + (((-0.2293460780295):ℝ):ℂ) * I)‖ ≤ 0.00000012449 := by
  have hl := lg_6
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.364147039032769584 25.36414705318878374 (-0.2314058) 0.00000002448 0.9733449421929 (-0.2293460780295) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_7 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7464867861188):ℝ):ℂ) + (((-0.6654002390419):ℝ):ℂ) * I)‖ ≤ 0.00000014812 := by
  have hl := lg_7
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.546304062667433832 27.546304076823462144 (-2.4135628) 0.00000004811 (-0.7464867861188) (-0.6654002390419) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_8 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3972843822707):ℝ):ℂ) + ((0.9176955484258:ℝ):ℂ) * I)‖ ≤ 0.00000013833 := by
  have hl := lg_8
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.4365744529804 29.4365744742144 1.9793521 0.00000003832 (-0.3972843822707) 0.9176955484258 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_9 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9517168210148:ℝ):ℂ) + ((0.3069773486718:ℝ):ℂ) * I)‖ ≤ 0.0000001265 := by
  have hl := lg_9
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.103911109411939168 31.10391112356796748 0.3120154 0.00000002649 0.9517168210148 0.3069773486718 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_10 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3814166608368:ℝ):ℂ) + (((-0.9244032295682):ℝ):ℂ) * I)‖ ≤ 0.00000015074 := by
  have hl := lg_10
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.595394565384342604 32.59539458661835676 (-1.179468) 0.00000005073 0.3814166608368 (-0.9244032295682) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_11 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8179753461896):ℝ):ℂ) + (((-0.5752532772347):ℝ):ℂ) * I)‖ ≤ 0.00000015605 := by
  have hl := lg_11
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.944605470694353148 33.94460549192838146 (-2.5286789) 0.00000005604 (-0.8179753461896) (-0.5752532772347) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_12 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8145638863246):ℝ):ℂ) + ((0.5800738530916:ℝ):ℂ) * I)‖ ≤ 0.00000011973 := by
  have hl := lg_12
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.176338523359569584 35.17633854459358374 2.5227733 0.00000001972 (-0.8145638863246) 0.5800738530916 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_13 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1801191950191:ℝ):ℂ) + ((0.9836447913681:ℝ):ℂ) * I)‖ ≤ 0.00000014991 := by
  have hl := lg_13
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.3094230931861452 36.309423114420173512 1.3896887 0.0000000499 0.1801191950191 0.9836447913681 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_14 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9425489584053:ℝ):ℂ) + ((0.3340680484709:ℝ):ℂ) * I)‖ ≤ 0.00000012517 := by
  have hl := lg_14
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.358495546994233832 37.358495568228262144 0.3406163 0.00000002516 0.9425489584053 0.3340680484709 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_15 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.80445031727:ℝ):ℂ) + (((-0.5940199382547):ℝ):ℂ) * I)‖ ≤ 0.00000011394 := by
  have hl := lg_15
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.335158635763512188 38.3351586569975405 (-0.6360468) 0.00000001393 0.80445031727 (-0.5940199382547) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_16 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0211406517562:ℝ):ℂ) + (((-0.999776511448):ℝ):ℂ) * I)‖ ≤ 0.00000012256 := by
  have hl := lg_16
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.2487659373072 39.2487659656192 (-1.5496541) 0.00000002255 0.0211406517562 (-0.999776511448) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_17 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7426775459451):ℝ):ℂ) + (((-0.6696492087032):ℝ):ℂ) * I)‖ ≤ 0.00000015935 := by
  have hl := lg_17
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.106968083740639704 40.10696811205265386 (-2.4078563) 0.00000005934 (-0.7426775459451) (-0.6696492087032) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_18 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9971589052975):ℝ):ℂ) + ((0.0753267353886:ℝ):ℂ) * I)‖ ≤ 0.00000015653 := by
  have hl := lg_18
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.916102593738739168 40.91610261497276748 3.0661945 0.00000005652 (-0.9971589052975) 0.0753267353886 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_19 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6668865303222):ℝ):ℂ) + ((0.7451592820706:ℝ):ℂ) * I)‖ ≤ 0.00000014903 := by
  have hl := lg_19
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.681478178040752068 41.681478199274794536 2.300819 0.00000004902 (-0.6668865303222) 0.7451592820706 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_20 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0039147632059):ℝ):ℂ) + ((0.9999923372851:ℝ):ℂ) * I)‖ ≤ 0.00000012778 := by
  have hl := lg_20
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.407586049711142604 42.40758607802315676 1.5747111 0.00000002777 (-0.0039147632059) 0.9999923372851 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_21 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6340341012069:ℝ):ℂ) + ((0.7733050875992:ℝ):ℂ) * I)‖ ≤ 0.0000001329 := by
  have hl := lg_21
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.098259617373403416 43.098259638607445884 0.8840375 0.00000003289 0.6340341012069 0.7733050875992 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_22 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9746823873245:ℝ):ℂ) + ((0.2235939262132:ℝ):ℂ) * I)‖ ≤ 0.00000013309 := by
  have hl := lg_22
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.756796955021153148 43.75679698333318146 0.2255002 0.00000003308 0.9746823873245 0.2235939262132 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_23 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9195906665759:ℝ):ℂ) + (((-0.3928778511783):ℝ):ℂ) * I)‖ ≤ 0.0000001443 := by
  have hl := lg_23
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.386056105973865096 44.386056134285907564 (-0.403759) 0.00000004429 0.9195906665759 (-0.3928778511783) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_24 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5350470402465:ℝ):ℂ) + (((-0.8448222681271):ℝ):ℂ) * I)‖ ≤ 0.00000014259 := by
  have hl := lg_24
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.988530007686369584 44.98853003599838374 (-1.0062329) 0.00000004258 0.5350470402465 (-0.8448222681271) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_25 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0133122799805):ℝ):ℂ) + (((-0.9999113876747):ℝ):ℂ) * I)‖ ≤ 0.00000014019 := by
  have hl := lg_25
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.566406162115085208 45.56640619042711352 (-1.584109) 0.00000004018 (-0.0133122799805) (-0.9999113876747) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_26 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5383863491286):ℝ):ℂ) + (((-0.84269813045):ℝ):ℂ) * I)‖ ≤ 0.00000015558 := by
  have hl := lg_26
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.1216145775129452 46.121614605824973512 (-2.1393174) 0.00000005557 (-0.5383863491286) (-0.84269813045) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_27 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8924618321198):ℝ):ℂ) + (((-0.4511229079766):ℝ):ℂ) * I)‖ ≤ 0.00000013511 := by
  have hl := lg_27
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.655866664117908752 46.65586668535195122 (-2.6735695) 0.0000000351 (-0.8924618321198) (-0.4511229079766) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_28 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9989052080702):ℝ):ℂ) + ((0.0467801743309:ℝ):ℂ) * I)‖ ≤ 0.00000012613 := by
  have hl := lg_28
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.170687031321033832 47.170687059633062144 3.0947954 0.00000002612 (-0.9989052080702) 0.0467801743309 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_29 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8558781217788):ℝ):ℂ) + ((0.5171775716162:ℝ):ℂ) * I)‖ ≤ 0.00000012546 := by
  have hl := lg_29
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.667439754569371952 47.66743978288141442 2.5980427 0.00000002545 (-0.8558781217788) 0.5171775716162 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_30 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5204142286821):ℝ):ℂ) + ((0.8539139479936:ℝ):ℂ) * I)‖ ≤ 0.00000013736 := by
  have hl := lg_30
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.147350120090312188 48.1473501484023405 2.1181323 0.00000003735 (-0.5204142286821) 0.8539139479936 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_31 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0830674450143):ℝ):ℂ) + ((0.9965439275709:ℝ):ℂ) * I)‖ ≤ 0.00000012286 := by
  have hl := lg_31
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.611522851972558628 48.611522880284601096 1.6539596 0.00000002285 (-0.0830674450143) 0.9965439275709 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_32 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3581365822608:ℝ):ℂ) + ((0.9336692071856:ℝ):ℂ) * I)‖ ≤ 0.00000013582 := by
  have hl := lg_32
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.060957421634 49.060957457024 1.204525 0.00000003581 0.3581365822608 0.9336692071856 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_33 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7186611033331:ℝ):ℂ) + ((0.6953604953951:ℝ):ℂ) * I)‖ ≤ 0.00000013205 := by
  have hl := lg_33
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.496561025400322732 49.4965610537123652 0.7689214 0.00000003204 0.7186611033331 0.6953604953951 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_34 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9406272288815:ℝ):ℂ) + ((0.339441329668:ℝ):ℂ) * I)‖ ≤ 0.00000014604 := by
  have hl := lg_34
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.919159568067439704 49.91915960345745386 0.3463229 0.00000004603 0.9406272288815 0.339441329668 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_35 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9979511189297:ℝ):ℂ) + (((-0.0639809676925):ℝ):ℂ) * I)‖ ≤ 0.00000011462 := by
  have hl := lg_35
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.329507143724976436 50.329507172037018904 (-0.0640247) 0.00000001461 0.9979511189297 (-0.0639809676925) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_36 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.894800752985:ℝ):ℂ) + (((-0.4464656901236):ℝ):ℂ) * I)‖ ≤ 0.00000014896 := by
  have hl := lg_36
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.728294078065539168 50.72829410637756748 (-0.4628116) 0.00000004895 0.894800752985 (-0.4464656901236) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_37 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6594785123336:ℝ):ℂ) + (((-0.7517234144087):ℝ):ℂ) * I)‖ ≤ 0.00000012756 := by
  have hl := lg_37
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.116153956672480952 51.11615398498452342 (-0.8506715) 0.00000002755 0.6594785123336 (-0.7517234144087) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_38 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3359457206957:ℝ):ℂ) + (((-0.9418813474882):ℝ):ℂ) * I)‖ ≤ 0.00000013326 := by
  have hl := lg_38
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.493669662367552068 51.493669690679594536 (-1.2281872) 0.00000003325 0.3359457206957 (-0.9418813474882) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_39 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0250972377863):ℝ):ℂ) + (((-0.9996850147198):ℝ):ℂ) * I)‖ ≤ 0.00000011878 := by
  have hl := lg_39
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.861378647892114784 51.861378676204157252 (-1.5958962) 0.00000001877 (-0.0250972377863) (-0.9996850147198) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p156_40 : ‖exp (-((((((14156:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3741673794343):ℝ):ℂ) + (((-0.9273611875448):ℝ):ℂ) * I)‖ ≤ 0.00000012341 := by
  have hl := lg_40
  refine (ecis_approx ((((14156:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.219777534037942604 52.21977756942795676 (-1.9542951) 0.0000000234 (-0.3741673794343) (-0.9273611875448) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_2 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9147803261132):ℝ):ℂ) + ((0.4039516738684:ℝ):ℂ) * I)‖ ≤ 0.00000011147 := by
  have hl := lg_2
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.8406105187191 9.8406105258176 2.7257601 0.00000001146 (-0.9147803261132) 0.4039516738684 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_3 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9938497372693):ℝ):ℂ) + (((-0.1107370727128):ℝ):ℂ) * I)‖ ≤ 0.00000015129 := by
  have hl := lg_3
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.596998658530704308 15.596998665629218505 (-3.030628) 0.00000005128 (-0.9938497372693) (-0.1107370727128) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_4 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6736460955471:ℝ):ℂ) + (((-0.7390540832403):ℝ):ℂ) * I)‖ ≤ 0.00000013011 := by
  have hl := lg_4
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.6812210374382 19.6812210516352 (-0.8316651) 0.0000000301 0.6736460955471 (-0.7390540832403) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_5 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.653920485701):ℝ):ℂ) + ((0.756563281136:ℝ):ℂ) * I)‖ ≤ 0.00000012094 := by
  have hl := lg_5
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.849190035446025173 22.84919004964303937 2.2835512 0.00000002093 (-0.653920485701) 0.756563281136 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_6 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9538865829568:ℝ):ℂ) + (((-0.3001672647957):ℝ):ℂ) * I)‖ ≤ 0.00000015148 := by
  have hl := lg_6
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.437609177249804308 25.437609191446818505 (-0.304868) 0.00000005147 0.9538865829568 (-0.3001672647957) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_7 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7971431927061):ℝ):ℂ) + (((-0.6037903032296):ℝ):ℂ) * I)‖ ≤ 0.00000014998 := by
  have hl := lg_7
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.626086378757386134 27.626086392954414528 (-2.4933452) 0.00000004997 (-0.7971431927061) (-0.6037903032296) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_8 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3176960609403):ℝ):ℂ) + ((0.9481926032516:ℝ):ℂ) * I)‖ ≤ 0.00000014157 := by
  have hl := lg_8
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.5218315561573 29.5218315774528 1.894095 0.00000004156 (-0.3176960609403) 0.9481926032516 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_9 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9754746249497:ℝ):ℂ) + ((0.2201119171675:ℝ):ℂ) * I)‖ ≤ 0.00000011885 := by
  have hl := lg_9
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.193997317061408616 31.19399733125843701 0.2219292 0.00000001884 0.9754746249497 0.2201119171675 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_10 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2925785981953:ℝ):ℂ) + (((-0.9562414778068):ℝ):ℂ) * I)‖ ≤ 0.00000013958 := by
  have hl := lg_10
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.689800554165125173 32.68980057546063937 (-1.273874) 0.00000003957 0.2925785981953 (-0.9562414778068) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_11 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8704896894281):ℝ):ℂ) + (((-0.4921866521057):ℝ):ℂ) * I)‖ ≤ 0.00000015907 := by
  have hl := lg_11
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.042919176847113001 34.042919198142641395 (-2.6269927) 0.00000005906 (-0.8704896894281) (-0.4921866521057) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_12 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.75134361039):ℝ):ℂ) + ((0.6599111903066:ℝ):ℂ) * I)‖ ≤ 0.00000014712 := by
  have hl := lg_12
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.278219695968904308 35.278219717264418505 2.4208921 0.00000004711 (-0.75134361039) 0.6599111903066 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_13 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2823764998835:ℝ):ℂ) + ((0.9593036601168:ℝ):ℂ) * I)‖ ≤ 0.00000012628 := by
  have hl := lg_13
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.4145860168100949 36.414586038105623294 1.2845258 0.00000002627 0.2823764998835 0.9593036601168 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_14 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9731130135347:ℝ):ℂ) + ((0.2303281634744:ℝ):ℂ) * I)‖ ≤ 0.00000014562 := by
  have hl := lg_14
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.466696897476486134 37.466696918772014528 0.2324149 0.00000004561 0.9731130135347 0.2303281634744 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_15 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7336782383352:ℝ):ℂ) + (((-0.6794970512028):ℝ):ℂ) * I)‖ ≤ 0.00000014912 := by
  have hl := lg_15
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.446188693976729481 38.446188715272257875 (-0.7470769) 0.00000004911 0.7336782383352 (-0.6794970512028) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_16 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0924018759083):ℝ):ℂ) + (((-0.9957217951457):ℝ):ℂ) * I)‖ ≤ 0.00000016021 := by
  have hl := lg_16
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.3624420748764 39.3624421032704 (-1.6633302) 0.0000000602 (-0.0924018759083) (-0.9957217951457) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_17 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8152852730702):ℝ):ℂ) + (((-0.5790595163361):ℝ):ℂ) * I)‖ ≤ 0.00000011614 := by
  have hl := lg_17
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.223129830804313498 40.223129859198327695 (-2.524018) 0.00000001613 (-0.8152852730702) (-0.5790595163361) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_18 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9812595728245):ℝ):ℂ) + ((0.1926905560939:ℝ):ℂ) * I)‖ ≤ 0.00000011449 := by
  have hl := lg_18
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.034607835780508616 41.03460785707603701 2.9476893 0.00000001448 (-0.9812595728245) 0.1926905560939 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_19 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5722941182426):ℝ):ℂ) + ((0.8200484389442:ℝ):ℂ) * I)‖ ≤ 0.00000014721 := by
  have hl := lg_19
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.802200176154602791 41.802200197450145382 2.180097 0.0000000472 (-0.5722941182426) 0.8200484389442 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_20 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1186302001685:ℝ):ℂ) + ((0.9929385054513:ℝ):ℂ) * I)‖ ≤ 0.00000015104 := by
  have hl := lg_20
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.530411072884225173 42.53041110127823937 1.4518861 0.00000005103 0.1186302001685 0.9929385054513 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_21 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7253785869072:ℝ):ℂ) + ((0.6883501330403:ℝ):ℂ) * I)‖ ≤ 0.00000011298 := by
  have hl := lg_21
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.223085037288090442 43.223085058583633033 0.7592121 0.00000001297 0.7253785869072 0.6883501330403 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_22 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.99512646406:ℝ):ℂ) + ((0.0986068989847:ℝ):ℂ) * I)‖ ≤ 0.00000015471 := by
  have hl := lg_22
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.883529695566213001 43.883529723960241395 0.0987674 0.0000000547 0.99512646406 0.0986068989847 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_23 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8616348559108:ℝ):ℂ) + (((-0.5075286938484):ℝ):ℂ) * I)‖ ≤ 0.00000014694 := by
  have hl := lg_23
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.514611368784329102 44.514611397178371693 (-0.5323142) 0.00000004693 0.8616348559108 (-0.5075286938484) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_24 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4207421295013:ℝ):ℂ) + (((-0.907180280023):ℝ):ℂ) * I)‖ ≤ 0.00000013558 := by
  have hl := lg_24
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.118830214688004308 45.118830243082018505 (-1.1365331) 0.00000003557 0.4207421295013 (-0.907180280023) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_25 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1447759896525):ℝ):ℂ) + (((-0.9894644575828):ℝ):ℂ) * I)‖ ≤ 0.00000014904 := by
  have hl := lg_25
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.698380070892050346 45.69838009928607874 (-1.7160829) 0.00000004903 (-0.1447759896525) (-0.9894644575828) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_26 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6458247805004):ℝ):ℂ) + (((-0.7634856599015):ℝ):ℂ) * I)‖ ≤ 0.00000011474 := by
  have hl := lg_26
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.2551965355291949 46.255196563923223294 (-2.2728994) 0.00000001473 (-0.6458247805004) (-0.7634856599015) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_27 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9451006504293):ℝ):ℂ) + (((-0.3267793756759):ℝ):ℂ) * I)‖ ≤ 0.00000014665 := by
  have hl := lg_27
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.790995975592112924 46.790995996887655515 (-2.8086988) 0.00000004664 (-0.9451006504293) (-0.3267793756759) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_28 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9832260869536):ℝ):ℂ) + ((0.1823909580749:ℝ):ℂ) * I)‖ ≤ 0.00000014126 := by
  have hl := lg_28
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.307307416195586134 47.307307444589614528 2.958175 0.00000004125 (-0.9832260869536) 0.1823909580749 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_29 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7765599509188):ℝ):ℂ) + ((0.6300433656406:ℝ):ℂ) * I)‖ ≤ 0.00000015453 := by
  have hl := lg_29
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.805498883556186324 47.805498911950228915 2.4599836 0.00000005452 (-0.7765599509188) 0.6300433656406 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_30 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3966704468862):ℝ):ℂ) + ((0.9179610866283:ℝ):ℂ) * I)‖ ≤ 0.00000014476 := by
  have hl := lg_30
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.286799212695829481 48.286799241089857875 1.9786832 0.00000004475 (-0.3966704468862) 0.9179610866283 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_31 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.057598331427:ℝ):ℂ) + ((0.9983398380395:ℝ):ℂ) * I)‖ ≤ 0.00000013014 := by
  have hl := lg_31
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.752316327313818511 48.752316355707861102 1.5131661 0.00000003013 0.057598331427 0.9983398380395 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_32 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4867509914631:ℝ):ℂ) + ((0.8735407673999:ℝ):ℂ) * I)‖ ≤ 0.00000016386 := by
  have hl := lg_32
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.2030525935955 49.203052629088 1.0624298 0.00000006385 0.4867509914631 0.8735407673999 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_33 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8106326443458:ℝ):ℂ) + ((0.5855550494368:ℝ):ℂ) * I)‖ ≤ 0.00000012207 := by
  have hl := lg_33
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.639917835377817309 49.6399178637718599 0.6255646 0.00000002206 0.8106326443458 0.5855550494368 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_34 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9797189889674:ℝ):ℂ) + ((0.2003764024448:ℝ):ℂ) * I)‖ ≤ 0.00000012759 := by
  have hl := lg_34
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.063740349523413498 50.063740385015927695 0.2017421 0.00000002758 0.9797189889674 0.2003764024448 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_35 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9780738367114:ℝ):ℂ) + (((-0.208258421056):ℝ):ℂ) * I)‖ ≤ 0.00000014325 := by
  have hl := lg_35
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.475276414203411307 50.475276442597453898 (-0.209794) 0.00000004324 0.9780738367114 (-0.208258421056) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_36 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8197992835552:ℝ):ℂ) + (((-0.5726509710831):ℝ):ℂ) * I)‖ ≤ 0.00000012547 := by
  have hl := lg_36
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.875218354499608616 50.87521838289363701 (-0.6097359) 0.00000002546 0.8197992835552 (-0.5726509710831) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_37 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5413797025196:ℝ):ℂ) + (((-0.8407782214709):ℝ):ℂ) * I)‖ ≤ 0.00000016202 := by
  have hl := lg_37
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.264201591048263074 51.264201619442305665 (-0.9987191) 0.00000006201 0.5413797025196 (-0.8407782214709) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_38 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1922633694283:ℝ):ℂ) + (((-0.9813433633423):ℝ):ℂ) * I)‖ ≤ 0.00000016258 := by
  have hl := lg_38
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.642810694873702791 51.642810723267745382 (-1.3773283) 0.00000006257 0.1922633694283 (-0.9813433633423) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_39 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.174409330907):ℝ):ℂ) + (((-0.9846732378266):ℝ):ℂ) * I)‖ ≤ 0.00000014631 := by
  have hl := lg_39
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.011584675340799208 52.011584703734841799 (-1.7461022) 0.0000000463 (-0.174409330907) (-0.9846732378266) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p197_40 : ‖exp (-((((((14197:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5096198244617):ℝ):ℂ) + (((-0.8603996946239):ℝ):ℂ) * I)‖ ≤ 0.00000016585 := by
  have hl := lg_40
  refine (ecis_approx ((((14197:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.371021591603325173 52.37102162709583937 (-2.1055392) 0.00000006584 (-0.5096198244617) (-0.8603996946239) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_2 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9029325871771):ℝ):ℂ) + ((0.4297822040218:ℝ):ℂ) * I)‖ ≤ 0.00000014589 := by
  have hl := lg_2
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.8690295531114 9.8690295602304 2.6973411 0.00000004588 (-0.9029325871771) 0.4297822040218 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_3 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9978279674672):ℝ):ℂ) + (((-0.065873718584):ℝ):ℂ) * I)‖ ≤ 0.00000015202 := by
  have hl := lg_3
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.642041762355439032 15.64204176947445327 (-3.0756712) 0.00000005201 (-0.9978279674672) (-0.065873718584) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_4 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6305744420606:ℝ):ℂ) + (((-0.7761287734776):ℝ):ℂ) * I)‖ ≤ 0.00000011533 := by
  have hl := lg_4
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.7380591062228 19.7380591204608 (-0.8885032) 0.00000001532 0.6305744420606 (-0.7761287734776) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_5 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6026102053582):ℝ):ℂ) + ((0.7980356761361:ℝ):ℂ) * I)‖ ≤ 0.0000001389 := by
  have hl := lg_5
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.915176989834507742 22.91517700407252198 2.2175642 0.00000003889 (-0.6026102053582) 0.7980356761361 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_6 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9292827405595:ℝ):ℂ) + (((-0.3693691758908):ℝ):ℂ) * I)‖ ≤ 0.00000011327 := by
  have hl := lg_6
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.511071315466839032 25.51107132970485327 (-0.3783301) 0.00000001326 0.9292827405595 (-0.3693691758908) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_7 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8427282354779):ℝ):ℂ) + (((-0.5383392248935):ℝ):ℂ) * I)‖ ≤ 0.00000013389 := by
  have hl := lg_7
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.705868694847338436 27.705868709085366912 (-2.5731275) 0.00000003388 (-0.8427282354779) (-0.5383392248935) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_8 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.23579987748):ℝ):ℂ) + ((0.9718016349952:ℝ):ℂ) * I)‖ ≤ 0.00000014481 := by
  have hl := lg_8
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.6070886593342 29.6070886806912 1.8088379 0.0000000448 (-0.23579987748) 0.9718016349952 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_9 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9913212941318:ℝ):ℂ) + ((0.1314613699945:ℝ):ℂ) * I)‖ ≤ 0.0000001112 := by
  have hl := lg_9
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.284083524710878064 31.28408353894890654 0.131843 0.00000001119 0.9913212941318 0.1314613699945 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_10 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2011348670062:ℝ):ℂ) + (((-0.979563558568):ℝ):ℂ) * I)‖ ≤ 0.00000012842 := by
  have hl := lg_10
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.784206542945907742 32.78420656430292198 (-1.36828) 0.00000002841 0.2011348670062 (-0.979563558568) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_11 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9145969590942):ℝ):ℂ) + (((-0.4043666681128):ℝ):ℂ) * I)‖ ≤ 0.00000015291 := by
  have hl := lg_11
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.141232882999872854 34.14123290435690133 (-2.7253064) 0.0000000529 (-0.9145969590942) (-0.4043666681128) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_12 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.680331370647):ℝ):ℂ) + ((0.7329046500691:ℝ):ℂ) * I)‖ ≤ 0.00000014687 := by
  have hl := lg_12
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.380100868578239032 35.38010088993525327 2.319011 0.00000004686 (-0.680331370647) 0.7329046500691 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_13 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3815138135095:ℝ):ℂ) + ((0.9243631375717:ℝ):ℂ) * I)‖ ≤ 0.00000011873 := by
  have hl := lg_13
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.5197489404340446 36.519748961791073076 1.1793629 0.00000001872 0.3815138135095 0.9243631375717 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_14 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9922954046297:ℝ):ℂ) + ((0.1238944306692:ℝ):ℂ) * I)‖ ≤ 0.00000012625 := by
  have hl := lg_14
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.574898247958738436 37.574898269315766912 0.1242136 0.00000002624 0.9922954046297 0.1238944306692 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_15 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6538709699516:ℝ):ℂ) + (((-0.7566060762739):ℝ):ℂ) * I)‖ ≤ 0.00000013048 := by
  have hl := lg_15
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.557218752189946774 38.55721877354697525 (-0.8581069) 0.00000003047 0.6538709699516 (-0.7566060762739) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_16 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2047517460399):ℝ):ℂ) + (((-0.9788139366053):ℝ):ℂ) * I)‖ ≤ 0.00000013065 := by
  have hl := lg_16
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.4761182124456 39.4761182409216 (-1.7770064) 0.00000003064 (-0.2047517460399) (-0.9788139366053) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_17 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8769042800353):ℝ):ℂ) + (((-0.4806650430001):ℝ):ℂ) * I)‖ ≤ 0.00000016328 := by
  have hl := lg_17
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.339291577867987292 40.33929160634400153 (-2.6401797) 0.00000006327 (-0.8769042800353) (-0.4806650430001) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_18 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9515960581435):ℝ):ℂ) + ((0.3073514957146:ℝ):ℂ) * I)‖ ≤ 0.00000014894 := by
  have hl := lg_18
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.153113077822278064 41.15311309917930654 2.8291841 0.00000004893 (-0.9515960581435) 0.3073514957146 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_19 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4693713298874):ℝ):ℂ) + ((0.8830008803363:ℝ):ℂ) * I)‖ ≤ 0.00000014538 := by
  have hl := lg_19
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.922922174268453514 41.922922195625496228 2.059375 0.00000004537 (-0.4693713298874) 0.8830008803363 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_20 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2393878564919:ℝ):ℂ) + ((0.9709240207988:ℝ):ℂ) * I)‖ ≤ 0.00000015421 := by
  have hl := lg_20
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.653236096057307742 42.65323612453332198 1.329061 0.0000000542 0.2393878564919 0.9709240207988 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_21 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8054353408116:ℝ):ℂ) + ((0.5926836523573:ℝ):ℂ) * I)‖ ≤ 0.00000012832 := by
  have hl := lg_21
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.347910457202777468 43.347910478559820182 0.6343867 0.00000002831 0.8054353408116 0.5926836523573 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_22 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9996089964812:ℝ):ℂ) + (((-0.0279616550614):ℝ):ℂ) * I)‖ ≤ 0.00000011435 := by
  have hl := lg_22
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.010262436111272854 44.01026246458730133 (-0.0279653) 0.00000001434 0.9996089964812 (-0.0279616550614) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_23 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7894588278328:ℝ):ℂ) + (((-0.6138035183647):ℝ):ℂ) * I)‖ ≤ 0.00000011868 := by
  have hl := lg_23
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.643166631594793108 44.643166660070835822 (-0.6608695) 0.00000001867 0.7894588278328 (-0.6138035183647) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_24 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2993039002003:ℝ):ℂ) + (((-0.9541578356461):ℝ):ℂ) * I)‖ ≤ 0.00000012858 := by
  have hl := lg_24
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.249130421689639032 45.24913045016565327 (-1.2668333) 0.00000002857 0.2993039002003 (-0.9541578356461) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_25 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2737217777079):ℝ):ℂ) + (((-0.9618089147055):ℝ):ℂ) * I)‖ ≤ 0.0000001579 := by
  have hl := lg_25
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.830353979669015484 45.83035400814504396 (-1.8480568) 0.00000005789 (-0.2737217777079) (-0.9618089147055) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_26 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.741756143578):ℝ):ℂ) + (((-0.670669682804):ℝ):ℂ) * I)‖ ≤ 0.00000015673 := by
  have hl := lg_26
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.3887784935454446 46.388778522021473076 (-2.4064814) 0.00000005672 (-0.741756143578) (-0.670669682804) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_27 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9805082431756):ℝ):ℂ) + (((-0.1964779497477):ℝ):ℂ) * I)‖ ≤ 0.00000015818 := by
  have hl := lg_27
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.926125287066317096 46.92612530842335981 (-2.9438281) 0.00000005817 (-0.9805082431756) (-0.1964779497477) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_28 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9492234469369):ℝ):ℂ) + ((0.3146026820991:ℝ):ℂ) * I)‖ ≤ 0.00000015638 := by
  have hl := lg_28
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.443927801070138436 47.443927829546166912 2.8215546 0.00000005637 (-0.9492234469369) 0.3146026820991 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_29 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6824637247437):ℝ):ℂ) + ((0.7309194650493:ℝ):ℂ) * I)‖ ≤ 0.00000014491 := by
  have hl := lg_29
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.943558012543000696 47.94355804101904341 2.3219244 0.0000000449 (-0.6824637247437) 0.7309194650493 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_30 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.265225483097):ℝ):ℂ) + ((0.9641864151266:ℝ):ℂ) * I)‖ ≤ 0.00000015215 := by
  have hl := lg_30
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.426248305301346774 48.42624833377737525 1.8392341 0.00000005214 (-0.265225483097) 0.9641864151266 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_31 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1971242319384:ℝ):ℂ) + ((0.9803785172997:ℝ):ℂ) * I)‖ ≤ 0.0000001548 := by
  have hl := lg_31
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.893109802655078394 48.893109831131121108 1.3723726 0.00000005479 0.1971242319384 0.9803785172997 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_32 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.605553834853:ℝ):ℂ) + ((0.7958043434757:ℝ):ℂ) * I)‖ ≤ 0.00000014373 := by
  have hl := lg_32
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.345147765557 49.345147801152 0.9203347 0.00000004372 0.605553834853 0.7958043434757 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_33 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8859732457691:ℝ):ℂ) + ((0.4637363558977:ℝ):ℂ) * I)‖ ≤ 0.00000011641 := by
  have hl := lg_33
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.783274645355311886 49.7832746738313546 0.4822078 0.0000000164 0.8859732457691 0.4637363558977 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_34 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9983667376759:ℝ):ℂ) + ((0.057130176811:ℝ):ℂ) * I)‖ ≤ 0.00000012647 := by
  have hl := lg_34
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.208321130979387292 50.20832116657440153 0.0571613 0.00000002646 0.9983667376759 0.057130176811 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_35 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.937450577228:ℝ):ℂ) + (((-0.3481183925835):ℝ):ℂ) * I)‖ ≤ 0.00000015574 := by
  have hl := lg_35
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.621045684681846178 50.621045713157888892 (-0.3555632) 0.00000005573 0.937450577228 (-0.3481183925835) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_36 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7271328238035:ℝ):ℂ) + (((-0.6864968001):ℝ):ℂ) * I)‖ ≤ 0.00000012652 := by
  have hl := lg_36
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.022142630933678064 51.02214265940970654 (-0.7566602) 0.00000002651 0.7271328238035 (-0.6864968001) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_37 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4114364490375:ℝ):ℂ) + (((-0.9114384501454):ℝ):ℂ) * I)‖ ≤ 0.00000013203 := by
  have hl := lg_37
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.412249225424045196 51.41224925390008791 (-1.1467668) 0.00000003202 0.4114364490375 (-0.9114384501454) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_38 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.044312511967:ℝ):ℂ) + (((-0.9990177182027):ℝ):ℂ) * I)‖ ≤ 0.00000013007 := by
  have hl := lg_38
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.791951727379853514 51.791951755855896228 (-1.5264693) 0.00000003006 0.044312511967 (-0.9990177182027) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_39 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3197939157676):ℝ):ℂ) + (((-0.9474871246809):ℝ):ℂ) * I)‖ ≤ 0.00000015466 := by
  have hl := lg_39
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.161790702789483632 52.161790731265526346 (-1.8963083) 0.00000005465 (-0.3197939157676) (-0.9474871246809) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p238_40 : ‖exp (-((((((14238:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.633436956712):ℝ):ℂ) + (((-0.7737943020315):ℝ):ℂ) * I)‖ ≤ 0.00000012734 := by
  have hl := lg_40
  refine (ecis_approx ((((14238:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.522265649168707742 52.52226568476372198 (-2.2567832) 0.00000002733 (-0.633436956712) (-0.7737943020315) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_2 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8903556077144):ℝ):ℂ) + ((0.4552657374605:ℝ):ℂ) * I)‖ ≤ 0.00000012687 := by
  have hl := lg_2
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.8974485875037 9.8974485946432 2.668922 0.00000002686 (-0.8903556077144) 0.4552657374605 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_3 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.99978205478):ℝ):ℂ) + (((-0.0208768365046):ℝ):ℂ) * I)‖ ≤ 0.00000014819 := by
  have hl := lg_3
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.687084866180173756 15.687084873319688035 (-3.1207143) 0.00000004818 (-0.99978205478) (-0.0208768365046) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_4 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5854662223048:ℝ):ℂ) + (((-0.8106968006229):ℝ):ℂ) * I)‖ ≤ 0.00000014655 := by
  have hl := lg_4
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.7948971750074 19.7948971892864 (-0.9453413) 0.00000004654 0.5854662223048 (-0.8106968006229) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_5 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5486770245166):ℝ):ℂ) + ((0.8360344028561:ℝ):ℂ) * I)‖ ≤ 0.0000001298 := by
  have hl := lg_5
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.981163944222990311 22.98116395850200459 2.1515773 0.00000002979 (-0.5486770245166) 0.8360344028561 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_6 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8996661114307:ℝ):ℂ) + (((-0.4365786159939):ℝ):ℂ) * I)‖ ≤ 0.00000013926 := by
  have hl := lg_6
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.584533453683873756 25.584533467962888035 (-0.4517922) 0.00000003925 0.8996661114307 (-0.4365786159939) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_7 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8829519762343):ℝ):ℂ) + (((-0.4694633186576):ℝ):ℂ) * I)‖ ≤ 0.0000001178 := by
  have hl := lg_7
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.785651010937290738 27.785651025216319296 (-2.6529098) 0.00000001779 (-0.8829519762343) (-0.4694633186576) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_8 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1521907561702):ℝ):ℂ) + ((0.9883511388852:ℝ):ℂ) * I)‖ ≤ 0.00000014805 := by
  have hl := lg_8
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.6923457625111 29.6923457839296 1.7235808 0.00000004804 (-0.1521907561702) 0.9883511388852 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_9 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9991283114965:ℝ):ℂ) + ((0.0417446663206:ℝ):ℂ) * I)‖ ≤ 0.00000011076 := by
  have hl := lg_9
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.374169732360347512 31.37416974663937607 0.0417568 0.00000001075 0.9991283114965 0.0417446663206 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_10 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1078998537479:ℝ):ℂ) + (((-0.9941617683059):ℝ):ℂ) * I)‖ ≤ 0.00000011726 := by
  have hl := lg_10
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.878612531726690311 32.87861255314520459 (-1.462686) 0.00000001725 0.1078998537479 (-0.9941617683059) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_11 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9498712334835):ℝ):ℂ) + (((-0.3126413913696):ℝ):ℂ) * I)‖ ≤ 0.00000014676 := by
  have hl := lg_11
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.239546589152632707 34.239546610571161265 (-2.8236201) 0.00000004675 (-0.9498712334835) (-0.3126413913696) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_12 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6022634818141):ℝ):ℂ) + ((0.798297374705:ℝ):ℂ) * I)‖ ≤ 0.00000011954 := by
  have hl := lg_12
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.481982041187573756 35.481982062606088035 2.2171298 0.00000001953 (-0.6022634818141) 0.798297374705 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_13 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4764357630528:ℝ):ℂ) + ((0.879209283211:ℝ):ℂ) * I)‖ ≤ 0.00000014241 := by
  have hl := lg_13
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.6249118640579943 36.624911885476522858 1.0742 0.0000000424 0.4764357630528 0.879209283211 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_14 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9998718074646:ℝ):ℂ) + ((0.0160115157793:ℝ):ℂ) * I)‖ ≤ 0.00000014465 := by
  have hl := lg_14
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.683099598440990738 37.683099619859519296 0.0160122 0.00000004464 0.9998718074646 0.0160115157793 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_15 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5660111969338:ℝ):ℂ) + (((-0.824397552729):ℝ):ℂ) * I)‖ ≤ 0.00000013269 := by
  have hl := lg_15
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.668248810403164067 38.668248831821692625 (-0.969137) 0.00000003268 0.5660111969338 (-0.824397552729) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_16 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3144585101534):ℝ):ℂ) + (((-0.9492712180353):ℝ):ℂ) * I)‖ ≤ 0.00000013551 := by
  have hl := lg_16
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.5897943500148 39.5897943785728 (-1.8906825) 0.0000000355 (-0.3144585101534) (-0.9492712180353) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_17 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9267040803685):ℝ):ℂ) + (((-0.3757918935721):ℝ):ℂ) * I)‖ ≤ 0.00000011816 := by
  have hl := lg_17
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.455453324931661086 40.455453353489675365 (-2.7563415) 0.00000001815 (-0.9267040803685) (-0.3757918935721) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
