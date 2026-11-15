/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 9

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

lemma cs_b1left_v21p459_35 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6247457906602:ℝ):ℂ) + (((-0.7808282122544):ℝ):ℂ) * I)‖ ≤ 0.00000015698 := by
  have hl := lg_35
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.294214029188631629 76.294214072106696006 (-0.8959904) 0.00000005697 0.6247457906602 (-0.7808282122544) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_36 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0702292680719:ℝ):ℂ) + (((-0.997530876668):ℝ):ℂ) * I)‖ ≤ 0.00000013479 := by
  have hl := lg_36
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.898732878016982552 76.89873292093502547 (-1.5005092) 0.00000003478 0.0702292680719 (-0.997530876668) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_37 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4948545765068):ℝ):ℂ) + (((-0.868975804096):ℝ):ℂ) * I)‖ ≤ 0.0000001219 := by
  have hl := lg_37
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.486687465119720878 77.486687508037785255 (-2.0884638) 0.00000002189 (-0.4948545765068) (-0.868975804096) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_38 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8865997988624):ℝ):ℂ) + (((-0.4625373461191):ℝ):ℂ) * I)‖ ≤ 0.00000013603 := by
  have hl := lg_38
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.058961379255813777 78.058961422173878154 (-2.6607377) 0.00000003602 (-0.8865997988624) (-0.4625373461191) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_39 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9970712454689):ℝ):ℂ) + ((0.0764783037183:ℝ):ℂ) * I)‖ ≤ 0.00000015137 := by
  have hl := lg_39
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.616369341983391576 78.616369384901455953 3.0650396 0.00000005136 (-0.9970712454689) 0.0764783037183 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_40 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8139668496442):ℝ):ℂ) + ((0.5809113250965:ℝ):ℂ) * I)‖ ≤ 0.00000013827 := by
  have hl := lg_40
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.159664177940110931 79.15966423158763239 2.5217448 0.00000003826 (-0.8139668496442) 0.5809113250965 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_2 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7092059590009):ℝ):ℂ) + (((-0.705001352972):ℝ):ℂ) * I)‖ ≤ 0.00000012982 := by
  have hl := lg_2
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.9255382333999 14.9255382441664 (-2.3591676) 0.00000002981 (-0.7092059590009) (-0.705001352972) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_3 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0943330562318:ℝ):ℂ) + ((0.9955406945484:ℝ):ℂ) * I)‖ ≤ 0.00000012244 := by
  have hl := lg_3
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.656418406292995412 23.656418417059516945 1.4763228 0.00000002243 0.0943330562318 0.9955406945484 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_4 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0059461917542:ℝ):ℂ) + ((0.9999823212454:ℝ):ℂ) * I)‖ ≤ 0.00000015245 := by
  have hl := lg_4
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.8510764667998 29.8510764883328 1.5648501 0.00000005244 0.0059461917542 0.9999823212454 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_5 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9951520725644):ℝ):ℂ) + ((0.0983481163638:ℝ):ℂ) * I)‖ ≤ 0.00000013572 := by
  have hl := lg_5
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.656026557248662397 34.65602657878168393 3.0430853 0.00000003571 (-0.9951520725644) 0.0983481163638 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_6 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6349559709989:ℝ):ℂ) + (((-0.7725483252799):ℝ):ℂ) * I)‖ ≤ 0.00000011816 := by
  have hl := lg_6
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.581956639692895412 38.581956661225916945 (-0.8828448) 0.00000001815 0.6349559709989 (-0.7725483252799) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_7 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4883671211464):ℝ):ℂ) + ((0.872638272698:ℝ):ℂ) * I)‖ ≤ 0.00000012186 := by
  have hl := lg_7
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.901283228413241926 41.901283249946284992 2.0810139 0.00000002185 (-0.4883671211464) 0.872638272698 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_8 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7007717434765:ℝ):ℂ) + (((-0.7133855644354):ℝ):ℂ) * I)‖ ≤ 0.00000015007 := by
  have hl := lg_8
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.7766147001997 44.7766147324992 (-0.7943176) 0.00000005006 0.7007717434765 (-0.7133855644354) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_9 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9822025488633):ℝ):ℂ) + ((0.187824792473:ℝ):ℂ) * I)‖ ≤ 0.00000014487 := by
  have hl := lg_9
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.312836812585990824 47.31283683411903389 2.9526456 0.00000004486 (-0.9822025488633) 0.187824792473 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_10 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7751033353918:ℝ):ℂ) + ((0.6318344873973:ℝ):ℂ) * I)‖ ≤ 0.00000016553 := by
  have hl := lg_10
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.581564790648562397 49.58156482294808393 0.6839177 0.00000006552 0.7751033353918 0.6318344873973 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_11 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2010207464869:ℝ):ℂ) + (((-0.9795869841325):ℝ):ℂ) * I)‖ ≤ 0.00000016508 := by
  have hl := lg_11
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.633878892375071089 51.633878924674614155 (-1.3683965) 0.00000006507 0.2010207464869 (-0.9795869841325) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_12 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9949621719716):ℝ):ℂ) + ((0.1002510641862:ℝ):ℂ) * I)‖ ≤ 0.00000014079 := by
  have hl := lg_12
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.507494873092795412 53.507494905392316945 3.0411729 0.00000004078 (-0.9949621719716) 0.1002510641862 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_13 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2504867749416:ℝ):ℂ) + ((0.9681200212677:ℝ):ℂ) * I)‖ ≤ 0.00000016513 := by
  have hl := lg_13
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.2310544974270461 55.231054529726589166 1.3176133 0.00000006512 0.2504867749416 0.9681200212677 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_14 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.961564035421:ℝ):ℂ) + (((-0.2745807818928):ℝ):ℂ) * I)‖ ≤ 0.00000012951 := by
  have hl := lg_14
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.826821461813141926 56.826821494112684992 (-0.2781537) 0.0000000295 0.961564035421 (-0.2745807818928) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_15 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1917852816912):ℝ):ℂ) + (((-0.9814369086833):ℝ):ℂ) * I)‖ ≤ 0.00000013124 := by
  have hl := lg_15
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.312444963541657809 58.312444995841200875 (-1.7637772) 0.00000003123 (-0.1917852816912) (-0.9814369086833) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_16 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999292840922):ℝ):ℂ) + ((0.0118922729648:ℝ):ℂ) * I)‖ ≤ 0.00000013821 := by
  have hl := lg_16
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.7021529335996 59.7021529766656 3.1297001 0.0000000382 (-0.9999292840922) 0.0118922729648 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_17 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2507682417714):ℝ):ℂ) + ((0.9680471522181:ℝ):ℂ) * I)‖ ≤ 0.00000015664 := by
  have hl := lg_17
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.007582915172873322 61.007582958238894855 1.8242701 0.00000005663 (-0.2507682417714) 0.9680471522181 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_18 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8290006336384:ℝ):ℂ) + ((0.5592476637655:ℝ):ℂ) * I)‖ ≤ 0.00000012582 := by
  have hl := lg_18
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.238375045985890824 62.23837507828543389 0.593478 0.00000002581 0.8290006336384 0.5592476637655 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_19 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8414952039831:ℝ):ℂ) + (((-0.5402645848781):ℝ):ℂ) * I)‖ ≤ 0.00000015021 := by
  have hl := lg_19
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.402604521598722399 63.402604553898286998 (-0.5707515) 0.0000000502 0.8414952039831 (-0.5402645848781) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_20 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1042638352806):ℝ):ℂ) + (((-0.9945496732955):ℝ):ℂ) * I)‖ ≤ 0.00000014776 := by
  have hl := lg_20
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.507103024048462397 64.50710306711448393 (-1.67525) 0.00000004775 (-0.1042638352806) (-0.9945496732955) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_21 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9148160722538):ℝ):ℂ) + (((-0.4038707142277):ℝ):ℂ) * I)‖ ≤ 0.0000001371 := by
  have hl := lg_21
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.557701634706237338 65.557701667005801937 (-2.7258486) 0.00000003709 (-0.9148160722538) (-0.4038707142277) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_22 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8331752564881):ℝ):ℂ) + ((0.5530090342046:ℝ):ℂ) * I)‖ ≤ 0.00000015322 := by
  have hl := lg_22
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.559417125774971089 66.559417168841014155 2.5556212 0.00000005321 (-0.8331752564881) 0.5530090342046 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_23 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0276415520482):ℝ):ℂ) + ((0.9996178992996:ℝ):ℂ) * I)‖ ≤ 0.00000014978 := by
  have hl := lg_23
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.516596929212718078 67.516596972278782677 1.5984414 0.00000004977 (-0.0276415520482) 0.9996178992996 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_24 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7763102375468:ℝ):ℂ) + ((0.6303510252867:ℝ):ℂ) * I)‖ ≤ 0.0000001706 := by
  have hl := lg_24
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.433033106492695412 68.433033149558716945 0.6820053 0.00000007059 0.7763102375468 0.6303510252867 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_25 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9806552777579:ℝ):ℂ) + (((-0.1957427551801):ℝ):ℂ) * I)‖ ≤ 0.00000016449 := by
  have hl := lg_25
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.312053114497324794 69.31205315756336786 (-0.1970148) 0.00000006448 0.9806552777579 (-0.1957427551801) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_26 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5048791250875:ℝ):ℂ) + (((-0.8631900538415):ℝ):ℂ) * I)‖ ≤ 0.00000014816 := by
  have hl := lg_26
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.1565927308269461 70.156592773892989166 (-1.0415544) 0.00000004815 0.5048791250875 (-0.8631900538415) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_27 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2796413859113):ℝ):ℂ) + (((-0.9601045231037):ℝ):ℂ) * I)‖ ≤ 0.00000016011 := by
  have hl := lg_27
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.969255218878986236 70.969255251178550835 (-1.8542169) 0.0000000601 (-0.2796413859113) (-0.9601045231037) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_28 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8755267665985):ℝ):ℂ) + (((-0.4831696191579):ℝ):ℂ) * I)‖ ≤ 0.00000015932 := by
  have hl := lg_28
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.752359695213041926 71.752359738279084992 (-2.6373213) 0.00000005931 (-0.8755267665985) (-0.4831696191579) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_29 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9685775301148):ℝ):ℂ) + ((0.2487118169514:ℝ):ℂ) * I)‖ ≤ 0.00000014164 := by
  have hl := lg_29
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.507981084709118836 72.507981127775183435 2.8902426 0.00000004163 (-0.9685775301148) 0.2487118169514 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p533_30 : ‖exp (-((((((21533:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5558990778996):ℝ):ℂ) + ((0.8312497910865:ℝ):ℂ) * I)‖ ≤ 0.00000015387 := by
  have hl := lg_30
  refine (ecis_approx ((((21533:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.237983196941557809 73.237983240007600875 2.1602405 0.00000005386 (-0.5558990778996) 0.8312497910865 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_2 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7444189260779):ℝ):ℂ) + (((-0.6677128592925):ℝ):ℂ) * I)‖ ≤ 0.0000001212 := by
  have hl := lg_2
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.9768311247421 14.9768311355456 (-2.4104605) 0.00000002119 (-0.7444189260779) (-0.6677128592925) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_3 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.174867139395:ℝ):ℂ) + ((0.9845920391511:ℝ):ℂ) * I)‖ ≤ 0.0000001131 := by
  have hl := lg_3
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.737715715635199548 23.737715726438721155 1.3950255 0.00000001309 0.174867139395 0.9845920391511 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_4 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1083190821593:ℝ):ℂ) + ((0.9941161785426:ℝ):ℂ) * I)‖ ≤ 0.00000013521 := by
  have hl := lg_4
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.9536622494842 29.9536622710912 1.4622643 0.0000000352 0.1083190821593 0.9941161785426 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_5 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9764171470776):ℝ):ℂ) + ((0.2158924607061:ℝ):ℂ) * I)‖ ≤ 0.00000014127 := by
  have hl := lg_5
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.775124962730313863 34.77512498433733547 2.9239869 0.00000004126 (-0.9764171470776) 0.2158924607061 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_6 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5272503576006:ℝ):ℂ) + (((-0.84970998606):ℝ):ℂ) * I)‖ ≤ 0.00000011892 := by
  have hl := lg_6
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.714546840377299548 38.714546861984321155 (-1.015435) 0.00000001891 0.5272503576006 (-0.84970998606) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_7 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3580889146295):ℝ):ℂ) + ((0.9336874901256:ℝ):ℂ) * I)‖ ≤ 0.00000015077 := by
  have hl := lg_7
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.045280579404863154 42.045280601011906368 1.9370166 0.00000005076 (-0.3580889146295) 0.9336874901256 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_8 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5831493812465:ℝ):ℂ) + (((-0.8123649420992):ℝ):ℂ) * I)‖ ≤ 0.00000015639 := by
  have hl := lg_8
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.9304933742263 44.9304934066368 (-0.9481962) 0.00000005638 0.5831493812465 (-0.8123649420992) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_9 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9388429670594):ℝ):ℂ) + ((0.3443455866221:ℝ):ℂ) * I)‖ ≤ 0.00000012618 := by
  have hl := lg_9
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.475431431270399096 47.47543145287744231 2.790051 0.00000002617 (-0.9388429670594) 0.3443455866221 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_10 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8710175764701:ℝ):ℂ) + ((0.4912518513758:ℝ):ℂ) * I)‖ ≤ 0.00000016246 := by
  have hl := lg_10
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.751956087472413863 49.75195611988293547 0.5135264 0.00000006245 0.8710175764701 0.4912518513758 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_11 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0249530365509:ℝ):ℂ) + (((-0.999688624506):ℝ):ℂ) * I)‖ ≤ 0.00000011749 := by
  have hl := lg_11
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.811323142504442531 51.811323174914985745 (-1.5458407) 0.00000001748 0.0249530365509 (-0.999688624506) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_12 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.959857427259):ℝ):ℂ) + ((0.280488358231:ℝ):ℂ) * I)‖ ≤ 0.00000013293 := by
  have hl := lg_12
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.691377965119399548 53.691377997529921155 2.8572898 0.00000003292 (-0.959857427259) 0.280488358231 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_13 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4286421563155:ℝ):ℂ) + ((0.9034743503992:ℝ):ℂ) * I)‖ ≤ 0.00000011763 := by
  have hl := lg_13
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.4208607498214919 55.420860782232035114 1.127807 0.00000001762 0.4286421563155 0.9034743503992 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_14 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8900032634107:ℝ):ℂ) + (((-0.4559541546233):ℝ):ℂ) * I)‖ ≤ 0.00000016048 := by
  have hl := lg_14
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.022111704146963154 57.022111736557506368 (-0.473444) 0.00000006047 0.8900032634107 (-0.4559541546233) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_15 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3833092650287):ℝ):ℂ) + (((-0.9236200557265):ℝ):ℂ) * I)‖ ≤ 0.00000014617 := by
  have hl := lg_15
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.512840678365513411 58.512840710776056625 (-1.9641729) 0.00000004616 (-0.3833092650287) (-0.9236200557265) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_16 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9765339527582):ℝ):ℂ) + ((0.2153635038874:ℝ):ℂ) * I)‖ ≤ 0.0000001704 := by
  have hl := lg_16
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.9073244989684 59.9073245421824 2.9245286 0.00000007039 (-0.9765339527582) 0.2153635038874 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_17 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0438019546115):ℝ):ℂ) + ((0.9990402338104:ℝ):ℂ) * I)‖ ≤ 0.00000016925 := by
  have hl := lg_17
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.217240702556089438 61.217240745770111045 1.6146123 0.00000006924 (-0.0438019546115) 0.9990402338104 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_18 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9288164496405:ℝ):ℂ) + ((0.3705401501555:ℝ):ℂ) * I)‖ ≤ 0.00000011664 := by
  have hl := lg_18
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.452262556012499096 62.45226258842304231 0.3795905 0.00000001663 0.9288164496405 0.3705401501555 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_19 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7048107448889:ℝ):ℂ) + (((-0.7093953861488):ℝ):ℂ) * I)‖ ≤ 0.00000016581 := by
  have hl := lg_19
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.620493005999331021 63.620493038409895842 (-0.78864) 0.0000000658 0.7048107448889 (-0.7093953861488) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_20 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3203868852804):ℝ):ℂ) + (((-0.9472867800927):ℝ):ℂ) * I)‖ ≤ 0.0000001596 := by
  have hl := lg_20
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.728787212214513863 64.72878725542853547 (-1.8969342) 0.00000005959 (-0.3203868852804) (-0.9472867800927) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_21 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9819192524856):ℝ):ℂ) + (((-0.1893002410487):ℝ):ℂ) * I)‖ ≤ 0.00000015567 := by
  have hl := lg_21
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.782996295040062702 65.782996327450627523 (-2.9511432) 0.00000005566 (-0.9819192524856) (-0.1893002410487) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_22 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6860804573352):ℝ):ℂ) + ((0.7275256738021:ℝ):ℂ) * I)‖ ≤ 0.0000001315 := by
  have hl := lg_22
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.788154267246542531 66.788154310460585745 2.3268841 0.00000003149 (-0.6860804573352) 0.7275256738021 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_23 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2029615001065:ℝ):ℂ) + ((0.9791867183916:ℝ):ℂ) * I)‖ ≤ 0.00000016537 := by
  have hl := lg_23
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.748623501114531162 67.748623544328595983 1.3664149 0.00000006536 0.2029615001065 0.9791867183916 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_24 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9018217190149:ℝ):ℂ) + ((0.4321083048416:ℝ):ℂ) * I)‖ ≤ 0.00000015412 := by
  have hl := lg_24
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.668209089861499548 68.668209133075521155 0.4468293 0.00000005411 0.9018217190149 0.4321083048416 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_25 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9067808515567:ℝ):ℂ) + (((-0.4216022856319):ℝ):ℂ) * I)‖ ≤ 0.00000015353 := by
  have hl := lg_25
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.550249925460627726 69.55024996867467094 (-0.4352116) 0.00000005352 0.9067808515567 (-0.4216022856319) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_26 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2841721081406:ℝ):ℂ) + (((-0.9587732854825):ℝ):ℂ) * I)‖ ≤ 0.00000013882 := by
  have hl := lg_26
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.3976918745635919 70.397691917777635114 (-1.2826535) 0.00000003881 0.2841721081406 (-0.9587732854825) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_27 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5032127011932):ℝ):ℂ) + (((-0.8641625873361):ℝ):ℂ) * I)‖ ≤ 0.00000013208 := by
  have hl := lg_27
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.213147146905598644 71.213147179316163465 (-2.0981088) 0.00000003207 (-0.5032127011932) (-0.8641625873361) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_28 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9669817257578):ℝ):ℂ) + (((-0.2548457215488):ℝ):ℂ) * I)‖ ≤ 0.0000001501 := by
  have hl := lg_28
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.998942828889063154 71.998942872103106368 (-2.8839045) 0.00000005009 (-0.9669817257578) (-0.2548457215488) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_29 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8773283653567):ℝ):ℂ) + ((0.4798905492366:ℝ):ℂ) * I)‖ ≤ 0.00000013313 := by
  have hl := lg_29
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.757160976051174044 72.757161019265238865 2.6410627 0.00000003312 (-0.8773283653567) 0.4798905492366 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p607_30 : ‖exp (-((((((21607:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3313703101229):ℝ):ℂ) + ((0.9435007777246:ℝ):ℂ) * I)‖ ≤ 0.00000016018 := by
  have hl := lg_30
  refine (ecis_approx ((((21607:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.489671803107613411 73.489671846321656625 1.9085519 0.00000006017 (-0.3313703101229) 0.9435007777246 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_2 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7884504807803):ℝ):ℂ) + (((-0.6150982354976):ℝ):ℂ) * I)‖ ≤ 0.00000011878 := by
  have hl := lg_2
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.0454526955918 15.0454527064448 (-2.4790821) 0.00000001877 (-0.7884504807803) (-0.6150982354976) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_3 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2807096682958:ℝ):ℂ) + ((0.9597927287312:ℝ):ℂ) * I)‖ ≤ 0.00000011434 := by
  have hl := lg_3
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.846478332187607784 23.84647834304062949 1.2862629 0.00000001433 0.2807096682958 0.9597927287312 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_4 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.243308328277:ℝ):ℂ) + ((0.9699489973143:ℝ):ℂ) * I)‖ ≤ 0.00000014473 := by
  have hl := lg_4
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.0909053911836 30.0909054128896 1.3250211 0.00000004472 0.243308328277 0.9699489973143 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_5 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9297952460377):ℝ):ℂ) + ((0.3680771662117:ℝ):ℂ) * I)‖ ≤ 0.00000012708 := by
  have hl := lg_5
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.934459316009820554 34.93445933771584226 2.7646525 0.00000002707 (-0.9297952460377) 0.3680771662117 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_6 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3690411409803:ℝ):ℂ) + (((-0.929413060089):ℝ):ℂ) * I)‖ ≤ 0.00000011531 := by
  have hl := lg_6
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.891931027779407784 38.89193104948542949 (-1.1928192) 0.0000000153 0.3690411409803 (-0.929413060089) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_7 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.172704896579):ℝ):ℂ) + ((0.9849736131983:ℝ):ℂ) * I)‖ ≤ 0.00000015557 := by
  have hl := lg_7
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.237925684109869932 42.237925705815913344 1.7443715 0.00000005556 (-0.172704896579) 0.9849736131983 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_8 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4047773483853:ℝ):ℂ) + (((-0.9144152766846):ℝ):ℂ) * I)‖ ≤ 0.0000001635 := by
  have hl := lg_8
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.1363580867754 45.1363581193344 (-1.154061) 0.00000006349 0.4047773483853 (-0.9144152766846) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_9 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.842404164234):ℝ):ℂ) + ((0.5388461969913:ℝ):ℂ) * I)‖ ≤ 0.00000012866 := by
  have hl := lg_9
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.692956664375215568 47.69295668608125898 2.5725258 0.00000002865 (-0.842404164234) 0.5388461969913 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_10 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.95950112434:ℝ):ℂ) + ((0.2817047965341:ℝ):ℂ) * I)‖ ≤ 0.00000014585 := by
  have hl := lg_10
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.979912011601620554 49.97991204416064226 0.2855704 0.00000004584 0.95950112434 0.2817047965341 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_11 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2108417360954):ℝ):ℂ) + (((-0.9775202106961):ℝ):ℂ) * I)‖ ≤ 0.00000014957 := by
  have hl := lg_11
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.048714774434277298 52.04871480699332071 (-1.7832323) 0.00000004956 (-0.2108417360954) (-0.9775202106961) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_12 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.862650994717):ℝ):ℂ) + ((0.5057996255746:ℝ):ℂ) * I)‖ ≤ 0.00000014126 := by
  have hl := lg_12
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.937383723371207784 53.93738375593022949 2.611284 0.00000004125 (-0.862650994717) 0.5057996255746 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_13 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6418584051453:ℝ):ℂ) + ((0.76682317893:ℝ):ℂ) * I)‖ ≤ 0.0000001285 := by
  have hl := lg_13
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.6747907361329802 55.674790768692023612 0.873877 0.00000002849 0.6418584051453 0.76682317893 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_14 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7420247902574:ℝ):ℂ) + (((-0.6703724417392):ℝ):ℂ) * I)‖ ≤ 0.00000014766 := by
  have hl := lg_14
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.283378379701669932 57.283378412260713344 (-0.7347106) 0.00000004765 0.7420247902574 (-0.6703724417392) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_15 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6142802972692):ℝ):ℂ) + (((-0.7890879015506):ℝ):ℂ) * I)‖ ≤ 0.00000011643 := by
  have hl := lg_15
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.780937648197428338 58.78093768075647175 (-2.2322699) 0.00000001642 (-0.6142802972692) (-0.7890879015506) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_16 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8816021619546):ℝ):ℂ) + ((0.4719932498875:ℝ):ℂ) * I)‖ ≤ 0.000000154 := by
  have hl := lg_16
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.1818107823672 60.1818108257792 2.6500423 0.00000005399 (-0.8816021619546) 0.4719932498875 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_17 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2344688265278:ℝ):ℂ) + ((0.9721236389404:ℝ):ℂ) * I)‖ ≤ 0.0000001483 := by
  have hl := lg_17
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.497728823514716404 61.49772886692673811 1.3341242 0.00000004829 0.2344688265278 0.9721236389404 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_18 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9956373133333:ℝ):ℂ) + ((0.0933077719083:ℝ):ℂ) * I)‖ ≤ 0.00000012075 := by
  have hl := lg_18
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.738409359967015568 62.73840939252605898 0.0934437 0.00000002074 0.9956373133333 0.0933077719083 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_19 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4712054146763:ℝ):ℂ) + (((-0.8820235014894):ℝ):ℂ) * I)‖ ≤ 0.00000012564 := by
  have hl := lg_19
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.911992464859604718 63.911992497418669836 (-1.0801394) 0.00000002563 0.4712054146763 (-0.8820235014894) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_20 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5832429995163):ℝ):ℂ) + (((-0.8122977308256):ℝ):ℂ) * I)‖ ≤ 0.00000016462 := by
  have hl := lg_20
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.025364707193420554 65.02536475060544226 (-2.1935117) 0.00000006461 (-0.5832429995163) (-0.8122977308256) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_21 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9938504348932):ℝ):ℂ) + ((0.1107308114573:ℝ):ℂ) * I)‖ ≤ 0.00000016269 := by
  have hl := lg_21
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.084404016297477716 66.084404048856542834 3.0306343 0.00000006268 (-0.9938504348932) 0.1107308114573 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_22 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4350326821282):ℝ):ℂ) + ((0.9004146630726:ℝ):ℂ) * I)‖ ≤ 0.00000013448 := by
  have hl := lg_22
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.094167470026077298 67.09416751343812071 2.0208709 0.00000003447 (-0.4350326821282) 0.9004146630726 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_23 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4923568001594:ℝ):ℂ) + ((0.8703934635191:ℝ):ℂ) * I)‖ ≤ 0.0000001506 := by
  have hl := lg_23
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.059037428388578396 68.059037471800643514 1.0560009 0.00000005059 0.4923568001594 0.8703934635191 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_24 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9912740488015:ℝ):ℂ) + ((0.1318171467326:ℝ):ℂ) * I)‖ ≤ 0.00000016003 := by
  have hl := lg_24
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.982836418963007784 68.98283646237502949 0.1322019 0.00000006002 0.9912740488015 0.1318171467326 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_25 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7290384042175:ℝ):ℂ) + (((-0.6844727935982):ℝ):ℂ) * I)‖ ≤ 0.00000014697 := by
  have hl := lg_25
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.868918632019641108 69.86891867543168452 (-0.7538803) 0.00000004696 0.7290384042175 (-0.6844727935982) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_26 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0344019838175):ℝ):ℂ) + (((-0.9994080765679):ℝ):ℂ) * I)‖ ≤ 0.00000014727 := by
  have hl := lg_26
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.7202434317247802 70.720243475136823612 (-1.6052051) 0.00000004726 (-0.0344019838175) (-0.9994080765679) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_27 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7536516506064):ℝ):ℂ) + (((-0.6572740596612):ℝ):ℂ) * I)‖ ≤ 0.00000015016 := by
  have hl := lg_27
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.539434996562823352 71.53943502912188847 (-2.4243966) 0.00000005015 (-0.7536516506064) (-0.6572740596612) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_28 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9973947079281):ℝ):ℂ) + ((0.0721373417118:ℝ):ℂ) * I)‖ ≤ 0.00000013257 := by
  have hl := lg_28
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.328831075293469932 72.328831118705513344 3.0693926 0.00000003256 (-0.9973947079281) 0.0721373417118 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_29 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6719984392376):ℝ):ℂ) + ((0.7405525623767:ℝ):ℂ) * I)‖ ≤ 0.00000012305 := by
  have hl := lg_29
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.090523263116896552 73.09052330652896167 2.3077004 0.00000002304 (-0.6719984392376) 0.7405525623767 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p706_30 : ‖exp (-((((((21706:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0010369730193):ℝ):ℂ) + ((0.9999994623432:ℝ):ℂ) * I)‖ ≤ 0.00000014238 := by
  have hl := lg_30
  refine (ecis_approx ((((21706:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.826390343789228338 73.82639038720127175 1.5718333 0.00000004237 (-0.0010369730193) 0.9999994623432 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_2 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8287707387938):ℝ):ℂ) + (((-0.5595882972842):ℝ):ℂ) * I)‖ ≤ 0.00000014793 := by
  have hl := lg_2
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.1140742664415 15.114074277344 (-2.5477037) 0.00000004792 (-0.8287707387938) (-0.5595882972842) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_3 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3832348695054:ℝ):ℂ) + ((0.9236509269173:ℝ):ℂ) * I)‖ ≤ 0.00000013094 := by
  have hl := lg_3
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.95524094874001602 23.955240959642537825 1.1775003 0.00000003093 0.3832348695054 0.9236509269173 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_4 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3737217889135:ℝ):ℂ) + ((0.9275408478829:ℝ):ℂ) * I)‖ ≤ 0.00000011881 := by
  have hl := lg_4
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.228148532883 30.228148554688 1.187778 0.0000000188 0.3737217889135 0.9275408478829 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_5 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8596181620495):ℝ):ℂ) + ((0.5109369974805:ℝ):ℂ) * I)‖ ≤ 0.00000014803 := by
  have hl := lg_5
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.093793669289327245 35.09379369109434905 2.6053182 0.00000004802 (-0.8596181620495) 0.5109369974805 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_6 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1992504035735:ℝ):ℂ) + (((-0.9799486092014):ℝ):ℂ) * I)‖ ≤ 0.00000012791 := by
  have hl := lg_6
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.06931521518151602 39.069315236986537825 (-1.3702034) 0.0000000279 0.1992504035735 (-0.9799486092014) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_7 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0190687709809:ℝ):ℂ) + ((0.9998181744563:ℝ):ℂ) * I)‖ ≤ 0.00000016038 := by
  have hl := lg_7
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.43057078881487671 42.43057081061992032 1.5517264 0.00000006037 0.0190687709809 0.9998181744563 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_8 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2093113206538:ℝ):ℂ) + (((-0.9778490533033):ℝ):ℂ) * I)‖ ≤ 0.00000015095 := by
  have hl := lg_8
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.3422227993245 45.342222832032 (-1.3599257) 0.00000005094 0.2093113206538 (-0.9778490533033) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_9 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7062619987919):ℝ):ℂ) + ((0.7079505555035:ℝ):ℂ) * I)‖ ≤ 0.00000015997 := by
  have hl := lg_9
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.91048189748003204 47.91048191928507565 2.3550005 0.00000005996 (-0.7062619987919) 0.7079505555035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_10 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9983407437532:ℝ):ℂ) + ((0.057582630734:ℝ):ℂ) * I)‖ ≤ 0.00000012172 := by
  have hl := lg_10
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.207867935730827245 50.20786796843834905 0.0576145 0.00000002171 0.9983407437532 0.057582630734 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_11 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4348103564904):ℝ):ℂ) + (((-0.9005220451963):ℝ):ℂ) * I)‖ ≤ 0.00000015109 := by
  have hl := lg_11
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.286106406364112065 52.286106439071655675 (-2.020624) 0.00000005108 (-0.4348103564904) (-0.9005220451963) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_12 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7135007428914):ℝ):ℂ) + ((0.7006544725237:ℝ):ℂ) * I)‖ ≤ 0.00000014973 := by
  have hl := lg_12
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.18338948162301602 54.183389514330537825 2.3652783 0.00000004972 (-0.7135007428914) 0.7006544725237 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_13 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8139092503829:ℝ):ℂ) + ((0.5809920241631:ℝ):ℂ) * I)‖ ≤ 0.00000014219 := by
  have hl := lg_13
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.9287207224444685 55.92872075515201211 0.619947 0.00000004218 0.8139092503829 0.5809920241631 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_14 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5436829104582:ℝ):ℂ) + (((-0.8392907082029):ℝ):ℂ) * I)‖ ≤ 0.00000012336 := by
  have hl := lg_14
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.54464505525637671 57.54464508796392032 (-0.9959773) 0.00000002335 0.5436829104582 (-0.8392907082029) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_15 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8013631410382):ℝ):ℂ) + (((-0.5981781642083):ℝ):ℂ) * I)‖ ≤ 0.0000001466 := by
  have hl := lg_15
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.049034618029343265 59.049034650736886875 (-2.5003669) 0.00000004659 (-0.8013631410382) (-0.5981781642083) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_16 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7206640489785):ℝ):ℂ) + ((0.6932844499067:ℝ):ℂ) * I)‖ ≤ 0.0000001376 := by
  have hl := lg_16
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.456297065766 60.456297109376 2.375556 0.00000003759 (-0.7206640489785) 0.6932844499067 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_17 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4944137280059:ℝ):ℂ) + ((0.8692267055029:ℝ):ℂ) * I)‖ ≤ 0.00000012734 := by
  have hl := lg_17
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.77821694447334337 61.778216988083365175 1.0536361 0.00000002733 0.4944137280059 0.8692267055029 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_18 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9814901436326:ℝ):ℂ) + (((-0.19151265742):ℝ):ℂ) * I)‖ ≤ 0.00000012485 := by
  have hl := lg_18
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.02455616392153204 63.02455619662907565 (-0.1927031) 0.00000002484 0.9814901436326 (-0.19151265742) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_19 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1978434825344:ℝ):ℂ) + (((-0.9802336233871):ℝ):ℂ) * I)‖ ≤ 0.00000014809 := by
  have hl := lg_19
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.203491923719878415 64.20349195642744383 (-1.3716389) 0.00000004808 0.1978434825344 (-0.9802336233871) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_20 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7951730294852):ℝ):ℂ) + (((-0.60638259633):ℝ):ℂ) * I)‖ ≤ 0.00000016964 := by
  have hl := lg_20
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.321942202172327245 65.32194224578234905 (-2.4900892) 0.00000006963 (-0.7951730294852) (-0.60638259633) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_21 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9161751255063):ℝ):ℂ) + ((0.4007781671528:ℝ):ℂ) * I)‖ ≤ 0.00000014144 := by
  have hl := lg_21
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.38581173755489273 66.385811770262458145 2.7292266 0.00000004143 (-0.9161751255063) 0.4007781671528 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_22 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1435635894397):ℝ):ℂ) + ((0.989641094431:ℝ):ℂ) * I)‖ ≤ 0.00000013746 := by
  have hl := lg_22
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.400180672805612065 67.400180716415655675 1.7148577 0.00000003745 (-0.1435635894397) 0.989641094431 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_23 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7346898063072:ℝ):ℂ) + ((0.6784031902256:ℝ):ℂ) * I)‖ ≤ 0.00000012333 := by
  have hl := lg_23
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.36945135566262563 68.369451399272691045 0.745587 0.00000002332 0.7346898063072 0.6784031902256 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_24 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9834065811256:ℝ):ℂ) + (((-0.1814152590025):ℝ):ℂ) * I)‖ ≤ 0.00000013093 := by
  have hl := lg_24
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.29746374806451602 69.297463791674537825 (-0.1824254) 0.00000003092 0.9834065811256 (-0.1814152590025) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_25 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4778866875855:ℝ):ℂ) + (((-0.878421489849):ℝ):ℂ) * I)‖ ≤ 0.00000014041 := by
  have hl := lg_25
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.18758733857865449 70.1875873821886981 (-1.072549) 0.0000000404 0.4778866875855 (-0.878421489849) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_26 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3494277395091):ℝ):ℂ) + (((-0.9369633156422):ℝ):ℂ) * I)‖ ≤ 0.00000015354 := by
  have hl := lg_26
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.0427949888859685 71.04279503249601211 (-1.9277566) 0.00000005353 (-0.3494277395091) (-0.9369633156422) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_27 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9245634089763):ℝ):ℂ) + (((-0.381028217632):ℝ):ℂ) * I)‖ ≤ 0.00000013277 := by
  have hl := lg_27
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.86572284622004806 71.865722878927613475 (-2.7506845) 0.00000003276 (-0.9245634089763) (-0.381028217632) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_28 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9202457428811):ℝ):ℂ) + ((0.391340992698:ℝ):ℂ) * I)‖ ≤ 0.00000016447 := by
  have hl := lg_28
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.65871932169787671 72.65871936530792032 2.7395043 0.00000006446 (-0.9202457428811) 0.391340992698 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_29 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3926780821774):ℝ):ℂ) + ((0.9196759884733:ℝ):ℂ) * I)‖ ≤ 0.00000013599 := by
  have hl := lg_29
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.42388555018261906 73.423885593792684475 1.9743381 0.00000003598 (-0.3926780821774) 0.9196759884733 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p805_30 : ‖exp (-((((((21805:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3294127344023:ℝ):ℂ) + ((0.9441860253221:ℝ):ℂ) * I)‖ ≤ 0.00000014194 := by
  have hl := lg_30
  refine (ecis_approx ((((21805:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.163108884470843265 74.163108928080886875 1.2351148 0.00000004193 0.3294127344023 0.9441860253221 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_2 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8651898594364):ℝ):ℂ) + (((-0.5014444206931):ℝ):ℂ) * I)‖ ≤ 0.0000001339 := by
  have hl := lg_2
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.1826958372912 15.1826958482432 (-2.6163252) 0.00000003389 (-0.8651898594364) (-0.5014444206931) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_3 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4812311364158:ℝ):ℂ) + ((0.8765937447552:ℝ):ℂ) * I)‖ ≤ 0.00000014754 := by
  have hl := lg_3
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.064003565292424256 24.06400357624444616 1.0687377 0.00000004753 0.4812311364158 0.8765937447552 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_4 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4971069920485:ℝ):ℂ) + ((0.8676892522421:ℝ):ℂ) * I)‖ ≤ 0.0000001606 := by
  have hl := lg_4
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.3653916745824 30.3653916964864 1.0505349 0.00000006059 0.4971069920485 0.8676892522421 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_5 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7676636584757):ℝ):ℂ) + ((0.6408529530377:ℝ):ℂ) * I)‖ ≤ 0.00000012052 := by
  have hl := lg_5
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.253128022568833936 35.25312804447285584 2.4459838 0.00000002051 (-0.7676636584757) 0.6408529530377 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_6 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0232066433069:ℝ):ℂ) + (((-0.9997306895891):ℝ):ℂ) * I)‖ ≤ 0.00000014051 := by
  have hl := lg_6
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.246699402583624256 39.24669942448764616 (-1.5475876) 0.0000000405 0.0232066433069 (-0.9997306895891) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_7 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2101370394428:ℝ):ℂ) + ((0.9776719412227:ℝ):ℂ) * I)‖ ≤ 0.00000015675 := by
  have hl := lg_7
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.623215893519883488 42.623215915423927296 1.3590812 0.00000005674 0.2101370394428 0.9776719412227 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_8 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0050059058874:ℝ):ℂ) + (((-0.9999874703745):ℝ):ℂ) * I)‖ ≤ 0.0000001384 := by
  have hl := lg_8
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.5480875118736 45.5480875447296 (-1.5657904) 0.00000003839 0.0050059058874 (-0.9999874703745) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_9 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5368331023188):ℝ):ℂ) + ((0.8436884616058:ℝ):ℂ) * I)‖ ≤ 0.00000012687 := by
  have hl := lg_9
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.128007130584848512 48.12800715248889232 2.1374753 0.00000002686 (-0.5368331023188) 0.8436884616058 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_10 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9855269506198:ℝ):ℂ) + (((-0.1695188178404):ℝ):ℂ) * I)‖ ≤ 0.00000013529 := by
  have hl := lg_10
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.435823859860033936 50.43582389271605584 (-0.1703414) 0.00000003528 0.9855269506198 (-0.1695188178404) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_11 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6343900995333):ℝ):ℂ) + (((-0.7730130669005):ℝ):ℂ) * I)‖ ≤ 0.00000011916 := by
  have hl := lg_11
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.523498038293946832 52.52349807114999064 (-2.2580156) 0.00000001915 (-0.6343900995333) (-0.7730130669005) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_12 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5213875228708):ℝ):ℂ) + ((0.8533200167507:ℝ):ℂ) * I)‖ ≤ 0.00000012476 := by
  have hl := lg_12
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.429395239874824256 54.42939527273084616 2.1192725 0.00000002475 (-0.5213875228708) 0.8533200167507 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_13 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9337602607178:ℝ):ℂ) + ((0.3578991135839:ℝ):ℂ) * I)‖ ≤ 0.00000015588 := by
  have hl := lg_13
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.1826507087559568 56.182650741612000608 0.366017 0.00000005587 0.9337602607178 0.3578991135839 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_14 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.308439704617:ℝ):ℂ) + (((-0.951243895442):ℝ):ℂ) * I)‖ ≤ 0.00000013382 := by
  have hl := lg_14
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.805911730811083488 57.805911763667127296 (-1.257244) 0.00000003381 0.308439704617 (-0.951243895442) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_15 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9311913420459):ℝ):ℂ) + (((-0.3645307728257):ℝ):ℂ) * I)‖ ≤ 0.00000015612 := by
  have hl := lg_15
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.317131587861258192 59.317131620717302 (-2.7684638) 0.00000005611 (-0.9311913420459) (-0.3645307728257) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_16 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.505769190646):ℝ):ℂ) + ((0.862668839003:ℝ):ℂ) * I)‖ ≤ 0.00000012265 := by
  have hl := lg_16
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.7307833491648 60.7307833929728 2.1010697 0.00000002264 (-0.505769190646) 0.862668839003 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_17 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7157156822893:ℝ):ℂ) + ((0.6983917683687:ℝ):ℂ) * I)‖ ≤ 0.00000013746 := by
  have hl := lg_17
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.058705065431970336 62.05870510923999224 0.773148 0.00000003745 0.7157156822893 0.6983917683687 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_18 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8875254282647:ℝ):ℂ) + (((-0.4607587375011):ℝ):ℂ) * I)‖ ≤ 0.00000012895 := by
  have hl := lg_18
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.310702967876048512 63.31070300073209232 (-0.4788499) 0.00000002894 0.8875254282647 (-0.4607587375011) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_19 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0922107951956):ℝ):ℂ) + (((-0.9957395087316):ℝ):ℂ) * I)‖ ≤ 0.00000014366 := by
  have hl := lg_19
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.494991382580152112 64.494991415436217824 (-1.6631383) 0.00000004365 (-0.0922107951956) (-0.9957395087316) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_20 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9376721892564):ℝ):ℂ) + (((-0.347521028602):ℝ):ℂ) * I)‖ ≤ 0.00000016918 := by
  have hl := lg_20
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.618519697151233936 65.61851974095925584 (-2.7866666) 0.00000006917 (-0.9376721892564) (-0.347521028602) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_21 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7558966217983):ℝ):ℂ) + ((0.6546909936134:ℝ):ℂ) * I)‖ ≤ 0.00000012018 := by
  have hl := lg_21
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.687219458812307744 66.687219491668373456 2.4278189 0.00000002017 (-0.7558966217983) 0.6546909936134 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_22 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1612447985837:ℝ):ℂ) + ((0.9869144415448:ℝ):ℂ) * I)‖ ≤ 0.00000014043 := by
  have hl := lg_22
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.706193875585146832 67.70619391939319064 1.4088445 0.00000004042 0.1612447985837 0.9869144415448 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_23 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9067970825727:ℝ):ℂ) + ((0.4215673742567:ℝ):ℂ) * I)‖ ≤ 0.00000014778 := by
  have hl := lg_23
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.679865282936672864 68.679865326744738576 0.4351731 0.00000004777 0.9067970825727 0.4215673742567 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_24 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.878991759143:ℝ):ℂ) + (((-0.4768369609822):ℝ):ℂ) * I)‖ ≤ 0.00000014201 := by
  have hl := lg_24
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.612091077166024256 69.61209112097404616 (-0.4970527) 0.000000042 0.878991759143 (-0.4768369609822) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_25 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1786149921741:ℝ):ℂ) + (((-0.9839190437077):ℝ):ℂ) * I)‖ ≤ 0.00000013385 := by
  have hl := lg_25
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.506256045137667872 70.50625608894571168 (-1.3912177) 0.00000003384 0.1786149921741 (-0.9839190437077) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_26 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6284133950426):ℝ):ℂ) + (((-0.7778795568187):ℝ):ℂ) * I)‖ ≤ 0.00000013294 := by
  have hl := lg_26
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.3653465460471568 71.365346589855200608 (-2.2503082) 0.00000003293 (-0.6284133950426) (-0.7778795568187) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_27 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.997912831145):ℝ):ℂ) + (((-0.064575389223):ℝ):ℂ) * I)‖ ≤ 0.00000014977 := by
  have hl := lg_27
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.192010695877272768 72.19201072873333848 (-3.0769723) 0.00000004976 (-0.997912831145) (-0.064575389223) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_28 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.743854844017):ℝ):ℂ) + ((0.6683412085156:ℝ):ℂ) * I)‖ ≤ 0.00000012577 := by
  have hl := lg_28
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.988607568102283488 72.988607611910327296 2.4096161 0.00000002576 (-0.743854844017) 0.6683412085156 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_29 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0701218798854):ℝ):ℂ) + ((0.9975384313203:ℝ):ℂ) * I)‖ ≤ 0.00000014892 := by
  have hl := lg_29
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.757247837248341568 73.75724788105640728 1.6409758 0.00000004891 (-0.0701218798854) 0.9975384313203 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p904_30 : ‖exp (-((((((21904:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6228654679853:ℝ):ℂ) + ((0.7823289645612:ℝ):ℂ) * I)‖ ≤ 0.00000016102 := by
  have hl := lg_30
  refine (ecis_approx ((((21904:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.499827425152458192 74.499827468960502 0.8983962 0.00000006101 0.6228654679853 0.7823289645612 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_2 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8975365212255):ℝ):ℂ) + (((-0.4409401239997):ℝ):ℂ) * I)‖ ≤ 0.00000010623 := by
  have hl := lg_2
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.2513174081409 15.2513174191424 (-2.6849468) 0.00000000622 (-0.8975365212255) (-0.4409401239997) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_3 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5735404656824:ℝ):ℂ) + ((0.8191772300454:ℝ):ℂ) * I)‖ ≤ 0.00000014689 := by
  have hl := lg_3
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.172766181844832492 24.172766192846354495 0.959975 0.00000004688 0.5735404656824 0.8191772300454 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_4 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6111436196688:ℝ):ℂ) + ((0.7915197256785:ℝ):ℂ) * I)‖ ≤ 0.00000011963 := by
  have hl := lg_4
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.5026348162818 30.5026348382848 0.9132917 0.00000001962 0.6111436196688 0.7915197256785 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_5 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6562614033244):ℝ):ℂ) + ((0.7545336112388:ℝ):ℂ) * I)‖ ≤ 0.00000015479 := by
  have hl := lg_5
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.412462375848340627 35.41246239785136263 2.2866495 0.00000005478 (-0.6562614033244) 0.7545336112388 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_6 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1535654049255):ℝ):ℂ) + (((-0.9881384854409):ℝ):ℂ) * I)‖ ≤ 0.00000015311 := by
  have hl := lg_6
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.424083589985732492 39.424083611988754495 (-1.7249718) 0.0000000531 (-0.1535654049255) (-0.9881384854409) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_7 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3934306626866:ℝ):ℂ) + ((0.919354291695:ℝ):ℂ) * I)‖ ≤ 0.00000015205 := by
  have hl := lg_7
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.815860998224890266 42.815861020227934272 1.1664361 0.00000005204 0.3934306626866 0.919354291695 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_8 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1995109123495):ℝ):ℂ) + (((-0.9798956045685):ℝ):ℂ) * I)‖ ≤ 0.00000012585 := by
  have hl := lg_8
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.7539522244227 45.7539522574272 (-1.7716551) 0.00000002584 (-0.1995109123495) (-0.9798956045685) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_9 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3421027624159):ℝ):ℂ) + ((0.9396625457818:ℝ):ℂ) * I)‖ ≤ 0.00000012827 := by
  have hl := lg_9
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.345532363689664984 48.34553238569270899 1.9199501 0.00000002826 (-0.3421027624159) 0.9396625457818 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_10 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9217227211301:ℝ):ℂ) + (((-0.3878494880137):ℝ):ℂ) * I)‖ ≤ 0.00000015957 := by
  have hl := lg_10
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.663779783989240627 50.66377981699376263 (-0.3982973) 0.00000005956 0.9217227211301 (-0.3878494880137) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_11 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7983865127654):ℝ):ℂ) + (((-0.6021453115201):ℝ):ℂ) * I)‖ ≤ 0.00000014581 := by
  have hl := lg_11
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.760889670223781599 52.760889703228325605 (-2.4954072) 0.0000000458 (-0.7983865127654) (-0.6021453115201) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_12 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.297879340184):ℝ):ℂ) + ((0.9546035295817:ℝ):ℂ) * I)‖ ≤ 0.0000001665 := by
  have hl := lg_12
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.675400998126632492 54.675401031131154495 1.8732667 0.00000006649 (-0.297879340184) 0.9546035295817 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_13 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9937248150025:ℝ):ℂ) + ((0.1118525460068:ℝ):ℂ) * I)‖ ≤ 0.00000016347 := by
  have hl := lg_13
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.4365806950674451 56.436580728071989106 0.1120871 0.00000006346 0.9937248150025 0.1118525460068 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_14 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0522618070919:ℝ):ℂ) + (((-0.9986334179865):ℝ):ℂ) * I)‖ ≤ 0.00000015827 := by
  have hl := lg_14
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.067178406365790266 58.067178439370334272 (-1.5185107) 0.00000005826 0.0522618070919 (-0.9986334179865) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_15 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9944892235479):ℝ):ℂ) + (((-0.1048388467135):ℝ):ℂ) * I)‖ ≤ 0.0000001261 := by
  have hl := lg_15
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.585228557693173119 59.585228590697717125 (-3.0365608) 0.00000002609 (-0.9944892235479) (-0.1048388467135) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_16 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2530069522764):ℝ):ℂ) + ((0.9674644603801:ℝ):ℂ) * I)‖ ≤ 0.00000013925 := by
  have hl := lg_16
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.0052696325636 61.0052696765696 1.8265834 0.00000003924 (-0.2530069522764) 0.9674644603801 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_17 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8810779210056:ℝ):ℂ) + ((0.4729711377202:ℝ):ℂ) * I)‖ ≤ 0.00000015862 := by
  have hl := lg_17
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.339193186390597302 62.339193230396619305 0.4926599 0.00000005861 0.8810779210056 0.4729711377202 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_18 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7213846428048:ℝ):ℂ) + (((-0.6925346179979):ℝ):ℂ) * I)‖ ≤ 0.00000013305 := by
  have hl := lg_18
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.596849771830564984 63.59684980483510899 (-0.7649967) 0.00000003304 0.7213846428048 (-0.6925346179979) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_19 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3744851641353):ℝ):ℂ) + (((-0.9272329059302):ℝ):ℂ) * I)‖ ≤ 0.00000013037 := by
  have hl := lg_19
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.786490841440425809 64.786490874444991818 (-1.9546378) 0.00000003036 (-0.3744851641353) (-0.9272329059302) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p003_20 : ‖exp (-((((((22003:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9982982057866):ℝ):ℂ) + (((-0.0583154505059):ℝ):ℂ) * I)‖ ≤ 0.00000016436 := by
  have hl := lg_20
  refine (ecis_approx ((((22003:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.915097192130140627 65.91509723613616263 (-3.0832441) 0.00000006435 (-0.9982982057866) (-0.0583154505059) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_2 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.925658409991):ℝ):ℂ) + (((-0.3783602884301):ℝ):ℂ) * I)‖ ≤ 0.00000013538 := by
  have hl := lg_2
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.3199389789906 15.3199389900416 (-2.7535684) 0.00000003537 (-0.925658409991) (-0.3783602884301) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_3 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6590718086858:ℝ):ℂ) + ((0.7520800163517:ℝ):ℂ) * I)‖ ≤ 0.00000013034 := by
  have hl := lg_3
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.281528798397240728 24.28152880944826283 0.8512124 0.00000003033 0.6590718086858 0.7520800163517 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_4 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7136869191387:ℝ):ℂ) + ((0.7004648324151:ℝ):ℂ) * I)‖ ≤ 0.0000001442 := by
  have hl := lg_4
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.6398779579812 30.6398779800832 0.7760486 0.00000004419 0.7136869191387 0.7004648324151 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_5 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5282334979799):ℝ):ℂ) + ((0.8490991529877:ℝ):ℂ) * I)‖ ≤ 0.00000011396 := by
  have hl := lg_5
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.571796729127847318 35.57179675122986942 2.1273151 0.00000001395 (-0.5282334979799) 0.8490991529877 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_6 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.325518056007):ℝ):ℂ) + (((-0.9455358243935):ℝ):ℂ) * I)‖ ≤ 0.00000015643 := by
  have hl := lg_6
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.601467777387840728 39.60146779948986283 (-1.9023559) 0.00000005642 (-0.325518056007) (-0.9455358243935) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_7 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5621683347641:ℝ):ℂ) + ((0.8270228312378:ℝ):ℂ) * I)‖ ≤ 0.00000014734 := by
  have hl := lg_7
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.008506102929897044 43.008506125031941248 0.973791 0.00000004733 0.5621683347641 0.8270228312378 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_8 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3956022227523):ℝ):ℂ) + (((-0.9184219516923):ℝ):ℂ) * I)‖ ≤ 0.00000011988 := by
  have hl := lg_8
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.9598169369718 45.9598169701248 (-1.9775198) 0.00000001987 (-0.3956022227523) (-0.9184219516923) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_9 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1312487019912):ℝ):ℂ) + ((0.9913494733065:ℝ):ℂ) * I)‖ ≤ 0.00000016066 := by
  have hl := lg_9
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.563057596794481456 48.56305761889652566 1.7024248 0.00000006065 (-0.1312487019912) 0.9913494733065 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_10 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8102291803705:ℝ):ℂ) + (((-0.5861131932282):ℝ):ℂ) * I)‖ ≤ 0.00000014933 := by
  have hl := lg_10
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.891735708118447318 50.89173574127146942 (-0.6262533) 0.00000004932 0.8102291803705 (-0.5861131932282) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_11 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.917600976508):ℝ):ℂ) + (((-0.3975027644838):ℝ):ℂ) * I)‖ ≤ 0.0000001553 := by
  have hl := lg_11
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.998281302153616366 52.99828133530666057 (-2.7327989) 0.00000005529 (-0.917600976508) (-0.3975027644838) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_12 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0564346739844):ℝ):ℂ) + ((0.9984062938363:ℝ):ℂ) * I)‖ ≤ 0.00000012493 := by
  have hl := lg_12
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.921406756378440728 54.92140678953146283 1.627261 0.00000002492 (-0.0564346739844) 0.9984062938363 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_13 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9899571508271:ℝ):ℂ) + (((-0.141367745707):ℝ):ℂ) * I)‖ ≤ 0.00000014993 := by
  have hl := lg_13
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.6905106813789334 56.690510714531977604 (-0.1418429) 0.00000004992 0.9899571508271 (-0.141367745707) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_14 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2074631520763):ℝ):ℂ) + (((-0.9782428331093):ℝ):ℂ) * I)‖ ≤ 0.00000015047 := by
  have hl := lg_14
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.328445081920497044 58.328445115073541248 (-1.7797773) 0.00000005046 (-0.2074631520763) (-0.9782428331093) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_15 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9867343116288):ℝ):ℂ) + ((0.1623434565354:ℝ):ℂ) * I)‖ ≤ 0.00000014429 := by
  have hl := lg_15
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.853325527525088046 59.85332556067813225 2.9785275 0.00000004428 (-0.9867343116288) 0.1623434565354 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_16 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0186981370819:ℝ):ℂ) + ((0.9998251745528:ℝ):ℂ) * I)‖ ≤ 0.00000015585 := by
  have hl := lg_16
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.2797559159624 61.2797559601664 1.5520971 0.00000005584 0.0186981370819 0.9998251745528 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_17 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9775758963822:ℝ):ℂ) + ((0.2105833963365:ℝ):ℂ) * I)‖ ≤ 0.00000016446 := by
  have hl := lg_17
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.619681307349224268 62.61968135155324637 0.2121717 0.00000006445 0.9775758963822 0.2105833963365 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_18 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4965788243394:ℝ):ℂ) + (((-0.8679916308454):ℝ):ℂ) * I)‖ ≤ 0.00000013716 := by
  have hl := lg_18
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.882996575785081456 63.88299660893812566 (-1.0511435) 0.00000003715 0.4965788243394 (-0.8679916308454) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_19 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6251634024971):ℝ):ℂ) + (((-0.7804938950203):ℝ):ℂ) * I)‖ ≤ 0.00000016167 := by
  have hl := lg_19
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.077990300300699506 65.077990333453765812 (-2.2461372) 0.00000006166 (-0.6251634024971) (-0.7804938950203) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p102_20 : ‖exp (-((((((22102:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9717574335539):ℝ):ℂ) + ((0.2359819697628:ℝ):ℂ) * I)‖ ≤ 0.00000015235 := by
  have hl := lg_20
  refine (ecis_approx ((((22102:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.211674687109047318 66.21167473131306942 2.9033637 0.00000005234 (-0.9717574335539) 0.2359819697628 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_2 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.949423122451):ℝ):ℂ) + (((-0.3139995769957):ℝ):ℂ) * I)‖ ≤ 0.0000001466 := by
  have hl := lg_2
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.3885605498403 15.3885605609408 (-2.8221899) 0.00000004659 (-0.949423122451) (-0.3139995769957) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_3 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7368144738902:ℝ):ℂ) + ((0.6760949867186:ℝ):ℂ) * I)‖ ≤ 0.00000011378 := by
  have hl := lg_3
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.390291414949648964 24.390291426050171165 0.7424498 0.00000001377 0.7368144738902 0.6760949867186 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_4 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8028085950659:ℝ):ℂ) + ((0.5962368318784:ℝ):ℂ) * I)‖ ≤ 0.00000013623 := by
  have hl := lg_4
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.7771210996806 30.7771211218816 0.6388054 0.00000003622 0.8028085950659 0.5962368318784 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_5 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3868234381154):ℝ):ℂ) + ((0.9221537983013:ℝ):ℂ) * I)‖ ≤ 0.00000016069 := by
  have hl := lg_5
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.731131082407354009 35.73113110460837621 1.9679807 0.00000006068 (-0.3868234381154) 0.9221537983013 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_6 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4872551586112):ℝ):ℂ) + (((-0.873259646612):ℝ):ℂ) * I)‖ ≤ 0.00000014393 := by
  have hl := lg_6
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.778851964789948964 39.778851986990971165 (-2.0797401) 0.00000004392 (-0.4872551586112) (-0.873259646612) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_7 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7101071835566:ℝ):ℂ) + ((0.7040935931119:ℝ):ℂ) * I)‖ ≤ 0.00000014264 := by
  have hl := lg_7
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.201151207634903822 43.201151229835948224 0.7811459 0.00000004263 0.7101071835566 0.7040935931119 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_8 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5749869300533):ℝ):ℂ) + (((-0.8181625940225):ℝ):ℂ) * I)‖ ≤ 0.00000013258 := by
  have hl := lg_8
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.1656816495209 46.1656816828224 (-2.1833845) 0.00000003257 (-0.5749869300533) (-0.8181625940225) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_9 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.085791137868:ℝ):ℂ) + ((0.9963131438776:ℝ):ℂ) * I)‖ ≤ 0.00000012755 := by
  have hl := lg_9
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.780582829899297928 48.78058285210034233 1.4848996 0.00000002754 0.085791137868 0.9963131438776 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_10 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6568150191692:ℝ):ℂ) + (((-0.7540517426502):ℝ):ℂ) * I)‖ ≤ 0.0000001252 := by
  have hl := lg_10
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.119691632247654009 51.11969166554917621 (-0.8542092) 0.00000002519 0.6568150191692 (-0.7540517426502) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_11 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.985346578349):ℝ):ℂ) + (((-0.1705641233469):ℝ):ℂ) * I)‖ ≤ 0.00000012337 := by
  have hl := lg_11
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.235672934083451133 53.235672967384995535 (-2.9701905) 0.00000002336 (-0.985346578349) (-0.1705641233469) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_12 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.188408259678:ℝ):ℂ) + ((0.982090794013:ℝ):ℂ) * I)‖ ≤ 0.00000015 := by
  have hl := lg_12
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.167412514630248964 55.167412547931771165 1.3812552 0.00000004999 0.188408259678 0.982090794013 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_13 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9226988704563:ℝ):ℂ) + (((-0.3855214578445):ℝ):ℂ) * I)‖ ≤ 0.00000013639 := by
  have hl := lg_13
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.9444406676904217 56.944440700991966102 (-0.3957729) 0.00000003638 0.9226988704563 (-0.3855214578445) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_14 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4531070890618):ℝ):ℂ) + (((-0.8914560930507):ℝ):ℂ) * I)‖ ≤ 0.00000012618 := by
  have hl := lg_14
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.589711757475203822 58.589711790776748224 (-2.041044) 0.00000002617 (-0.4531070890618) (-0.8914560930507) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_15 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9084807098137):ℝ):ℂ) + ((0.4179267875713:ℝ):ℂ) * I)‖ ≤ 0.00000015888 := by
  have hl := lg_15
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.121422497357002973 60.121422530658547375 2.7104306 0.00000005887 (-0.9084807098137) 0.4179267875713 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_16 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2890031848905:ℝ):ℂ) + ((0.9573281355539:ℝ):ℂ) * I)‖ ≤ 0.00000017198 := by
  have hl := lg_16
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.5542421993612 61.5542422437632 1.2776109 0.00000007197 0.2890031848905 0.9573281355539 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_17 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9976673421921:ℝ):ℂ) + (((-0.0682632721401):ℝ):ℂ) * I)‖ ≤ 0.0000001435 := by
  have hl := lg_17
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.900169428307851234 62.900169472709873435 (-0.0683164) 0.00000004349 0.9976673421921 (-0.0682632721401) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_18 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2313898158378:ℝ):ℂ) + (((-0.9728611170802):ℝ):ℂ) * I)‖ ≤ 0.00000014126 := by
  have hl := lg_18
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.169143379739597928 64.16914341304114233 (-1.3372903) 0.00000004125 0.2313898158378 (-0.9728611170802) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_19 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8230954632382):ℝ):ℂ) + (((-0.5679030360349):ℝ):ℂ) * I)‖ ≤ 0.00000012068 := by
  have hl := lg_19
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.369489759160973203 65.369489792462539806 (-2.5376367) 0.00000002067 (-0.8230954632382) (-0.5679030360349) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_20 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8603672910436):ℝ):ℂ) + ((0.5096745279309:ℝ):ℂ) * I)‖ ≤ 0.00000014753 := by
  have hl := lg_20
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.508252182087954009 66.50825222648997621 2.6067862 0.00000004752 (-0.8603672910436) 0.5096745279309 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_21 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0471831023742:ℝ):ℂ) + ((0.9988862572136:ℝ):ℂ) * I)‖ ≤ 0.00000015641 := by
  have hl := lg_21
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.591442622584552786 67.591442655886119389 1.5235957 0.0000000564 0.0471831023742 0.9988862572136 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_22 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8819537660578:ℝ):ℂ) + ((0.4713359253616:ℝ):ℂ) * I)‖ ≤ 0.00000014937 := by
  have hl := lg_22
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.624233483923751133 68.624233528325795535 0.4908049 0.00000004936 0.8819537660578 0.4713359253616 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_23 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8794605410924:ℝ):ℂ) + (((-0.4759718023807):ℝ):ℂ) * I)‖ ≤ 0.0000001302 := by
  have hl := lg_23
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.611107064758814566 69.611107109160881169 (-0.4960687) 0.00000003019 0.8794605410924 (-0.4759718023807) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_24 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1294969357818:ℝ):ℂ) + (((-0.9915798221137):ℝ):ℂ) * I)‖ ≤ 0.00000012991 := by
  have hl := lg_24
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.555973064470548964 70.555973108872571165 (-1.4409347) 0.0000000299 0.1294969357818 (-0.9915798221137) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_25 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7007351789818):ℝ):ℂ) + (((-0.7134214805524):ℝ):ℂ) * I)‖ ≤ 0.00000013026 := by
  have hl := lg_25
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.462262164814708018 71.46226220921675242 (-2.3472238) 0.00000003025 (-0.7007351789818) (-0.7134214805524) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_26 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9970852090436):ℝ):ℂ) + ((0.0762960378177:ℝ):ℂ) * I)‖ ≤ 0.00000016864 := by
  have hl := lg_26
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.3330012175307217 72.333001261932766102 3.0652224 0.00000006863 (-0.9970852090436) 0.0762960378177 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_27 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6103901696637):ℝ):ℂ) + ((0.7921009031462:ℝ):ℂ) * I)‖ ≤ 0.00000014132 := by
  have hl := lg_27
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.170874244848946892 73.170874278150513495 2.2273494 0.00000004131 (-0.6103901696637) 0.7921009031462 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_28 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1502735182099:ℝ):ℂ) + ((0.9886444607263:ℝ):ℂ) * I)‖ ≤ 0.00000016558 := by
  have hl := lg_28
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.978272307315503822 73.978272351717548224 1.4199514 0.00000006557 0.1502735182099 0.9886444607263 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_29 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8015645342503:ℝ):ℂ) + ((0.5979082684092:ℝ):ℂ) * I)‖ ≤ 0.00000015671 := by
  have hl := lg_29
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.757334698445509092 74.757334742847575695 0.640889 0.0000000567 0.8015645342503 0.5979082684092 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p201_30 : ‖exp (-((((((22201:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9937614157245:ℝ):ℂ) + (((-0.111526896385):ℝ):ℂ) * I)‖ ≤ 0.00000013897 := by
  have hl := lg_30
  refine (ecis_approx ((((22201:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.509983047197302973 75.509983091599347375 (-0.1117594) 0.00000003896 0.9937614157245 (-0.111526896385) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_2 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9741413615577):ℝ):ℂ) + (((-0.2259393888002):ℝ):ℂ) * I)‖ ≤ 0.00000013673 := by
  have hl := lg_2
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.4800559776399 15.4800559888064 (-2.9136854) 0.00000003672 (-0.9741413615577) (-0.2259393888002) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_3 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8267823312786:ℝ):ℂ) + ((0.5625219788467:ℝ):ℂ) * I)‖ ≤ 0.00000011948 := by
  have hl := lg_3
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.535308237019526612 24.535308248186048945 0.597433 0.00000001947 0.8267823312786 0.5625219788467 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_4 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8979027441864:ℝ):ℂ) + ((0.4401938913508:ℝ):ℂ) * I)‖ ≤ 0.00000014173 := by
  have hl := lg_4
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.9601119552798 30.9601119776128 0.4558146 0.00000004172 0.8979027441864 0.4401938913508 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_5 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1836895613717):ℝ):ℂ) + ((0.9829843055931:ℝ):ℂ) * I)‖ ≤ 0.00000015631 := by
  have hl := lg_5
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.943576886780029597 35.94357690911305193 1.7555349 0.0000000563 (-0.1836895613717) 0.9829843055931 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_6 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6783069938273):ℝ):ℂ) + (((-0.7347786211537):ℝ):ℂ) * I)‖ ≤ 0.00000012843 := by
  have hl := lg_6
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.015364214659426612 40.015364236992448945 (-2.3162524) 0.00000002842 (-0.6783069938273) (-0.7347786211537) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_7 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8656816872275:ℝ):ℂ) + ((0.5005948625375:ℝ):ℂ) * I)‖ ≤ 0.00000011933 := by
  have hl := lg_7
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.458011347241579526 43.458011369574624192 0.5242858 0.00000001932 0.8656816872275 0.5005948625375 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_8 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7752270630347):ℝ):ℂ) + (((-0.6316826740522):ℝ):ℂ) * I)‖ ≤ 0.00000011735 := by
  have hl := lg_8
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.4401679329197 46.4401679664192 (-2.4578708) 0.00000001734 (-0.7752270630347) (-0.6316826740522) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_9 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3671380466288:ℝ):ℂ) + ((0.9301664661326:ℝ):ℂ) * I)‖ ≤ 0.00000013895 := by
  have hl := lg_9
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.070616474039053224 49.07061649637209789 1.194866 0.00000003894 0.3671380466288 0.9301664661326 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_10 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4010345643953:ℝ):ℂ) + (((-0.9160629225988):ℝ):ℂ) * I)‖ ≤ 0.0000001405 := by
  have hl := lg_10
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.423632864419929597 51.42363289791945193 (-1.1581504) 0.00000004049 0.4010345643953 (-0.9160629225988) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_11 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9894885517323):ℝ):ℂ) + ((0.1446112222117:ℝ):ℂ) * I)‖ ≤ 0.00000015464 := by
  have hl := lg_11
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.552195109989897489 53.552195143489442155 2.9964726 0.00000005463 (-0.9894885517323) 0.1446112222117 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_12 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.494751385261:ℝ):ℂ) + ((0.8690345601772:ℝ):ℂ) * I)‖ ≤ 0.0000001612 := by
  have hl := lg_12
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.495420192299326612 55.495420225798848945 1.0532476 0.00000006119 0.494751385261 0.8690345601772 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_13 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.742269024704:ℝ):ℂ) + (((-0.6701020034032):ℝ):ℂ) * I)‖ ≤ 0.00000015167 := by
  have hl := lg_13
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.2830139827724061 57.283014016271950766 (-0.7343462) 0.00000005166 0.742269024704 (-0.6701020034032) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_14 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7301922402157):ℝ):ℂ) + (((-0.6832417524563):ℝ):ℂ) * I)‖ ≤ 0.00000013975 := by
  have hl := lg_14
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.938067324881479526 58.938067358381024192 (-2.3893996) 0.00000003974 (-0.7301922402157) (-0.6832417524563) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_15 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7048215605366):ℝ):ℂ) + ((0.7093846402187:ℝ):ℂ) * I)‖ ≤ 0.00000014801 := by
  have hl := lg_15
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.478885123799556209 60.478885157299100875 2.3529679 0.000000048 (-0.7048215605366) 0.7093846402187 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_16 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6124587550852:ℝ):ℂ) + ((0.7905025447901:ℝ):ℂ) * I)‖ ≤ 0.00000016125 := by
  have hl := lg_16
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.9202239105596 61.9202239552256 0.9116291 0.00000006124 0.6124587550852 0.7905025447901 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_17 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9037693962372:ℝ):ℂ) + (((-0.4280197173321):ℝ):ℂ) * I)‖ ≤ 0.00000016247 := by
  have hl := lg_17
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.274153589586020522 63.274153634252042855 (-0.4423005) 0.00000006246 0.9037693962372 (-0.4280197173321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_18 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.147483113689):ℝ):ℂ) + (((-0.9890645738151):ℝ):ℂ) * I)‖ ≤ 0.00000012013 := by
  have hl := lg_18
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.550672451678953224 64.55067248517849789 (-1.7188194) 0.00000002012 (-0.147483113689) (-0.9890645738151) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_19 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9769144708):ℝ):ℂ) + (((-0.2136307946801):ℝ):ℂ) * I)‖ ≤ 0.00000016603 := by
  have hl := lg_19
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.758155704308004799 65.758155737807571798 (-2.9263026) 0.00000006602 (-0.9769144708) (-0.2136307946801) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_20 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.597639047849):ℝ):ℂ) + ((0.8017652826571:ℝ):ℂ) * I)‖ ≤ 0.00000013693 := by
  have hl := lg_20
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.903688842059829597 66.90368888672585193 2.2113495 0.00000003692 (-0.597639047849) 0.8017652826571 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_21 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4341347108361:ℝ):ℂ) + ((0.9008479632254:ℝ):ℂ) * I)‖ ≤ 0.0000001388 := by
  have hl := lg_21
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.993319584261106138 67.993319617760673137 1.1217188 0.00000003879 0.4341347108361 0.9008479632254 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_22 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9965750882702:ℝ):ℂ) + ((0.0826927653375:ℝ):ℂ) * I)‖ ≤ 0.00000015334 := by
  have hl := lg_22
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.032251087629797489 69.032251132295842155 0.0827873 0.00000005333 0.9965750882702 0.0826927653375 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_23 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.613782144959:ℝ):ℂ) + (((-0.789475445172):ℝ):ℂ) * I)‖ ≤ 0.00000016683 := by
  have hl := lg_23
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.024992301124210878 70.024992345790277877 (-0.9099539) 0.00000006682 0.613782144959 (-0.789475445172) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_24 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2856086506285):ℝ):ℂ) + (((-0.9583463354574):ℝ):ℂ) * I)‖ ≤ 0.00000013564 := by
  have hl := lg_24
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.975476169939226612 70.975476214605248945 (-1.8604378) 0.00000003563 (-0.2856086506285) (-0.9583463354574) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_25 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9325162513262):ℝ):ℂ) + (((-0.3611280117192):ℝ):ℂ) * I)‖ ≤ 0.00000013927 := by
  have hl := lg_25
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.887153773560059194 71.88715381822610386 (-2.7721154) 0.00000003926 (-0.9325162513262) (-0.3611280117192) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_26 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8744773921264):ℝ):ℂ) + ((0.4850662744083:ℝ):ℂ) * I)‖ ≤ 0.00000012576 := by
  have hl := lg_26
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.7630699604123061 72.763070005078350766 2.6351537 0.00000002575 (-0.8744773921264) 0.4850662744083 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_27 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.219695831093):ℝ):ℂ) + ((0.9755684198452:ℝ):ℂ) * I)‖ ≤ 0.00000015842 := by
  have hl := lg_27
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.605924711058579836 73.605924744558146835 1.792299 0.00000005841 (-0.219695831093) 0.9755684198452 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_28 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5569391620229:ℝ):ℂ) + ((0.8305532913698:ℝ):ℂ) * I)‖ ≤ 0.00000016105 := by
  have hl := lg_28
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.418123302521379526 74.418123347187424192 0.9801004 0.00000006104 0.5569391620229 0.8305532913698 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_29 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9807742837207:ℝ):ℂ) + ((0.1951455979316:ℝ):ℂ) * I)‖ ≤ 0.0000001383 := by
  have hl := lg_29
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.201817747866472436 75.201817792532539435 0.1964059 0.00000003829 0.9807742837207 0.1951455979316 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p333_30 : ‖exp (-((((((22333:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8468738200424:ℝ):ℂ) + (((-0.5317938819945):ℝ):ℂ) * I)‖ ≤ 0.00000015997 := by
  have hl := lg_30
  refine (ecis_approx ((((22333:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.958941101439456209 75.958941146105500875 (-0.5607174) 0.00000005996 0.8468738200424 (-0.5317938819945) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_2 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9907103216751):ℝ):ℂ) + (((-0.1359891838037):ℝ):ℂ) * I)‖ ≤ 0.00000010893 := by
  have hl := lg_2
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.5715514054395 15.571551416672 (-3.0051808) 0.00000000892 (-0.9907103216751) (-0.1359891838037) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_3 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8993935112378:ℝ):ℂ) + ((0.4371399226144:ℝ):ℂ) * I)‖ ≤ 0.00000014162 := by
  have hl := lg_3
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.68032505908940426 24.680325070321926725 0.4524162 0.00000004161 0.8993935112378 0.4371399226144 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_4 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9630138856031:ℝ):ℂ) + ((0.2694517695908:ℝ):ℂ) * I)‖ ≤ 0.00000012503 := by
  have hl := lg_4
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.143102810879 31.143102833344 0.2728237 0.00000002502 0.9630138856031 0.2694517695908 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_5 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0277036818355:ℝ):ℂ) + ((0.9996161793471:ℝ):ℂ) * I)‖ ≤ 0.00000015194 := by
  have hl := lg_5
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.156022691152705185 36.15602271361772765 1.5430891 0.00000005193 0.0277036818355 0.9996161793471 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_6 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8315921336088):ℝ):ℂ) + (((-0.5553868230852):ℝ):ℂ) * I)‖ ≤ 0.00000014393 := by
  have hl := lg_6
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.25187646452890426 40.251876486993926725 (-2.5527646) 0.00000004392 (-0.8315921336088) (-0.5553868230852) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_7 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.964454348882:ℝ):ℂ) + ((0.2642495201938:ℝ):ℂ) * I)‖ ≤ 0.00000015907 := by
  have hl := lg_7
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.71487148684825523 43.71487150931330016 0.2674257 0.00000005906 0.964454348882 0.2642495201938 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_8 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9174252702404):ℝ):ℂ) + (((-0.3979081217884):ℝ):ℂ) * I)‖ ≤ 0.00000013395 := by
  have hl := lg_8
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.7146542163185 46.714654250016 (-2.7323571) 0.00000003394 (-0.9174252702404) (-0.3979081217884) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_9 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6178174547456:ℝ):ℂ) + ((0.786321558023:ℝ):ℂ) * I)‖ ≤ 0.00000013927 := by
  have hl := lg_9
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.36065011817880852 49.36065014064385345 0.9048323 0.00000003926 0.6178174547456 0.786321558023 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_10 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1084906649974:ℝ):ℂ) + (((-0.9940974678613):ℝ):ℂ) * I)‖ ≤ 0.00000016086 := by
  have hl := lg_10
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.727574096592205185 51.72757413028972765 (-1.4620917) 0.00000006085 0.1084906649974 (-0.9940974678613) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_11 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8953222586655):ℝ):ℂ) + ((0.4454189634792:ℝ):ℂ) * I)‖ ≤ 0.00000015499 := by
  have hl := lg_11
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.868717285896343845 53.868717319593888775 2.6799505 0.00000005498 (-0.8953222586655) 0.4454189634792 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_12 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7483403142362:ℝ):ℂ) + ((0.6633149885906:ℝ):ℂ) * I)‖ ≤ 0.00000013906 := by
  have hl := lg_12
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.82342786996840426 55.823427903665926725 0.7252399 0.00000003905 0.7483403142362 0.6633149885906 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_13 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4775611117713:ℝ):ℂ) + (((-0.8785985343283):ℝ):ℂ) * I)‖ ≤ 0.00000016678 := by
  have hl := lg_13
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.6215872978543905 57.62158733155193543 (-1.0729196) 0.00000006677 0.4775611117713 (-0.8785985343283) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_14 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9195598017282):ℝ):ℂ) + (((-0.3929500870382):ℝ):ℂ) * I)‖ ≤ 0.00000016138 := by
  have hl := lg_14
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.28642289228775523 59.28642292598530016 (-2.7377551) 0.00000006137 (-0.9195598017282) (-0.3929500870382) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_15 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4120556276037):ℝ):ℂ) + ((0.911158690765:ℝ):ℂ) * I)‖ ≤ 0.00000012157 := by
  have hl := lg_15
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.836347750242109445 60.836347783939654375 1.9955053 0.00000002156 (-0.4120556276037) 0.911158690765 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_16 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8547914877288:ℝ):ℂ) + ((0.5189715912325:ℝ):ℂ) * I)‖ ≤ 0.00000015005 := by
  have hl := lg_16
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.286205621758 62.286205666688 0.5456474 0.00000005004 0.8547914877288 0.5189715912325 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_17 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6849329186403:ℝ):ℂ) + (((-0.7286061329435):ℝ):ℂ) * I)‖ ≤ 0.00000012401 := by
  have hl := lg_17
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.64813775086418981 63.648137795794212275 (-0.8162847) 0.000000024 0.6849329186403 (-0.7286061329435) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_18 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5051469024005):ℝ):ℂ) + (((-0.863033375362):ℝ):ℂ) * I)‖ ≤ 0.00000014819 := by
  have hl := lg_18
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.93220152361830852 64.93220155731585345 (-2.1003485) 0.00000004818 (-0.5051469024005) (-0.863033375362) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_19 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9850079997035):ℝ):ℂ) + ((0.1725086669128:ℝ):ℂ) * I)‖ ≤ 0.00000012954 := by
  have hl := lg_19
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.146821649455036395 66.14682168315260379 2.9682167 0.00000002953 (-0.9850079997035) 0.1725086669128 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p465_20 : ‖exp (-((((((22465:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2426694151577):ℝ):ℂ) + ((0.9701090428121:ℝ):ℂ) * I)‖ ≤ 0.000000168 := by
  have hl := lg_20
  refine (ecis_approx ((((22465:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.299125502031705185 67.29912554696172765 1.8159129 0.00000006799 (-0.2426694151577) 0.9701090428121 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_2 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9989914254009):ℝ):ℂ) + (((-0.0449013517809):ℝ):ℂ) * I)‖ ≤ 0.00000013019 := by
  have hl := lg_2
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.6630468332391 15.6630468445376 (-3.0966762) 0.00000003018 (-0.9989914254009) (-0.0449013517809) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_3 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.953123714368:ℝ):ℂ) + ((0.3025808736673:ℝ):ℂ) * I)‖ ≤ 0.00000014757 := by
  have hl := lg_3
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.825341881159281908 24.825341892457804505 0.3073993 0.00000004756 0.953123714368 0.3025808736673 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_4 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9959677378128:ℝ):ℂ) + ((0.0897121242423:ℝ):ℂ) * I)‖ ≤ 0.00000015319 := by
  have hl := lg_4
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.3260936664782 31.3260936890752 0.0898329 0.00000005318 0.9959677378128 0.0897121242423 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_5 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2378512643804:ℝ):ℂ) + ((0.9713015886081:ℝ):ℂ) * I)‖ ≤ 0.00000014757 := by
  have hl := lg_5
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.368468495525380773 36.36846851812240337 1.3306433 0.00000004756 0.2378512643804 0.9713015886081 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_6 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9385761278758):ℝ):ℂ) + (((-0.3450722417194):ℝ):ℂ) * I)‖ ≤ 0.00000012869 := by
  have hl := lg_6
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.488388714398381908 40.488388736995404505 (-2.7892769) 0.00000002868 (-0.9385761278758) (-0.3450722417194) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_7 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999441856241:ℝ):ℂ) + ((0.0105653034303:ℝ):ℂ) * I)‖ ≤ 0.00000012382 := by
  have hl := lg_7
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.971731626454930934 43.971731649051976128 0.0105655 0.00000002381 0.9999441856241 0.0105653034303 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_8 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9909350479072):ℝ):ℂ) + (((-0.1343418416271):ℝ):ℂ) * I)‖ ≤ 0.00000015055 := by
  have hl := lg_8
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.9891404997173 46.9891405336128 (-3.0068434) 0.00000005054 (-0.9909350479072) (-0.1343418416271) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_9 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8168895721021:ℝ):ℂ) + ((0.576794094102:ℝ):ℂ) * I)‖ ≤ 0.00000012749 := by
  have hl := lg_9
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.650683762318563816 49.65068378491560901 0.6147987 0.00000002748 0.8168895721021 0.576794094102 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_10 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1939986191296):ℝ):ℂ) + (((-0.9810018021263):ℝ):ℂ) * I)‖ ≤ 0.00000012869 := by
  have hl := lg_10
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.031515328764480773 52.03151536266000337 (-1.7660329) 0.00000002868 (-0.1939986191296) (-0.9810018021263) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_11 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7122033118788):ℝ):ℂ) + ((0.7019732491506:ℝ):ℂ) * I)‖ ≤ 0.0000001311 := by
  have hl := lg_11
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.185239461802790201 54.185239495698335395 2.3634283 0.00000003109 (-0.7122033118788) 0.7019732491506 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_12 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9221352967231:ℝ):ℂ) + ((0.3868675413335:ℝ):ℂ) * I)‖ ≤ 0.00000011699 := by
  have hl := lg_12
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.151435547637481908 56.151435581533004505 0.3972322 0.00000001698 0.9221352967231 0.3868675413335 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_13 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1586304919452:ℝ):ℂ) + (((-0.9873380206521):ℝ):ℂ) * I)‖ ≤ 0.00000015169 := by
  have hl := lg_13
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.9601606129363749 57.960160646831920094 (-1.4114929) 0.00000005168 0.1586304919452 (-0.9873380206521) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_14 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9984612709224):ℝ):ℂ) + (((-0.0554534931851):ℝ):ℂ) * I)‖ ≤ 0.00000012899 := by
  have hl := lg_14
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.634778459694030934 59.634778493589576128 (-3.0861107) 0.00000002898 (-0.9984612709224) (-0.0554534931851) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_15 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0671957024761):ℝ):ℂ) + ((0.9977398145651:ℝ):ℂ) * I)‖ ≤ 0.0000001388 := by
  have hl := lg_15
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.193810376684662681 61.193810410580207875 1.6380427 0.00000003879 (-0.0671957024761) 0.9977398145651 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_16 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9839034873979:ℝ):ℂ) + ((0.1787006644816:ℝ):ℂ) * I)‖ ≤ 0.00000013885 := by
  have hl := lg_16
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.6521873329564 62.6521873781504 0.1796657 0.00000003884 0.9839034873979 0.1787006644816 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_17 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3714102204114:ℝ):ℂ) + (((-0.9284688730237):ℝ):ℂ) * I)‖ ≤ 0.00000015967 := by
  have hl := lg_17
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.022121912142359098 64.022121957336381695 (-1.1902689) 0.00000005966 0.3714102204114 (-0.9284688730237) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_18 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7901668435713):ℝ):ℂ) + (((-0.6128918006262):ℝ):ℂ) * I)‖ ≤ 0.00000015767 := by
  have hl := lg_18
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.313730595557663816 65.31373062945320901 (-2.4818775) 0.00000005766 (-0.7901668435713) (-0.6128918006262) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_19 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8461687411316):ℝ):ℂ) + ((0.5329150602678:ℝ):ℂ) * I)‖ ≤ 0.00000014954 := by
  have hl := lg_19
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.535487594602067991 66.535487628497635782 2.5795508 0.00000004953 (-0.8461687411316) 0.5329150602678 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p597_20 : ‖exp (-((((((22597:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1497546569269:ℝ):ℂ) + ((0.9887231881212:ℝ):ℂ) * I)‖ ≤ 0.00000012824 := by
  have hl := lg_20
  refine (ecis_approx ((((22597:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.694562162003580773 67.69456220719760337 1.4204762 0.00000002823 0.1497546569269 0.9887231881212 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_2 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9969773864067):ℝ):ℂ) + ((0.0776922806766:ℝ):ℂ) * I)‖ ≤ 0.0000001374 := by
  have hl := lg_2
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.7857338841522 15.7857338955392 3.063822 0.00000003739 (-0.9969773864067) 0.0776922806766 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_3 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9936284910281:ℝ):ℂ) + ((0.1127050212597:ℝ):ℂ) * I)‖ ≤ 0.00000013889 := by
  have hl := lg_3
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.019796256207526936 25.01979626759454971 0.112945 0.00000003888 0.9936284910281 0.1127050212597 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_4 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9879278355756:ℝ):ℂ) + (((-0.1549147884967):ℝ):ℂ) * I)‖ ≤ 0.0000001552 := by
  have hl := lg_4
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.5714677683044 31.5714677910784 (-0.1555412) 0.00000005519 0.9879278355756 (-0.1549147884967) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_5 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.501233362834:ℝ):ℂ) + ((0.8653121494479:ℝ):ℂ) * I)‖ ≤ 0.00000013716 := by
  have hl := lg_5
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.653339005934195766 36.65333902870821854 1.0457728 0.00000003715 0.501233362834 0.8653121494479 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_6 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993814459104):ℝ):ℂ) + (((-0.0351671006066):ℝ):ℂ) * I)‖ ≤ 0.00000012007 := by
  have hl := lg_6
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.805530140359726936 40.80553016313374971 (-3.1064183) 0.00000002006 (-0.9993814459104) (-0.0351671006066) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_7 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9447842961118:ℝ):ℂ) + (((-0.3276928955906):ℝ):ℂ) * I)‖ ≤ 0.00000012753 := by
  have hl := lg_7
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.316157722745700628 44.316157745519746176 (-0.3338606) 0.00000002752 0.9447842961118 (-0.3276928955906) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_8 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9729060283296):ℝ):ℂ) + ((0.2312009077726:ℝ):ℂ) * I)‖ ≤ 0.0000001292 := by
  have hl := lg_8
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.3572016524566 47.3572016866176 2.9082808 0.00000002919 (-0.9729060283296) 0.2312009077726 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_9 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9745951787631:ℝ):ℂ) + ((0.2239737429517:ℝ):ℂ) * I)‖ ≤ 0.00000014504 := by
  have hl := lg_9
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.039592512415053872 50.03959253518909942 0.2258899 0.00000004503 0.9745951787631 0.2239737429517 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_10 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5669463144841):ℝ):ℂ) + (((-0.82375474292):ℝ):ℂ) * I)‖ ≤ 0.00000016683 := by
  have hl := lg_10
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.439072890086395766 52.43907292424741854 (-2.1735904) 0.00000006682 (-0.5669463144841) (-0.82375474292) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_11 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3599408312251):ℝ):ℂ) + ((0.932975132581:ℝ):ℂ) * I)‖ ≤ 0.00000013968 := by
  have hl := lg_11
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.609666924950070542 54.60966695911111609 1.9390008 0.00000003967 (-0.3599408312251) 0.932975132581 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_12 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9990929147803:ℝ):ℂ) + (((-0.0425834197296):ℝ):ℂ) * I)‖ ≤ 0.00000014012 := by
  have hl := lg_12
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.591264024511926936 56.59126405867294971 (-0.0425963) 0.00000004011 0.9990929147803 (-0.0425834197296) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_13 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2904456897733):ℝ):ℂ) + (((-0.9568914783247):ℝ):ℂ) * I)‖ ≤ 0.00000011863 := by
  have hl := lg_13
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.4141566490690358 58.414156683230081348 (-1.8654889) 0.00000001862 (-0.2904456897733) (-0.9568914783247) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_14 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9164693699412):ℝ):ℂ) + ((0.4001048535346:ℝ):ℂ) * I)‖ ≤ 0.00000016491 := by
  have hl := lg_14
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.101891606897900628 60.101891641058946176 2.7299614 0.0000000649 (-0.9164693699412) 0.4001048535346 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_15 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4005147257658:ℝ):ℂ) + ((0.9162903221385:ℝ):ℂ) * I)‖ ≤ 0.00000012452 := by
  have hl := lg_15
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.673135262141722702 61.67313529630276825 1.1587178 0.00000002451 0.4005147257658 0.9162903221385 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_16 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9520027860011:ℝ):ℂ) + (((-0.3060893585967):ℝ):ℂ) * I)‖ ≤ 0.0000001352 := by
  have hl := lg_16
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.1429355366088 63.1429355821568 (-0.3110825) 0.00000003519 0.9520027860011 (-0.3060893585967) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
