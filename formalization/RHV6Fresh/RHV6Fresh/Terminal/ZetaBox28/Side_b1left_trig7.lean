/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 7

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

lemma cs_b1left_v21p002_44 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5932274060892):ℝ):ℂ) + ((0.8050349338092:ℝ):ℂ) * I)‖ ≤ 0.0000001291 := by
  have hl := lg_44
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.475550664254430066 79.47555071675947207 2.2058583 0.00000002909 (-0.5932274060892) 0.8050349338092 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_45 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1623650855152):ℝ):ℂ) + ((0.9867307530451:ℝ):ℂ) * I)‖ ≤ 0.000000137 := by
  have hl := lg_45
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.947525588318738074 79.94752563032280108 1.7338834 0.00000003699 (-0.1623650855152) 0.9867307530451 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_46 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2941001809102:ℝ):ℂ) + ((0.9557745987358:ℝ):ℂ) * I)‖ ≤ 0.00000014095 := by
  have hl := lg_46
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.409126581767064732 80.409126634272127738 1.2722824 0.00000004094 0.2941001809102 0.9557745987358 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_47 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6817757398373:ℝ):ℂ) + ((0.73156123501:ℝ):ℂ) * I)‖ ≤ 0.000000163 := by
  have hl := lg_47
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.860799903817729658 80.860799956322813666 0.8206091 0.00000006299 0.6817757398373 0.73156123501 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_48 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9292401461166:ℝ):ℂ) + ((0.3694763197353:ℝ):ℂ) * I)‖ ≤ 0.00000016298 := by
  have hl := lg_48
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.302963603790660328 81.30296365629568133 0.3784454 0.00000006297 0.9292401461166 0.3694763197353 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_49 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.998509741152:ℝ):ℂ) + (((-0.0545737741462):ℝ):ℂ) * I)‖ ≤ 0.00000012777 := by
  have hl := lg_49
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.736009879081865688 81.736009921085949696 (-0.0546009) 0.00000002776 0.998509741152 (-0.0545737741462) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_50 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8875031725824:ℝ):ℂ) + (((-0.4608016044419):ℝ):ℂ) * I)‖ ≤ 0.00000016064 := by
  have hl := lg_50
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.160307132705034836 82.16030718521007684 (-0.4788982) 0.00000006063 0.8875031725824 (-0.4608016044419) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_51 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6256803842763:ℝ):ℂ) + (((-0.7800795194927):ℝ):ℂ) * I)‖ ≤ 0.00000017036 := by
  have hl := lg_51
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.576201911179407196 82.5762019636844492 (-0.8947929) 0.00000007035 0.6256803842763 (-0.7800795194927) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_52 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2649814906968:ℝ):ℂ) + (((-0.9642534986133):ℝ):ℂ) * I)‖ ≤ 0.000000143 := by
  have hl := lg_52
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.9840205503502634 82.984020602855305404 (-1.3026116) 0.00000004299 0.2649814906968 (-0.9642534986133) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_53 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1314836481281):ℝ):ℂ) + (((-0.9913183395229):ℝ):ℂ) * I)‖ ≤ 0.00000015222 := by
  have hl := lg_53
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.384070741124778788 83.384070793629841794 (-1.7026618) 0.00000005221 (-0.1314836481281) (-0.9913183395229) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_54 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.500726330616):ℝ):ℂ) + (((-0.8656056502944):ℝ):ℂ) * I)‖ ≤ 0.00000016924 := by
  have hl := lg_54
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.776642924105380984 83.77664296610944399 (-2.095234) 0.00000006923 (-0.500726330616) (-0.8656056502944) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_55 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7893848258698):ℝ):ℂ) + (((-0.6138986859745):ℝ):ℂ) * I)‖ ≤ 0.00000016439 := by
  have hl := lg_55
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.162011528955447484 84.16201158146051049 (-2.4806026) 0.00000006438 (-0.7893848258698) (-0.6138986859745) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_56 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9603432987941):ℝ):ℂ) + (((-0.2788202794398):ℝ):ℂ) * I)‖ ≤ 0.00000014071 := by
  have hl := lg_56
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.540436181522732844 84.540436234027774848 (-2.8590272) 0.0000000407 (-0.9603432987941) (-0.2788202794398) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_57 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9960277855701):ℝ):ℂ) + ((0.0890429664645:ℝ):ℂ) * I)‖ ≤ 0.00000014673 := by
  have hl := lg_57
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 84.912162705223696534 84.912162747227780542 3.0524316 0.00000004672 (-0.9960277855701) 0.0890429664645 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_58 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8985146882008):ℝ):ℂ) + ((0.438943453047:ℝ):ℂ) * I)‖ ≤ 0.0000001322 := by
  have hl := lg_58
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.277424080199025384 85.27742413270408839 2.6871702 0.00000003219 (-0.8985146882008) 0.438943453047 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_59 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.687002989418):ℝ):ℂ) + ((0.7266545895466:ℝ):ℂ) * I)‖ ≤ 0.00000013092 := by
  have hl := lg_59
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.636441369611043984 85.636441422116127992 2.3281529 0.00000003091 (-0.687002989418) 0.7266545895466 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p002_60 : ‖exp (-((((((21002:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3934428407962):ℝ):ℂ) + ((0.9193490800686:ℝ):ℂ) * I)‖ ≤ 0.00000013204 := by
  have hl := lg_60
  refine (ecis_approx ((((21002:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.989424468491677746 85.98942452099671975 1.9751698 0.00000003203 (-0.3934428407962) 0.9193490800686 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_2 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4338208708794):ℝ):ℂ) + (((-0.9009991409459):ℝ):ℂ) * I)‖ ≤ 0.00000011123 := by
  have hl := lg_2
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.5858961150529 14.5858961255744 (-2.0195255) 0.00000001122 (-0.4338208708794) (-0.9009991409459) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_3 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4294164085552):ℝ):ℂ) + ((0.9031066094651:ℝ):ℂ) * I)‖ ≤ 0.00000014376 := by
  have hl := lg_3
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.118098384972995052 23.118098395494516095 2.0146428 0.00000004375 (-0.4294164085552) 0.9031066094651 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_4 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.623598898365):ℝ):ℂ) + ((0.7817444684447:ℝ):ℂ) * I)‖ ≤ 0.00000011527 := by
  have hl := lg_4
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.1717922301058 29.1717922511488 2.2441343 0.00000001526 (-0.623598898365) 0.7817444684447 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_5 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7711714370814):ℝ):ℂ) + (((-0.6366275320705):ℝ):ℂ) * I)‖ ≤ 0.0000001555 := by
  have hl := lg_5
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.867401980410699987 33.86740200145372103 (-2.4514755) 0.00000005549 (-0.7711714370814) (-0.6366275320705) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_6 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.999988079644:ℝ):ℂ) + (((-0.0048826805988):ℝ):ℂ) * I)‖ ≤ 0.00000014307 := by
  have hl := lg_6
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.703994500025895052 37.703994521068916095 (-0.0048827) 0.00000004306 0.999988079644 (-0.0048826805988) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_7 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9942721182045):ℝ):ℂ) + ((0.1068782227481:ℝ):ℂ) * I)‖ ≤ 0.00000012643 := by
  have hl := lg_7
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.947787255630885146 40.947787276673927232 3.0345099 0.00000002642 (-0.9942721182045) 0.1068782227481 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_8 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9748813116856:ℝ):ℂ) + ((0.222725005615:ℝ):ℂ) * I)‖ ≤ 0.00000012648 := by
  have hl := lg_8
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.7576883451587 43.7576883767232 0.2246088 0.00000002647 0.9748813116856 0.222725005615 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_9 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6312030129954):ℝ):ℂ) + (((-0.7756176612034):ℝ):ℂ) * I)‖ ≤ 0.00000014075 := by
  have hl := lg_9
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.236196769945990104 46.23619679098903219 (-2.2538996) 0.00000004074 (-0.6312030129954) (-0.7756176612034) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_10 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2390505881132):ℝ):ℂ) + ((0.9710071144547:ℝ):ℂ) * I)‖ ≤ 0.00000016199 := by
  have hl := lg_10
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.453298095463599987 48.45329812702812103 1.8121843 0.00000006198 (-0.2390505881132) 0.9710071144547 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_11 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9813510966875:ℝ):ℂ) + (((-0.1922238929745):ℝ):ℂ) * I)‖ ≤ 0.00000014837 := by
  have hl := lg_11
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.458910209085989919 50.458910240650532005 (-0.1934278) 0.00000004836 0.9813510966875 (-0.1922238929745) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_12 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4382149906053):ℝ):ℂ) + (((-0.8988701919658):ℝ):ℂ) * I)‖ ≤ 0.00000014237 := by
  have hl := lg_12
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.289890615078795052 52.289890646643316095 (-2.0244082) 0.00000004236 (-0.4382149906053) (-0.8988701919658) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_13 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8434332200688):ℝ):ℂ) + ((0.5372340302089:ℝ):ℂ) * I)‖ ≤ 0.00000015198 := by
  have hl := lg_13
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.9742293126530131 53.974229344217555186 2.5744384 0.00000005197 (-0.8434332200688) 0.5372340302089 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_14 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5276331833808:ℝ):ℂ) + ((0.8494723207942:ℝ):ℂ) * I)‖ ≤ 0.00000013765 := by
  have hl := lg_14
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.533683370683785146 55.533683402248327232 1.0149844 0.00000003764 0.5276331833808 0.8494723207942 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_15 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.906096243204:ℝ):ℂ) + (((-0.423071622839):ℝ):ℂ) * I)‖ ≤ 0.00000013235 := by
  have hl := lg_15
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.985500365383695039 56.985500396948237125 (-0.4368326) 0.00000003234 0.906096243204 (-0.423071622839) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_16 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2222488209128):ℝ):ℂ) + (((-0.9749899802572):ℝ):ℂ) * I)‖ ≤ 0.0000001377 := by
  have hl := lg_16
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.3435844602116 58.3435845022976 (-1.7949167) 0.00000003769 (-0.2222488209128) (-0.9749899802572) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_17 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.997483958583):ℝ):ℂ) + (((-0.070892537261):ℝ):ℂ) * I)‖ ≤ 0.00000015458 := by
  have hl := lg_17
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.619308377094820662 59.619308419180841705 (-3.0706406) 0.00000005457 (-0.997483958583) (-0.070892537261) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_18 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4250017991573):ℝ):ℂ) + ((0.9051925047796:ℝ):ℂ) * I)‖ ≤ 0.00000014478 := by
  have hl := lg_18
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.822092884998890104 60.82209291656343219 2.0097602 0.00000004477 (-0.4250017991573) 0.9051925047796 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_19 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6432785319906:ℝ):ℂ) + ((0.7656322421894:ℝ):ℂ) * I)‖ ≤ 0.00000014962 := by
  have hl := lg_19
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.959829422189286929 61.959829453753850058 0.8720236 0.00000004961 0.6432785319906 0.7656322421894 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_20 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9785817102983:ℝ):ℂ) + (((-0.2058587774901):ℝ):ℂ) * I)‖ ≤ 0.00000016129 := by
  have hl := lg_20
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.039194210516499987 63.03919425260252103 (-0.2073412) 0.00000006128 0.9785817102983 (-0.2058587774901) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_21 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3304343394225:ℝ):ℂ) + (((-0.9438289820356):ℝ):ℂ) * I)‖ ≤ 0.00000013121 := by
  have hl := lg_21
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.065885640603880198 64.065885672168443327 (-1.2340326) 0.0000000312 0.3304343394225 (-0.9438289820356) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_22 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5989241498423):ℝ):ℂ) + (((-0.8008057584232):ℝ):ℂ) * I)‖ ≤ 0.00000014767 := by
  have hl := lg_22
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.044806324138889919 65.044806366224932005 (-2.2129533) 0.00000004766 (-0.5989241498423) (-0.8008057584232) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_23 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999771573508):ℝ):ℂ) + ((0.006759001827:ℝ):ℂ) * I)‖ ≤ 0.00000012704 := by
  have hl := lg_23
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 65.980204763916928738 65.980204806002991867 3.1348336 0.00000002703 (-0.9999771573508) 0.006759001827 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_24 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6197744562949):ℝ):ℂ) + ((0.784779984015:ℝ):ℂ) * I)‖ ≤ 0.00000014886 := by
  have hl := lg_24
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.875786730131695052 66.875786772217716095 2.2392516 0.00000004885 (-0.6197744562949) 0.784779984015 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_25 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1894106796227:ℝ):ℂ) + ((0.9818979552096:ℝ):ℂ) * I)‖ ≤ 0.00000012395 := by
  have hl := lg_25
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.734803960821399974 67.73480400290744206 1.3802344 0.00000002394 0.1894106796227 0.9818979552096 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_26 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8499463338074:ℝ):ℂ) + ((0.5268692718762:ℝ):ℂ) * I)‖ ≤ 0.00000015128 := by
  have hl := lg_26
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.5601254277059131 68.560125469791955186 0.5549129 0.00000005127 0.8499463338074 0.5268692718762 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_27 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9715143671703:ℝ):ℂ) + (((-0.2369806624636):ℝ):ℂ) * I)‖ ≤ 0.00000012407 := by
  have hl := lg_27
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.354295154918985156 69.354295186483548285 (-0.2392568) 0.00000002406 0.9715143671703 (-0.2369806624636) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_28 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5364755441757:ℝ):ℂ) + (((-0.8439158669568):ℝ):ℂ) * I)‖ ≤ 0.00000014886 := by
  have hl := lg_28
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.119579485736685146 70.119579527822727232 (-1.0045411) 0.00000004885 0.5364755441757 (-0.8439158669568) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_29 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1713221194256):ℝ):ℂ) + (((-0.9852150685991):ℝ):ℂ) * I)‖ ≤ 0.00000015047 := by
  have hl := lg_29
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.858006128525239756 70.858006170611302885 (-1.7429678) 0.00000005046 (-0.1713221194256) (-0.9852150685991) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_30 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7742706300573):ℝ):ℂ) + (((-0.6328546368561):ℝ):ℂ) * I)‖ ≤ 0.00000014356 := by
  have hl := lg_30
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.571396480436595039 71.571396522522637125 (-2.4563581) 0.00000004355 (-0.7742706300573) (-0.6328546368561) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_31 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999886625363):ℝ):ℂ) + ((0.0047617352946:ℝ):ℂ) * I)‖ ≤ 0.00000016407 := by
  have hl := lg_31
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.261392722100773609 72.261392764186836738 3.1368309 0.00000006406 (-0.9999886625363) 0.0047617352946 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_32 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7820489531224):ℝ):ℂ) + ((0.6232170046439:ℝ):ℂ) * I)‖ ≤ 0.00000014173 := by
  have hl := lg_32
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.9294805752645 72.929480627872 2.4687431 0.00000004172 (-0.7820489531224) 0.6232170046439 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_33 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2478096921093):ℝ):ℂ) + ((0.9688087306045:ℝ):ℂ) * I)‖ ≤ 0.00000015001 := by
  have hl := lg_33
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.577008594058984971 73.5770086361450481 1.8212151 0.00000005 (-0.2478096921093) 0.9688087306045 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_34 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3688552509887:ℝ):ℂ) + ((0.9294868497284:ℝ):ℂ) * I)‖ ≤ 0.00000015862 := by
  have hl := lg_34
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.205204492147720662 74.205204544755241705 1.1930192 0.00000005861 0.3688552509887 0.9294868497284 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_35 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8347958777365:ℝ):ℂ) + ((0.5505595721756:ℝ):ℂ) * I)‖ ≤ 0.00000015013 := by
  have hl := lg_35
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.815189236041585133 74.815189278127648262 0.5830344 0.00000005012 0.8347958777365 0.5505595721756 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_36 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999523198369:ℝ):ℂ) + (((-0.0097651447958):ℝ):ℂ) * I)‖ ≤ 0.000000156 := by
  have hl := lg_36
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.407989000051790104 75.40798904213783219 (-0.0097653) 0.00000005599 0.9999523198369 (-0.0097651447958) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_37 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8329814053138:ℝ):ℂ) + (((-0.5533009835537):ℝ):ℂ) * I)‖ ≤ 0.00000016984 := by
  have hl := lg_37
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.984545613892273006 75.984545655978336135 (-0.5863219) 0.00000006983 0.8329814053138 (-0.5533009835537) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_38 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4107663395287:ℝ):ℂ) + (((-0.9117406507939):ℝ):ℂ) * I)‖ ≤ 0.00000014893 := by
  have hl := lg_38
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.545725537242186929 76.545725579328250058 (-1.1475019) 0.00000004892 0.4107663395287 (-0.9117406507939) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_39 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1229954329564):ℝ):ℂ) + (((-0.9924072367085):ℝ):ℂ) * I)‖ ≤ 0.00000015357 := by
  have hl := lg_39
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.092327697626008152 77.092327739712071281 (-1.694104) 0.00000005356 (-0.1229954329564) (-0.9924072367085) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_40 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6100077514624):ℝ):ℂ) + (((-0.7923954461902):ℝ):ℂ) * I)‖ ≤ 0.0000001606 := by
  have hl := lg_40
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.625090325569399987 77.62509037817692103 (-2.2268667) 0.00000006059 (-0.6100077514624) (-0.7923954461902) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_41 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9229506295031):ℝ):ℂ) + (((-0.384918348942):ℝ):ℂ) * I)‖ ≤ 0.00000013878 := by
  have hl := lg_41
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.14469697230857694 78.144697024916119026 (-2.7464733) 0.00000003877 (-0.9229506295031) (-0.384918348942) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_42 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.993738413906):ℝ):ℂ) + ((0.1117316619076:ℝ):ℂ) * I)‖ ≤ 0.00000013769 := by
  have hl := lg_42
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.651781755656780198 78.651781797742843327 3.0296272 0.00000003768 (-0.993738413906) 0.1117316619076 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_43 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8212958132303):ℝ):ℂ) + ((0.5705025741503:ℝ):ℂ) * I)‖ ≤ 0.00000016143 := by
  have hl := lg_43
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.14693401265949254 79.146934054745576712 2.534475 0.00000006142 (-0.8212958132303) 0.5705025741503 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_44 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4616994977676):ℝ):ℂ) + ((0.8870363993413:ℝ):ℂ) * I)‖ ≤ 0.00000015416 := by
  have hl := lg_44
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.630702439191789919 79.630702491799332005 2.0507065 0.00000005415 (-0.4616994977676) 0.8870363993413 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_45 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0070138156981):ℝ):ℂ) + ((0.9999754028921:ℝ):ℂ) * I)‖ ≤ 0.00000014299 := by
  have hl := lg_45
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.103598750356690091 80.10359879244275322 1.5778102 0.00000004298 (-0.0070138156981) 0.9999754028921 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_46 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4399008165149:ℝ):ℂ) + ((0.898046363853:ℝ):ℂ) * I)‖ ≤ 0.00000013826 := by
  have hl := lg_46
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.566100878969828738 80.566100931577391867 1.1153081 0.00000003825 0.4399008165149 0.898046363853 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_47 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7883013292588:ℝ):ℂ) + ((0.6152893744319:ℝ):ℂ) * I)‖ ≤ 0.00000013792 := by
  have hl := lg_47
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.018655955434553147 81.018656008042137319 0.662753 0.00000003791 0.7883013292588 0.6152893744319 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_48 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9759571858171:ℝ):ℂ) + ((0.2179623165869:ℝ):ℂ) * I)‖ ≤ 0.00000014817 := by
  have hl := lg_48
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.461682845184595052 81.461682897792116095 0.2197261 0.00000004816 0.9759571858171 0.2179623165869 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_49 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9771540924367:ℝ):ℂ) + (((-0.2125320673079):ℝ):ℂ) * I)‖ ≤ 0.00000016003 := by
  have hl := lg_49
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.895574511261770292 81.895574553347854464 (-0.2141655) 0.00000006002 0.9771540924367 (-0.2125320673079) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_50 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8025189081549:ℝ):ℂ) + (((-0.5966266856702):ℝ):ℂ) * I)‖ ≤ 0.00000013516 := by
  have hl := lg_50
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.320700075874299974 82.32070012848184206 (-0.6392911) 0.00000003515 0.8025189081549 (-0.5966266856702) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_51 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4923594983768:ℝ):ℂ) + (((-0.8703919372088):ℝ):ℂ) * I)‖ ≤ 0.00000013128 := by
  have hl := lg_51
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.737406762067815714 82.7374068146753578 (-1.0559978) 0.00000003127 0.4923594983768 (-0.8703919372088) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_52 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1059843026194:ℝ):ℂ) + (((-0.9943678029774):ℝ):ℂ) * I)‖ ≤ 0.00000015059 := by
  have hl := lg_52
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.1460215427588131 83.146021595366355186 (-1.4646126) 0.00000005058 0.1059843026194 (-0.9943678029774) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_53 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2904024379818):ℝ):ℂ) + (((-0.9569046054924):ℝ):ℂ) * I)‖ ≤ 0.00000016882 := by
  have hl := lg_53
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.546852709527126942 83.546852762134690071 (-1.8654437) 0.00000006881 (-0.2904024379818) (-0.9569046054924) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_54 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6349825821373):ℝ):ℂ) + (((-0.7725264528591):ℝ):ℂ) * I)‖ ≤ 0.00000012338 := by
  have hl := lg_54
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.940191269971885156 83.940191312057948285 (-2.2587823) 0.00000002337 (-0.6349825821373) (-0.7725264528591) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_55 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8791649104369):ℝ):ℂ) + (((-0.4765176388772):ℝ):ℂ) * I)‖ ≤ 0.00000014878 := by
  have hl := lg_55
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.326312189496689906 84.326312242104253035 (-2.6449032) 0.00000004877 (-0.8791649104369) (-0.4765176388772) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_56 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9931017587411):ℝ):ℂ) + (((-0.1172556878783):ℝ):ℂ) * I)‖ ≤ 0.00000016008 := by
  have hl := lg_56
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.705475600789585146 84.705475653397127232 (-3.0240666) 0.00000006007 (-0.9931017587411) (-0.1172556878783) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_57 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9676819203673):ℝ):ℂ) + ((0.2521739493535:ℝ):ℂ) * I)‖ ≤ 0.00000014875 := by
  have hl := lg_57
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.077927807162281981 85.077927849248366153 2.8866665 0.00000004874 (-0.9676819203673) 0.2521739493535 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_58 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8133548152187):ℝ):ℂ) + ((0.5817679473002:ℝ):ℂ) * I)‖ ≤ 0.00000015695 := by
  have hl := lg_58
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.443902243578139756 85.443902296185702885 2.520692 0.00000005694 (-0.8133548152187) 0.5817679473002 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_59 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5565085669395):ℝ):ℂ) + ((0.8308418711848:ℝ):ℂ) * I)‖ ≤ 0.00000015687 := by
  have hl := lg_59
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.803620404757889656 85.803620457365473828 2.1609739 0.00000005686 (-0.5565085669395) 0.8308418711848 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p043_60 : ‖exp (-((((((21043:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2343067181623):ℝ):ℂ) + ((0.9721627239423:ℝ):ℂ) * I)‖ ≤ 0.0000001476 := by
  have hl := lg_60
  refine (ecis_approx ((((21043:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.157292595489495039 86.157292648097037125 1.8073017 0.00000004759 (-0.2343067181623) 0.9721627239423 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_2 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4524614669745):ℝ):ℂ) + (((-0.8917839541608):ℝ):ℂ) * I)‖ ≤ 0.00000012665 := by
  have hl := lg_2
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.6066905304619 14.6066905409984 (-2.0403199) 0.00000002664 (-0.4524614669745) (-0.8917839541608) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_3 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3994237327963):ℝ):ℂ) + ((0.9167664270008:ℝ):ℂ) * I)‖ ≤ 0.00000013546 := by
  have hl := lg_3
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.151056753625239972 23.151056764161761045 1.9816845 0.00000003545 (-0.3994237327963) 0.9167664270008 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_4 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5905572360118):ℝ):ℂ) + ((0.8069957564837:ℝ):ℂ) * I)‖ ≤ 0.00000014611 := by
  have hl := lg_4
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.2133810609238 29.2133810819968 2.2025455 0.0000000461 (-0.5905572360118) 0.8069957564837 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_5 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8009991210196):ℝ):ℂ) + (((-0.5986655227054):ℝ):ℂ) * I)‖ ≤ 0.00000011814 := by
  have hl := lg_5
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.915685117768126257 33.91568513884114733 (-2.4997586) 0.00000001813 (-0.8009991210196) (-0.5986655227054) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_6 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9982814315418:ℝ):ℂ) + (((-0.0586019064431):ℝ):ℂ) * I)‖ ≤ 0.00000015901 := by
  have hl := lg_6
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.757747284087139972 37.757747305160161045 (-0.0586355) 0.000000059 0.9982814315418 (-0.0586019064431) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_7 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9863426859291):ℝ):ℂ) + ((0.1647061187173:ℝ):ℂ) * I)‖ ≤ 0.00000013092 := by
  have hl := lg_7
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.006164560086947806 41.006164581159989952 2.9761326 0.00000003091 (-0.9863426859291) 0.1647061187173 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_8 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.986870276206:ℝ):ℂ) + ((0.1615148845803:ℝ):ℂ) * I)‖ ≤ 0.00000015889 := by
  have hl := lg_8
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.8200715913857 43.8200716229952 0.1622255 0.00000005888 0.986870276206 0.1615148845803 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_9 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6809214313334):ℝ):ℂ) + (((-0.732356473536):ℝ):ℂ) * I)‖ ≤ 0.00000014302 := by
  have hl := lg_9
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.302113507250479944 46.30211352832352209 (-2.3198164) 0.00000004301 (-0.6809214313334) (-0.732356473536) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_10 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1714590626646):ℝ):ℂ) + ((0.9851912453069:ℝ):ℂ) * I)‖ ≤ 0.00000012242 := by
  have hl := lg_10
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.522375648230026257 48.52237567983954733 1.7431068 0.00000002241 (-0.1714590626646) 0.9851912453069 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_11 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9649969446179:ℝ):ℂ) + (((-0.2622611234593):ℝ):ℂ) * I)‖ ≤ 0.00000014143 := by
  have hl := lg_11
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.530847067246545909 50.530847098856088055 (-0.2653646) 0.00000004142 0.9649969446179 (-0.2622611234593) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_12 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.503944120818):ℝ):ℂ) + (((-0.8637362578279):ℝ):ℂ) * I)‖ ≤ 0.0000001429 := by
  have hl := lg_12
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.364437814549039972 52.364437846158561045 (-2.0989554) 0.00000004289 (-0.503944120818) (-0.8637362578279) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_13 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7996389283914):ℝ):ℂ) + ((0.6004811272238:ℝ):ℂ) * I)‖ ≤ 0.00000016036 := by
  have hl := lg_13
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.0511777933534641 54.051177824963006246 2.49749 0.00000006035 (-0.7996389283914) 0.6004811272238 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_14 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5931643326723:ℝ):ℂ) + ((0.8050814085827:ℝ):ℂ) * I)‖ ≤ 0.00000015756 := by
  have hl := lg_14
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.612855090548847806 55.612855122158389952 0.9358127 0.00000005755 0.5931643326723 0.8050814085827 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_15 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.868774511134:ℝ):ℂ) + (((-0.4952078844323):ℝ):ℂ) * I)‖ ≤ 0.0000001384 := by
  have hl := lg_15
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.066741871393366229 57.066741903002908375 (-0.5180741) 0.00000003839 0.868774511134 (-0.4952078844323) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_16 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3024843904586):ℝ):ℂ) + (((-0.9531543387758):ℝ):ℂ) * I)‖ ≤ 0.00000014278 := by
  have hl := lg_16
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.4267621218476 58.4267621639936 (-1.8780944) 0.00000004277 (-0.3024843904586) (-0.9531543387758) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_17 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999013793645):ℝ):ℂ) + ((0.0140438916084:ℝ):ℂ) * I)‖ ≤ 0.00000014775 := by
  have hl := lg_17
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.704304777385313682 59.704304819531334755 3.1275483 0.00000004774 (-0.9999013793645) 0.0140438916084 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_18 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3450130353823):ℝ):ℂ) + ((0.9385978933569:ℝ):ℂ) * I)‖ ≤ 0.0000001341 := by
  have hl := lg_18
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.908804037712379944 60.90880406932192209 1.923049 0.00000003409 (-0.3450130353823) 0.9385978933569 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_19 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7083132499662:ℝ):ℂ) + ((0.7058982504033:ℝ):ℂ) * I)‖ ≤ 0.00000015137 := by
  have hl := lg_19
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.048162591540885019 62.048162623150448238 0.7836905 0.00000005136 0.7083132499662 0.7058982504033 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_20 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9561563633666:ℝ):ℂ) + (((-0.2928566352221):ℝ):ℂ) * I)‖ ≤ 0.00000014906 := by
  have hl := lg_20
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.129066178691926257 63.12906622083794733 (-0.2972131) 0.00000004905 0.9561563633666 (-0.2928566352221) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_21 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2429715473267:ℝ):ℂ) + (((-0.9700334155016):ℝ):ℂ) * I)‖ ≤ 0.0000001581 := by
  have hl := lg_21
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.157221313712187778 64.157221345321750997 (-1.3253683) 0.00000005809 0.2429715473267 (-0.9700334155016) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_22 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6705041948874):ℝ):ℂ) + (((-0.7419057383651):ℝ):ℂ) * I)‖ ≤ 0.00000016807 := by
  have hl := lg_22
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.137537597708445909 65.137537639854488055 (-2.3056845) 0.00000006806 (-0.6705041948874) (-0.7419057383651) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_23 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9949215792809):ℝ):ℂ) + ((0.100653120204:ℝ):ℂ) * I)‖ ≤ 0.00000015355 := by
  have hl := lg_23
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.074269590363609718 66.074269632509672937 3.0407688 0.00000005354 (-0.9949215792809) 0.100653120204 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_24 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5422508331519):ℝ):ℂ) + ((0.8402166589266:ℝ):ℂ) * I)‖ ≤ 0.00000013398 := by
  have hl := lg_24
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.971128345010939972 66.971128387156961045 2.14391 0.00000003397 (-0.5422508331519) 0.8402166589266 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_25 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2831991906668:ℝ):ℂ) + ((0.9590611129671:ℝ):ℂ) * I)‖ ≤ 0.00000014345 := by
  have hl := lg_25
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.831370235536252514 67.83137027768229466 1.2836681 0.00000004344 0.2831991906668 0.9590611129671 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_26 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8973052807962:ℝ):ℂ) + ((0.4414105040156:ℝ):ℂ) * I)‖ ≤ 0.00000015518 := by
  have hl := lg_26
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.6578683238153641 68.657868365961406246 0.45717 0.00000005517 0.8973052807962 0.4414105040156 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_27 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9433760073918:ℝ):ℂ) + (((-0.3317253512734):ℝ):ℂ) * I)‖ ≤ 0.00000011811 := by
  have hl := lg_27
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.453170260875719916 69.453170292485283135 (-0.3381319) 0.0000000181 0.9433760073918 (-0.3317253512734) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_28 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4495745885271:ℝ):ℂ) + (((-0.8932427941779):ℝ):ℂ) * I)‖ ≤ 0.00000015798 := by
  have hl := lg_28
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.219545621010747806 70.219545663156789952 (-1.1045073) 0.00000005797 0.4495745885271 (-0.8932427941779) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_29 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2698047665657):ℝ):ℂ) + (((-0.9629150471028):ℝ):ℂ) * I)‖ ≤ 0.00000016658 := by
  have hl := lg_29
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.959025003393640516 70.959025045539703735 (-1.8439866) 0.00000006657 (-0.2698047665657) (-0.9629150471028) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_30 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8347054350745):ℝ):ℂ) + (((-0.5506966829318):ℝ):ℂ) * I)‖ ≤ 0.00000016504 := by
  have hl := lg_30
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.673432401855266229 71.673432444001308375 (-2.558394) 0.00000006503 (-0.8347054350745) (-0.5506966829318) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_31 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9941972104614):ℝ):ℂ) + ((0.1075727951135:ℝ):ℂ) * I)‖ ≤ 0.00000014797 := by
  have hl := lg_31
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.364412338204134499 72.364412380350197718 3.0338113 0.00000004796 (-0.9941972104614) 0.1075727951135 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_32 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7131452090818):ℝ):ℂ) + ((0.7010163412772:ℝ):ℂ) * I)‖ ≤ 0.00000013386 := by
  have hl := lg_32
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.0334526523095 73.033452704992 2.364771 0.00000003385 (-0.7131452090818) 0.7010163412772 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_33 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1450103897178):ℝ):ℂ) + ((0.989430132386:ℝ):ℂ) * I)‖ ≤ 0.0000001653 := by
  have hl := lg_33
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.681903820871785881 73.6819038630178491 1.7163198 0.00000006529 (-0.1450103897178) 0.989430132386 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_34 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.464940962534:ℝ):ℂ) + ((0.8853416862195:ℝ):ℂ) * I)‖ ≤ 0.00000017439 := by
  have hl := lg_34
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.310995307847213682 74.310995360529734755 1.0872284 0.00000007438 0.464940962534 0.8853416862195 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_35 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8886634993574:ℝ):ℂ) + ((0.4585599032949:ℝ):ℂ) * I)‖ ≤ 0.00000013386 := by
  have hl := lg_35
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.921849677855074063 74.921849720001137282 0.476374 0.00000003385 0.8886634993574 0.4585599032949 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_36 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9931316448227:ℝ):ℂ) + (((-0.117002290797):ℝ):ℂ) * I)‖ ≤ 0.00000012418 := by
  have hl := lg_36
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.515494568174279944 75.51549461032032209 (-0.1172709) 0.00000002417 0.9931316448227 (-0.117002290797) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_37 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7682781097062:ℝ):ℂ) + (((-0.6401161973784):ℝ):ℂ) * I)‖ ≤ 0.00000013493 := by
  have hl := lg_37
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.092873151240406266 76.092873193386469485 (-0.6946495) 0.00000003492 0.7682781097062 (-0.6401161973784) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_38 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.309024185719:ℝ):ℂ) + (((-0.9510541796558):ℝ):ℂ) * I)‖ ≤ 0.00000016417 := by
  have hl := lg_38
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.654853122002785019 76.654853164148848238 (-1.2566295) 0.00000006416 0.309024185719 (-0.9510541796558) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_39 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2311062621492):ℝ):ℂ) + (((-0.9729285151512):ℝ):ℂ) * I)‖ ≤ 0.00000013919 := by
  have hl := lg_39
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.202234546978704072 77.202234589124767291 (-1.8040109) 0.00000003918 (-0.2311062621492) (-0.9729285151512) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_40 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6937887589842):ℝ):ℂ) + (((-0.7201785597228):ℝ):ℂ) * I)‖ ≤ 0.0000001757 := by
  have hl := lg_40
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.735756709153826257 77.73575676183634733 (-2.337533) 0.00000007569 (-0.6937887589842) (-0.7201785597228) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_41 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9600229442625):ℝ):ℂ) + (((-0.2799213215465):ℝ):ℂ) * I)‖ ≤ 0.0000001519 := by
  have hl := lg_41
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.25610413427071434 78.256104186953256486 (-2.8578805) 0.00000005189 (-0.9600229442625) (-0.2799213215465) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_42 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9749954959697):ℝ):ℂ) + ((0.2222246218203:ℝ):ℂ) * I)‖ ≤ 0.00000014918 := by
  have hl := lg_42
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.763911844174087778 78.763911886320150997 2.9174971 0.00000004917 (-0.9749954959697) 0.2222246218203 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_43 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7518362884401):ℝ):ℂ) + ((0.6593498277472:ℝ):ℂ) * I)‖ ≤ 0.00000016493 := by
  have hl := lg_43
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.25977001609910594 79.259770058245190232 2.421639 0.00000006492 (-0.7518362884401) 0.6593498277472 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_44 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3582422212874):ℝ):ℂ) + ((0.9336286793392:ℝ):ℂ) * I)‖ ≤ 0.00000016518 := by
  have hl := lg_44
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.744228128170345909 79.744228180852888055 1.9371808 0.00000006517 (-0.3582422212874) 0.9336286793392 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_45 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1069809040653:ℝ):ℂ) + ((0.9942610754552:ℝ):ℂ) * I)‖ ≤ 0.00000016833 := by
  have hl := lg_45
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.217798625018606201 80.21779866716466942 1.4636103 0.00000006832 0.1069809040653 0.9942610754552 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_46 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5399245992886:ℝ):ℂ) + ((0.8417133877295:ℝ):ℂ) * I)‖ ≤ 0.00000017252 := by
  have hl := lg_46
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.680960120825509718 80.680960173508072937 1.0004488 0.00000007251 0.5399245992886 0.8417133877295 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_47 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8539594149973:ℝ):ℂ) + ((0.5203396174975:ℝ):ℂ) * I)‖ ≤ 0.00000014281 := by
  have hl := lg_47
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.134160383446863017 81.134160436129447309 0.5472486 0.0000000428 0.8539594149973 0.5203396174975 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_48 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9946393418919:ℝ):ℂ) + ((0.1034049300604:ℝ):ℂ) * I)‖ ≤ 0.00000013484 := by
  have hl := lg_48
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.577818875472839972 81.577818928155361045 0.1035901 0.00000003483 0.9946393418919 0.1034049300604 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_49 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9457437911279:ℝ):ℂ) + (((-0.3249133446675):ℝ):ℂ) * I)‖ ≤ 0.000000169 := by
  have hl := lg_49
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.012329120173895612 82.012329162319979904 (-0.3309201) 0.00000006899 0.9457437911279 (-0.3249133446675) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p073_50 : ‖exp (-((((((21073:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.727138590351:ℝ):ℂ) + (((-0.68649069216):ℝ):ℂ) * I)‖ ≤ 0.00000012735 := by
  have hl := lg_50
  refine (ecis_approx ((((21073:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.438060765998152514 82.43806081868069466 (-0.7566518) 0.00000002734 0.727138590351 (-0.68649069216) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_2 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4709064225816):ℝ):ℂ) + (((-0.8821831675827):ℝ):ℂ) * I)‖ ≤ 0.00000014208 := by
  have hl := lg_2
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.6274849458709 14.6274849564224 (-2.0611143) 0.00000004207 (-0.4709064225816) (-0.8821831675827) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_3 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3689971295219):ℝ):ℂ) + ((0.9294305344682:ℝ):ℂ) * I)‖ ≤ 0.00000010646 := by
  have hl := lg_3
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.184015122277484892 23.184015132829005995 1.9487261 0.00000000645 (-0.3689971295219) 0.9294305344682 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_4 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5564941932919):ℝ):ℂ) + ((0.8308514986587:ℝ):ℂ) * I)‖ ≤ 0.00000014417 := by
  have hl := lg_4
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.2549698917418 29.2549699128448 2.1609566 0.00000004416 (-0.5564941932919) 0.8308514986587 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_5 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8289598322936):ℝ):ℂ) + (((-0.5593081408149):ℝ):ℂ) * I)‖ ≤ 0.00000014035 := by
  have hl := lg_5
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.963968255125552527 33.96396827622857363 (-2.5480417) 0.00000004034 (-0.8289598322936) (-0.5593081408149) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_6 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9936910911553:ℝ):ℂ) + (((-0.1121517514738):ℝ):ℂ) * I)‖ ≤ 0.00000014619 := by
  have hl := lg_6
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.811500068148384892 37.811500089251405995 (-0.1123882) 0.00000004618 0.9936910911553 (-0.1121517514738) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_7 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9750528418662):ℝ):ℂ) + ((0.2219728705783:ℝ):ℂ) * I)‖ ≤ 0.0000001354 := by
  have hl := lg_7
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.064541864543010466 41.064541885646052672 2.9177553 0.00000003539 (-0.9750528418662) 0.2219728705783 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_8 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9950198966352:ℝ):ℂ) + ((0.0996765032492:ℝ):ℂ) * I)‖ ≤ 0.00000011903 := by
  have hl := lg_8
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.8824548376127 43.8824548692672 0.0998423 0.00000001902 0.9950198966352 0.0996765032492 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_9 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7276822318803):ℝ):ℂ) + (((-0.6859144038266):ℝ):ℂ) * I)‖ ≤ 0.00000011542 := by
  have hl := lg_9
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.368030244554969784 46.36803026565801199 (-2.3857331) 0.00000001541 (-0.7276822318803) (-0.6859144038266) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_10 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1030496116461):ℝ):ℂ) + ((0.9946762174392:ℝ):ℂ) * I)‖ ≤ 0.00000015646 := by
  have hl := lg_10
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.591453200996452527 48.59145323265097363 1.6740292 0.00000005645 (-0.1030496116461) 0.9946762174392 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_11 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9436511468327:ℝ):ℂ) + (((-0.330941857554):ℝ):ℂ) * I)‖ ≤ 0.00000013204 := by
  have hl := lg_11
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.602783925407101899 50.602783957061644105 (-0.3373015) 0.00000003203 0.9436511468327 (-0.330941857554) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_12 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5668739866325):ℝ):ℂ) + (((-0.8238045176313):ℝ):ℂ) * I)‖ ≤ 0.00000014343 := by
  have hl := lg_12
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.438985014019284892 52.438985045673805995 (-2.1735026) 0.00000004342 (-0.5668739866325) (-0.8238045176313) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_13 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7511121993538):ℝ):ℂ) + ((0.6601745708128:ℝ):ℂ) * I)‖ ≤ 0.00000014111 := by
  have hl := lg_13
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.1281262740539151 54.128126305708457306 2.4205415 0.0000000411 (-0.7511121993538) 0.6601745708128 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_14 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6549794514269:ℝ):ℂ) + ((0.7556466887432:ℝ):ℂ) * I)‖ ≤ 0.00000015422 := by
  have hl := lg_14
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.692026810413910466 55.692026842068452672 0.8566409 0.00000005421 0.6549794514269 0.7556466887432 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_15 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8257218628933:ℝ):ℂ) + (((-0.5640774815041):ℝ):ℂ) * I)‖ ≤ 0.00000014446 := by
  have hl := lg_15
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.147983377403037419 57.147983409057579625 (-0.5993156) 0.00000004445 0.8257218628933 (-0.5640774815041) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_16 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3806283265519):ℝ):ℂ) + (((-0.9247281097833):ℝ):ℂ) * I)‖ ≤ 0.00000016109 := by
  have hl := lg_16
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.5099397834836 58.5099398256896 (-1.961272) 0.00000006108 (-0.3806283265519) (-0.9247281097833) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_17 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9950994721139):ℝ):ℂ) + ((0.0988789164638:ℝ):ℂ) * I)‖ ≤ 0.0000001481 := by
  have hl := lg_17
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.789301177675806702 59.789301219881827805 3.0425519 0.00000004809 (-0.9950994721139) 0.0988789164638 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_18 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2624318979538):ℝ):ℂ) + ((0.9649505163142:ℝ):ℂ) * I)‖ ≤ 0.0000001503 := by
  have hl := lg_18
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.995515190425869784 60.99551522208041199 1.8363379 0.00000005029 (-0.2624318979538) 0.9649505163142 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_19 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7678248430533:ℝ):ℂ) + ((0.6406598242361:ℝ):ℂ) * I)‖ ≤ 0.00000012077 := by
  have hl := lg_19
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.136495760892483109 62.136495792547046418 0.6953573 0.00000002076 0.7678248430533 0.6406598242361 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_20 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9260133401914:ℝ):ℂ) + (((-0.3774907863611):ℝ):ℂ) * I)‖ ≤ 0.00000012494 := by
  have hl := lg_20
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.218938146867352527 63.21893818907337363 (-0.3870851) 0.00000002493 0.9260133401914 (-0.3774907863611) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_21 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.153483343042:ℝ):ℂ) + (((-0.9881512350893):ℝ):ℂ) * I)‖ ≤ 0.00000014669 := by
  have hl := lg_21
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.248556986820495358 64.248557018475058667 (-1.4167039) 0.00000004668 0.153483343042 (-0.9881512350893) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_22 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7363227218988):ℝ):ℂ) + (((-0.676630511568):ℝ):ℂ) * I)‖ ≤ 0.0000001417 := by
  have hl := lg_22
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.230268871278001899 65.230268913484044105 (-2.3984158) 0.00000004169 (-0.7363227218988) (-0.676630511568) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_23 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9810692191738):ℝ):ℂ) + ((0.1936573955687:ℝ):ℂ) * I)‖ ≤ 0.00000016218 := by
  have hl := lg_23
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.168334416810290698 66.168334459016354007 2.9467039 0.00000006217 (-0.9810692191738) 0.1936573955687 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_24 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4598018713645):ℝ):ℂ) + ((0.8880215307552:ℝ):ℂ) * I)‖ ≤ 0.00000012314 := by
  have hl := lg_24
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.066469959890184892 67.066470002096205995 2.0485684 0.00000002313 (-0.4598018713645) 0.8880215307552 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_25 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3743489065456:ℝ):ℂ) + ((0.9272879251711:ℝ):ℂ) * I)‖ ≤ 0.00000016874 := by
  have hl := lg_25
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.927936510251105054 67.92793655245714726 1.1871018 0.00000006873 0.3743489065456 0.9272879251711 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_26 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9360984879877:ℝ):ℂ) + ((0.3517380002034:ℝ):ℂ) * I)‖ ≤ 0.00000015907 := by
  have hl := lg_26
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.7556112199248151 68.755611262130857306 0.3594271 0.00000005906 0.9360984879877 0.3517380002034 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_27 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9060224457337:ℝ):ℂ) + (((-0.4232296395891):ℝ):ℂ) * I)‖ ≤ 0.00000011953 := by
  have hl := lg_27
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.552045366832454676 69.552045398487017985 (-0.437007) 0.00000001952 0.9060224457337 (-0.4232296395891) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_28 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3581847591151:ℝ):ℂ) + (((-0.933650726095):ℝ):ℂ) * I)‖ ≤ 0.00000012271 := by
  have hl := lg_28
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.319511756284810466 70.319511798490852672 (-1.2044734) 0.0000000227 0.3581847591151 (-0.933650726095) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_29 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3655365442679):ℝ):ℂ) + (((-0.9307969890379):ℝ):ℂ) * I)‖ ≤ 0.00000014151 := by
  have hl := lg_29
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.060043878262041276 71.060043920468104585 (-1.9450055) 0.0000000415 (-0.3655365442679) (-0.9307969890379) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_30 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8864574341519):ℝ):ℂ) + (((-0.4628101309766):ℝ):ℂ) * I)‖ ≤ 0.00000015572 := by
  have hl := lg_30
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.775468323273937419 71.775468365479979625 (-2.66043) 0.00000005571 (-0.8864574341519) (-0.4628101309766) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_31 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9778636341944):ℝ):ℂ) + ((0.2092431901134:ℝ):ℂ) * I)‖ ≤ 0.00000013186 := by
  have hl := lg_31
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.467431954307495389 72.467431996513558698 2.9307917 0.00000003185 (-0.9778636341944) 0.2092431901134 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_32 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6365391667926):ℝ):ℂ) + ((0.7712443770451:ℝ):ℂ) * I)‖ ≤ 0.00000015682 := by
  have hl := lg_32
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.1374247293545 73.137424782112 2.2607989 0.00000005681 (-0.6365391667926) 0.7712443770451 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_33 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0406170969065):ℝ):ℂ) + ((0.9991747852296:ℝ):ℂ) * I)‖ ≤ 0.00000013849 := by
  have hl := lg_33
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.786799047684586791 73.7867990898906501 1.6114246 0.00000003848 (-0.0406170969065) 0.9991747852296 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_34 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.55582813169:ℝ):ℂ) + ((0.8312972320548:ℝ):ℂ) * I)‖ ≤ 0.00000016262 := by
  have hl := lg_34
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.416786123546706702 74.416786176304227805 0.9814375 0.00000006261 0.55582813169 0.8312972320548 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_35 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9324309101621:ℝ):ℂ) + ((0.361348305343:ℝ):ℂ) * I)‖ ≤ 0.0000001665 := by
  have hl := lg_35
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.028510119668562993 75.028510161874626302 0.3697135 0.00000006649 0.9324309101621 0.361348305343 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_36 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9748439469939:ℝ):ℂ) + (((-0.2228884900783):ℝ):ℂ) * I)‖ ≤ 0.00000014987 := by
  have hl := lg_36
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.623000136296769784 75.62300017850281199 (-0.2247765) 0.00000004986 0.9748439469939 (-0.2228884900783) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_37 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6945680561296:ℝ):ℂ) + (((-0.7194270049174):ℝ):ℂ) * I)‖ ≤ 0.00000014465 := by
  have hl := lg_37
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.201200688588539526 76.201200730794602835 (-0.802977) 0.00000004464 0.6945680561296 (-0.7194270049174) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_38 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2036056630779:ℝ):ℂ) + (((-0.9790529781184):ℝ):ℂ) * I)‖ ≤ 0.00000016283 := by
  have hl := lg_38
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.763980706763383109 76.763980748969446418 (-1.365757) 0.00000006282 0.2036056630779 (-0.9790529781184) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_39 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3364281519383):ℝ):ℂ) + (((-0.941709136932):ℝ):ℂ) * I)‖ ≤ 0.0000001524 := by
  have hl := lg_39
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.312141396331399992 77.312141438537463301 (-1.9139177) 0.00000005239 (-0.3364281519383) (-0.941709136932) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_40 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7690816469318):ℝ):ℂ) + (((-0.6391505458918):ℝ):ℂ) * I)‖ ≤ 0.00000015936 := by
  have hl := lg_40
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.846423092738252527 77.84642314549577363 (-2.4481994) 0.00000005935 (-0.7690816469318) (-0.6391505458918) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_41 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9851921743823):ℝ):ℂ) + (((-0.1714537231279):ℝ):ℂ) * I)‖ ≤ 0.00000016285 := by
  have hl := lg_41
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.36751129623285174 78.367511348990393946 (-2.9692876) 0.00000006284 (-0.9851921743823) (-0.1714537231279) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_42 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9440066431957):ℝ):ℂ) + ((0.3299264424291:ℝ):ℂ) * I)‖ ≤ 0.00000016066 := by
  have hl := lg_42
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.876041932691395358 78.876041974897458667 2.805367 0.00000006065 (-0.9440066431957) 0.3299264424291 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_43 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6728145638442):ℝ):ℂ) + ((0.7398111668929:ℝ):ℂ) * I)‖ ≤ 0.00000016843 := by
  have hl := lg_43
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.37260601953871934 79.372606061744803752 2.308803 0.00000006842 (-0.6728145638442) 0.7398111668929 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_44 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2501728453869):ℝ):ℂ) + ((0.9682011916073:ℝ):ℂ) * I)‖ ≤ 0.0000001762 := by
  have hl := lg_44
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.857753817148901899 79.857753869906444105 1.8236551 0.00000007619 (-0.2501728453869) 0.9682011916073 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_45 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2195818379256:ℝ):ℂ) + ((0.9755940838552:ℝ):ℂ) * I)‖ ≤ 0.00000014857 := by
  have hl := lg_45
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.331998499680522311 80.33199854188658562 1.3494105 0.00000004856 0.2195818379256 0.9755940838552 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_46 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6328330911638:ℝ):ℂ) + ((0.7742882400812:ℝ):ℂ) * I)‖ ≤ 0.00000013067 := by
  have hl := lg_46
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.795819362681190698 80.795819415438754007 0.8855896 0.00000003066 0.6328330911638 0.7742882400812 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_47 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9082372613472:ℝ):ℂ) + ((0.4184555855769:ℝ):ℂ) * I)‖ ≤ 0.0000001709 := by
  have hl := lg_47
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.249664811459172887 81.249664864216757299 0.4317442 0.00000007089 0.9082372613472 0.4184555855769 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_48 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999213012289:ℝ):ℂ) + (((-0.0125455708826):ℝ):ℂ) * I)‖ ≤ 0.0000001652 := by
  have hl := lg_48
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.693954905761084892 81.693954958518605995 (-0.0125459) 0.00000006519 0.9999213012289 (-0.0125455708826) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_49 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9014560491439:ℝ):ℂ) + (((-0.4328706405635):ℝ):ℂ) * I)‖ ≤ 0.00000016426 := by
  have hl := lg_49
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.129083729086020932 82.129083771292105344 (-0.4476748) 0.00000006425 0.9014560491439 (-0.4328706405635) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p103_50 : ‖exp (-((((((21103:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6417544947126:ℝ):ℂ) + (((-0.7669101437041):ℝ):ℂ) * I)‖ ≤ 0.00000013723 := by
  have hl := lg_50
  refine (ecis_approx ((((21103:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.555421456122005054 82.55542150887954726 (-0.8740125) 0.00000003722 0.6417544947126 (-0.7669101437041) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_2 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.489147849479):ℝ):ℂ) + (((-0.8722008835952):ℝ):ℂ) * I)‖ ≤ 0.00000015309 := by
  have hl := lg_2
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.6482793612799 14.6482793718464 (-2.0819088) 0.00000005308 (-0.489147849479) (-0.8722008835952) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_3 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3381697371354):ℝ):ℂ) + ((0.9410851337066:ℝ):ℂ) * I)‖ ≤ 0.0000001378 := by
  have hl := lg_3
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.216973490929729812 23.216973501496250945 1.9157677 0.00000003779 (-0.3381697371354) 0.9410851337066 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_4 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5214688419007):ℝ):ℂ) + ((0.8532703246449:ℝ):ℂ) * I)‖ ≤ 0.00000011335 := by
  have hl := lg_4
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.2965587225598 29.2965587436928 2.1193678 0.00000001334 (-0.5214688419007) 0.8532703246449 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_5 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8549884518053):ℝ):ℂ) + (((-0.5186470352779):ℝ):ℂ) * I)‖ ≤ 0.00000014343 := by
  have hl := lg_5
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.012251392482978797 34.01225141361599993 (-2.5963249) 0.00000004342 (-0.8549884518053) (-0.5186470352779) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_6 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9862303013778:ℝ):ℂ) + (((-0.1653777271712):ℝ):ℂ) * I)‖ ≤ 0.00000013028 := by
  have hl := lg_6
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.865252852209629812 37.865252873342650945 (-0.166141) 0.00000003027 0.9862303013778 (-0.1653777271712) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_7 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9604410498558):ℝ):ℂ) + ((0.2784833738614:ℝ):ℂ) * I)‖ ≤ 0.00000013989 := by
  have hl := lg_7
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.122919168999073126 41.122919190132115392 2.859378 0.00000003988 (-0.9604410498558) 0.2784833738614 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_8 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9992984899483:ℝ):ℂ) + ((0.0374503402786:ℝ):ℂ) * I)‖ ≤ 0.0000001653 := by
  have hl := lg_8
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.9448380838397 43.9448381155392 0.0374591 0.00000006529 0.9992984899483 0.0374503402786 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_9 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7712823895454):ℝ):ℂ) + (((-0.6364931072192):ℝ):ℂ) * I)‖ ≤ 0.00000015275 := by
  have hl := lg_9
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.433946981859459624 46.43394700299250189 (-2.4516498) 0.00000005274 (-0.7712823895454) (-0.6364931072192) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_10 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0341487327091):ℝ):ℂ) + ((0.9994167619437:ℝ):ℂ) * I)‖ ≤ 0.00000012804 := by
  have hl := lg_10
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.660530753762878797 48.66053078546239993 1.6049517 0.00000002803 (-0.0341487327091) 0.9994167619437 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_11 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9174241774616:ℝ):ℂ) + (((-0.3979106414873):ℝ):ℂ) * I)‖ ≤ 0.00000015785 := by
  have hl := lg_11
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.674720783567657889 50.674720815267200155 (-0.4092383) 0.00000005784 0.9174241774616 (-0.3979106414873) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_12 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.626655030775):ℝ):ℂ) + (((-0.7792967806876):ℝ):ℂ) * I)‖ ≤ 0.00000014396 := by
  have hl := lg_12
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.513532213489529812 52.513532245189050945 (-2.2480498) 0.00000004395 (-0.626655030775) (-0.7792967806876) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_13 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6981402751726):ℝ):ℂ) + ((0.7159610018419:ℝ):ℂ) * I)‖ ≤ 0.00000012185 := by
  have hl := lg_13
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.2050747547543661 54.205074786453908366 2.343593 0.00000002184 (-0.6981402751726) 0.7159610018419 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_14 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7126911189853:ℝ):ℂ) + ((0.7014779889059:ℝ):ℂ) * I)‖ ≤ 0.00000013435 := by
  have hl := lg_14
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.771198530278973126 55.771198561978515392 0.7774692 0.00000003434 0.7126911189853 0.7014779889059 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_15 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7772222975115:ℝ):ℂ) + (((-0.6292261121814):ℝ):ℂ) * I)‖ ≤ 0.00000015051 := by
  have hl := lg_15
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.229224883412708609 57.229224915112250875 (-0.6805571) 0.0000000505 0.7772222975115 (-0.6292261121814) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_16 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4561404874639):ℝ):ℂ) + (((-0.8899077793184):ℝ):ℂ) * I)‖ ≤ 0.00000012278 := by
  have hl := lg_16
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.5931174451196 58.5931174873856 (-2.0444497) 0.00000002277 (-0.4561404874639) (-0.8899077793184) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_17 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9831129070913):ℝ):ℂ) + ((0.1830000315983:ℝ):ℂ) * I)‖ ≤ 0.00000014845 := by
  have hl := lg_17
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.874297577966299722 59.874297620232320855 2.9575555 0.00000004844 (-0.9831129070913) 0.1830000315983 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_18 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1778787212846):ℝ):ℂ) + ((0.9840524175639:ℝ):ℂ) * I)‖ ≤ 0.00000012867 := by
  have hl := lg_18
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.082226343139359624 61.08222637483890189 1.7496267 0.00000002866 (-0.1778787212846) 0.9840524175639 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_19 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8213491822128:ℝ):ℂ) + ((0.5704257365147:ℝ):ℂ) * I)‖ ≤ 0.00000014157 := by
  have hl := lg_19
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.224828930244081199 62.224828961943644598 0.6070241 0.00000004156 0.8213491822128 0.5704257365147 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_20 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8883959620177:ℝ):ℂ) + (((-0.4590780049956):ℝ):ℂ) * I)‖ ≤ 0.00000015677 := by
  have hl := lg_20
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.308810115042778797 63.30881015730879993 (-0.4769571) 0.00000005676 0.8883959620177 (-0.4590780049956) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_21 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0627155413198:ℝ):ℂ) + (((-0.9980314428298):ℝ):ℂ) * I)‖ ≤ 0.00000011985 := by
  have hl := lg_21
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.339892659928802938 64.339892691628366337 (-1.5080396) 0.00000001984 0.0627155413198 (-0.9980314428298) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_22 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7958140765543):ℝ):ℂ) + (((-0.6055410436216):ℝ):ℂ) * I)‖ ≤ 0.00000012696 := by
  have hl := lg_22
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.323000144847557889 65.323000187113600155 (-2.4911471) 0.00000002695 (-0.7958140765543) (-0.6055410436216) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_23 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9585425843908):ℝ):ℂ) + ((0.284949317741:ℝ):ℂ) * I)‖ ≤ 0.00000013573 := by
  have hl := lg_23
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.262399243256971678 66.262399285523035077 2.8526391 0.00000003572 (-0.9585425843908) 0.284949317741 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_24 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.373176466154):ℝ):ℂ) + ((0.9277603812979:ℝ):ℂ) * I)‖ ≤ 0.00000013807 := by
  have hl := lg_24
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.161811574769429812 67.161811617035450945 1.9532268 0.00000003806 (-0.373176466154) 0.9277603812979 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_25 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4620104231866:ℝ):ℂ) + ((0.886874494428:ℝ):ℂ) * I)‖ ≤ 0.00000014827 := by
  have hl := lg_25
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.024502784965957594 68.02450282723199986 1.0905356 0.00000004826 0.4620104231866 0.886874494428 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_26 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9659556326771:ℝ):ℂ) + ((0.2587077805157:ℝ):ℂ) * I)‖ ≤ 0.00000016296 := by
  have hl := lg_26
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.8533541160342661 68.853354158300308366 0.2616842 0.00000006295 0.9659556326771 0.2587077805157 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_27 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8598185638645:ℝ):ℂ) + (((-0.5105996839344):ℝ):ℂ) * I)‖ ≤ 0.00000012553 := by
  have hl := lg_27
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.650920472789189436 69.650920504488752835 (-0.5358821) 0.00000002552 0.8598185638645 (-0.5105996839344) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_28 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2632184900278:ℝ):ℂ) + (((-0.9647362471201):ℝ):ℂ) * I)‖ ≤ 0.00000015486 := by
  have hl := lg_28
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.419477891558873126 70.419477933824915392 (-1.3044395) 0.00000005485 0.2632184900278 (-0.9647362471201) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_29 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4575412591237):ℝ):ℂ) + (((-0.8891883918466):ℝ):ℂ) * I)‖ ≤ 0.00000012586 := by
  have hl := lg_29
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.161062753130442036 71.161062795396505435 (-2.0460244) 0.00000002585 (-0.4575412591237) (-0.8891883918466) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_30 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9289881863712):ℝ):ℂ) + (((-0.3701093749488):ℝ):ℂ) * I)‖ ≤ 0.0000001343 := by
  have hl := lg_30
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.877504244692608609 71.877504286958650875 (-2.7624659) 0.00000003429 (-0.9289881863712) (-0.3701093749488) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_31 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9511611293569):ℝ):ℂ) + ((0.3086948425129:ℝ):ℂ) * I)‖ ≤ 0.00000012654 := by
  have hl := lg_31
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.570451570410856279 72.570451612676919678 2.8277721 0.00000002653 (-0.9511611293569) 0.3086948425129 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_32 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5530582902739):ℝ):ℂ) + ((0.8331425613605:ℝ):ℂ) * I)‖ ≤ 0.00000017309 := by
  have hl := lg_32
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.2413968063995 73.241396859232 2.1568269 0.00000007308 (-0.5530582902739) 0.8331425613605 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_33 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0642226963141:ℝ):ℂ) + ((0.9979355917483:ℝ):ℂ) * I)‖ ≤ 0.00000013062 := by
  have hl := lg_33
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.891694274497387701 73.8916943167634511 1.5065294 0.00000003061 0.0642226963141 0.9979355917483 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_34 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6405003537759:ℝ):ℂ) + ((0.7679578743739:ℝ):ℂ) * I)‖ ≤ 0.00000014692 := by
  have hl := lg_34
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.522576939246199722 74.522576992078720855 0.8756467 0.00000004691 0.6405003537759 0.7679578743739 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_35 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9656005826612:ℝ):ℂ) + ((0.2600298343737:ℝ):ℂ) * I)‖ ≤ 0.00000012469 := by
  have hl := lg_35
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.135170561482051923 75.135170603748115322 0.2630531 0.00000002468 0.9656005826612 0.2600298343737 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_36 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9453004147114:ℝ):ℂ) + (((-0.3262010514185):ℝ):ℂ) * I)‖ ≤ 0.00000016055 := by
  have hl := lg_36
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.730505704419259624 75.73050574668530189 (-0.332282) 0.00000006054 0.9453004147114 (-0.3262010514185) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_37 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6127152409104:ℝ):ℂ) + (((-0.7903037603075):ℝ):ℂ) * I)‖ ≤ 0.00000016023 := by
  have hl := lg_37
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.309528225936672786 76.309528268202736185 (-0.9113046) 0.00000006022 0.6127152409104 (-0.7903037603075) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_38 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.095764744805:ℝ):ℂ) + (((-0.9954039951961):ℝ):ℂ) * I)‖ ≤ 0.00000014765 := by
  have hl := lg_38
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.873108291523981199 76.873108333790044598 (-1.4748846) 0.00000004764 0.095764744805 (-0.9954039951961) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_39 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4376903353654):ℝ):ℂ) + (((-0.8991257811472):ℝ):ℂ) * I)‖ ≤ 0.00000014049 := by
  have hl := lg_39
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.422048245684095912 77.422048287950159311 (-2.0238246) 0.00000004048 (-0.4376903353654) (-0.8991257811472) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_40 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8349651608592):ℝ):ℂ) + (((-0.5503028076308):ℝ):ℂ) * I)‖ ≤ 0.00000014302 := by
  have hl := lg_40
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.957089476322678797 77.95708952915519993 (-2.5588658) 0.00000004301 (-0.8349651608592) (-0.5503028076308) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_41 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9981462984385):ℝ):ℂ) + (((-0.0608602198741):ℝ):ℂ) * I)‖ ≤ 0.00000012798 := by
  have hl := lg_41
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.47891845819498914 78.478918511027531406 (-3.0806948) 0.00000002797 (-0.9981462984385) (-0.0608602198741) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_42 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9011611186622):ℝ):ℂ) + ((0.4334842997085:ℝ):ℂ) * I)‖ ≤ 0.00000017016 := by
  have hl := lg_42
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.988172021208702938 78.988172063474766337 2.693237 0.00000007015 (-0.9011611186622) 0.4334842997085 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_43 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5852355930058):ℝ):ℂ) + ((0.8108633057848:ℝ):ℂ) * I)‖ ≤ 0.00000017037 := by
  have hl := lg_43
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.48544202297833274 79.485442065244417272 2.1959669 0.00000007036 (-0.5852355930058) 0.8108633057848 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_44 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1388827811098):ℝ):ℂ) + ((0.9903088271396:ℝ):ℂ) * I)‖ ≤ 0.00000016564 := by
  have hl := lg_44
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.971279506127457889 79.971279558960000155 1.7101295 0.00000006563 (-0.1388827811098) 0.9903088271396 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_45 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3293222798696:ℝ):ℂ) + ((0.9442175787293:ℝ):ℂ) * I)‖ ≤ 0.00000012329 := by
  have hl := lg_45
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.446198374342438421 80.44619841660850182 1.2352106 0.00000002328 0.3293222798696 0.9442175787293 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_46 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7174020209809:ℝ):ℂ) + ((0.6966594148453:ℝ):ℂ) * I)‖ ≤ 0.00000016405 := by
  have hl := lg_46
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.910678604536871678 80.910678657369435077 0.7707304 0.00000006404 0.7174020209809 0.6966594148453 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_47 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9504115689145:ℝ):ℂ) + ((0.310994935125:ℝ):ℂ) * I)‖ ≤ 0.00000015388 := by
  have hl := lg_47
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.365169239471482757 81.365169292304067289 0.3162397 0.00000005387 0.9504115689145 0.310994935125 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_48 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9917318902324:ℝ):ℂ) + (((-0.1283271518269):ℝ):ℂ) * I)‖ ≤ 0.0000001573 := by
  have hl := lg_48
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.810090936049329812 81.810090988881850945 (-0.128682) 0.00000005729 0.9917318902324 (-0.1283271518269) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_49 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.844893971179:ℝ):ℂ) + (((-0.5349338066204):ℝ):ℂ) * I)‖ ≤ 0.00000015535 := by
  have hl := lg_49
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.245838337998146252 82.245838380264230784 (-0.5644294) 0.00000005534 0.844893971179 (-0.5349338066204) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_50 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5475413127424:ℝ):ℂ) + (((-0.8367786510424):ℝ):ℂ) * I)‖ ≤ 0.0000001471 := by
  have hl := lg_50
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.672782146245857594 82.67278219907839986 (-0.9913732) 0.00000004709 0.5475413127424 (-0.8367786510424) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_51 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.160240431136:ℝ):ℂ) + (((-0.9870780132438):ℝ):ℂ) * I)‖ ≤ 0.00000012841 := by
  have hl := lg_51
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.091271068896029534 83.0912711217285718 (-1.4098621) 0.0000000284 0.160240431136 (-0.9870780132438) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_52 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2468498687514):ℝ):ℂ) + (((-0.969053735505):ℝ):ℂ) * I)‖ ≤ 0.00000013683 := by
  have hl := lg_52
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.5016334773141661 83.501633530146708366 (-1.8202245) 0.00000003682 (-0.2468498687514) (-0.969053735505) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_53 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6067564352603):ℝ):ℂ) + (((-0.794887808598):ℝ):ℂ) * I)‖ ≤ 0.00000014114 := by
  have hl := lg_53
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.904178981629842402 83.904179034462405801 (-2.22277) 0.00000004113 (-0.6067564352603) (-0.794887808598) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_54 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8659238969272):ℝ):ℂ) + (((-0.5001757737493):ℝ):ℂ) * I)‖ ≤ 0.00000015928 := by
  have hl := lg_54
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.299199834069089436 84.299199876335152835 (-2.6177909) 0.00000005927 (-0.8659238969272) (-0.5001757737493) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_55 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9907622515018):ℝ):ℂ) + (((-0.1356103262428):ℝ):ℂ) * I)‖ ≤ 0.00000013556 := by
  have hl := lg_55
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.686972176050636686 84.686972228883200085 (-3.0055632) 0.00000003555 (-0.9907622515018) (-0.1356103262428) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_56 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9701965636721):ℝ):ℂ) + ((0.2423192678398:ℝ):ℂ) * I)‖ ≤ 0.00000014769 := by
  have hl := lg_56
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.067757252838773126 85.067757305671315392 2.896837 0.00000004768 (-0.9701965636721) 0.2423192678398 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_57 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8145746755574):ℝ):ℂ) + ((0.580058702103:ℝ):ℂ) * I)‖ ≤ 0.00000016294 := by
  have hl := lg_57
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.441802421173811011 85.441802463439895543 2.5227919 0.00000006293 (-0.8145746755574) 0.580058702103 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_58 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5517456555211):ℝ):ℂ) + ((0.8340124289271:ℝ):ℂ) * I)‖ ≤ 0.00000016674 := by
  have hl := lg_58
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.809342114410342036 85.809342167242905435 2.1552522 0.00000006673 (-0.5517456555211) 0.8340124289271 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_59 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2213505659688):ℝ):ℂ) + ((0.9751943021492:ℝ):ℂ) * I)‖ ≤ 0.00000012693 := by
  have hl := lg_59
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.170598774592428936 86.170598827425013468 1.7939955 0.00000002692 (-0.2213505659688) 0.9751943021492 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_60 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1316027576358:ℝ):ℂ) + ((0.9913025341351:ℝ):ℂ) * I)‖ ≤ 0.00000015831 := by
  have hl := lg_60
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.525783605972508609 86.525783658805050875 1.4388107 0.0000000583 0.1316027576358 0.9913025341351 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_61 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4629313703274:ℝ):ℂ) + ((0.8863941258643:ℝ):ℂ) * I)‖ ≤ 0.00000015642 := by
  have hl := lg_61
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.875097344107429539 86.875097396939992938 1.0894969 0.00000005641 0.4629313703274 0.8863941258643 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_62 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7345023354644:ℝ):ℂ) + ((0.6786061591213:ℝ):ℂ) * I)‖ ≤ 0.00000016884 := by
  have hl := lg_62
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.218730931690756279 87.218730984523319678 0.7458633 0.00000006883 0.7345023354644 0.6786061591213 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_63 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9180240556977:ℝ):ℂ) + ((0.396524694263:ℝ):ℂ) * I)‖ ≤ 0.00000014967 := by
  have hl := lg_63
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.55686615085853275 87.556866193124617282 0.4077281 0.00000004966 0.9180240556977 0.396524694263 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_64 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9971949515108:ℝ):ℂ) + ((0.0748480372573:ℝ):ℂ) * I)‖ ≤ 0.00000013285 := by
  have hl := lg_64
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.8896761676794 87.8896762310784 0.0749181 0.00000003284 0.9971949515108 0.0748480372573 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_65 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9682329240461:ℝ):ℂ) + (((-0.2500500045852):ℝ):ℂ) * I)‖ ≤ 0.00000015329 := by
  have hl := lg_65
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.217326147237344897 88.217326200069908296 (-0.2527319) 0.00000005328 0.9682329240461 (-0.2500500045852) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_66 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8389859111075:ℝ):ℂ) + (((-0.5441531410946):ℝ):ℂ) * I)‖ ≤ 0.00000016475 := by
  have hl := lg_66
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.539973635777287701 88.5399736886098511 (-0.5753794) 0.00000006474 0.8389859111075 (-0.5441531410946) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_67 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.626941811303:ℝ):ℂ) + (((-0.7790660852842):ℝ):ℂ) * I)‖ ≤ 0.00000015046 := by
  have hl := lg_67
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.857769098122111521 88.857769150954696053 (-0.8931748) 0.00000005045 0.626941811303 (-0.7790660852842) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_68 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3565142593843:ℝ):ℂ) + (((-0.9342898815976):ℝ):ℂ) * I)‖ ≤ 0.00000016343 := by
  have hl := lg_68
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.170856300526099722 89.170856363925120855 (-1.206262) 0.00000006342 0.3565142593843 (-0.9342898815976) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_69 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0559885340966:ℝ):ℂ) + (((-0.9984314117903):ℝ):ℂ) * I)‖ ≤ 0.00000016634 := by
  have hl := lg_69
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.47937273418670149 89.479372787019286022 (-1.5147785) 0.00000006633 0.0559885340966 (-0.9984314117903) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_70 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2455231002228):ℝ):ℂ) + (((-0.9693907402363):ℝ):ℂ) * I)‖ ≤ 0.0000001751 := by
  have hl := lg_70
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.783449922761951923 89.783449975594515322 (-1.8188556) 0.00000007509 (-0.2455231002228) (-0.9693907402363) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_71 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5208301937773):ℝ):ℂ) + (((-0.8536603008473):ℝ):ℂ) * I)‖ ≤ 0.00000016638 := by
  have hl := lg_71
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.083213814046958071 90.083213866879542603 (-2.1186195) 0.00000006637 (-0.5208301937773) (-0.8536603008473) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_72 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7469045102402):ℝ):ℂ) + (((-0.6649313141594):ℝ):ℂ) * I)‖ ≤ 0.00000013483 := by
  have hl := lg_72
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.378785065699159624 90.37878511853170189 (-2.4141908) 0.00000003482 (-0.7469045102402) (-0.6649313141594) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_73 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9064872163186):ℝ):ℂ) + (((-0.4222332608012):ℝ):ℂ) * I)‖ ≤ 0.00000015821 := by
  have hl := lg_73
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.670279342321795179 90.670279395154358578 (-2.7056851) 0.0000000582 (-0.9064872163186) (-0.4222332608012) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_74 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9890119655305):ℝ):ℂ) + (((-0.1478354884366):ℝ):ℂ) * I)‖ ≤ 0.00000013955 := by
  have hl := lg_74
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.957807587216572786 90.957807640049136185 (-2.9932133) 0.00000003954 (-0.9890119655305) (-0.1478354884366) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_75 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9908623453506):ℝ):ℂ) + ((0.1348770260266:ℝ):ℂ) * I)‖ ≤ 0.00000013181 := by
  have hl := lg_75
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.241476275895687406 91.241476328728250805 3.0063033 0.0000000318 (-0.9908623453506) 0.1348770260266 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_76 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9150353601866):ℝ):ℂ) + ((0.4033736350736:ℝ):ℂ) * I)‖ ≤ 0.0000001549 := by
  have hl := lg_76
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.521387652803881199 91.521387705636444598 2.7263919 0.00000005489 (-0.9150353601866) 0.4033736350736 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_77 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7703202784871):ℝ):ℂ) + ((0.6376571716152:ℝ):ℂ) * I)‖ ≤ 0.00000015514 := by
  have hl := lg_77
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.797639952566731015 91.797640005399315547 2.4501396 0.00000005513 (-0.7703202784871) 0.6376571716152 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_78 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5701230907599):ℝ):ℂ) + ((0.821559286584:ℝ):ℂ) * I)‖ ≤ 0.00000015212 := by
  have hl := lg_78
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.070327606963995912 92.070327659796559311 2.177452 0.00000005211 (-0.5701230907599) 0.821559286584 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_79 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3310742232686):ℝ):ℂ) + ((0.9436047152728:ℝ):ℂ) * I)‖ ≤ 0.00000016899 := by
  have hl := lg_79
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.339541438718402969 92.339541491550987501 1.9082381 0.00000006898 (-0.3310742232686) 0.9436047152728 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p133_80 : ‖exp (-((((((21133:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0715531751011):ℝ):ℂ) + ((0.9974367865347:ℝ):ℂ) * I)‖ ≤ 0.00000017011 := by
  have hl := lg_80
  refine (ecis_approx ((((21133:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.605368837602578797 92.60536890100159993 1.6424107 0.0000000701 (-0.0715531751011) 0.9974367865347 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_2 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5071776847904):ℝ):ℂ) + (((-0.8618415144585):ℝ):ℂ) * I)‖ ≤ 0.00000013769 := by
  have hl := lg_2
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.6690737766889 14.6690737872704 (-2.1027032) 0.00000003768 (-0.5071776847904) (-0.8618415144585) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_3 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3069751342213):ℝ):ℂ) + ((0.9517175352845:ℝ):ℂ) * I)‖ ≤ 0.00000014146 := by
  have hl := lg_3
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.249931859581974732 23.249931870163495895 1.8828094 0.00000004145 (-0.3069751342213) 0.9517175352845 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_4 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4855416732457):ℝ):ℂ) + ((0.8742135228513:ℝ):ℂ) * I)‖ ≤ 0.00000013866 := by
  have hl := lg_4
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.3381475533778 29.3381475745408 2.077779 0.00000003865 (-0.4855416732457) 0.8742135228513 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_5 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8790242041254):ℝ):ℂ) + (((-0.4767771475924):ℝ):ℂ) * I)‖ ≤ 0.00000011512 := by
  have hl := lg_5
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.060534529840405067 34.06053455100342623 (-2.644608) 0.00000001511 (-0.8790242041254) (-0.4767771475924) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_6 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9759206198132:ℝ):ℂ) + (((-0.2181259815413):ℝ):ℂ) * I)‖ ≤ 0.00000011437 := by
  have hl := lg_6
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.919005636270874732 37.919005657433895895 (-0.2198938) 0.00000001436 0.9759206198132 (-0.2181259815413) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_7 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9425570914198):ℝ):ℂ) + ((0.3340451005916:ℝ):ℂ) * I)‖ ≤ 0.00000014438 := by
  have hl := lg_7
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.181296473455135786 41.181296494618178112 2.8010007 0.00000004437 (-0.9425570914198) 0.3340451005916 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_8 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9996894082064:ℝ):ℂ) + (((-0.0249216195292):ℝ):ℂ) * I)‖ ≤ 0.00000012021 := by
  have hl := lg_8
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.0072213300667 44.0072213618112 (-0.0249242) 0.0000000202 0.9996894082064 (-0.0249216195292) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_9 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8115325881639):ℝ):ℂ) + (((-0.5843071609129):ℝ):ℂ) * I)‖ ≤ 0.00000013111 := by
  have hl := lg_9
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.499863719163949464 46.49986374032699179 (-2.5175666) 0.0000000311 (-0.8115325881639) (-0.5843071609129) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_10 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0349151289247:ℝ):ℂ) + ((0.9993902810074:ℝ):ℂ) * I)‖ ≤ 0.00000015092 := by
  have hl := lg_10
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.729608306529305067 48.72960833827382623 1.5358741 0.00000005091 0.0349151289247 0.9993902810074 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_11 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.886451627505:ℝ):ℂ) + (((-0.4628212528544):ℝ):ℂ) * I)‖ ≤ 0.00000011605 := by
  have hl := lg_11
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.746657641728213879 50.746657673472756205 (-0.4811752) 0.00000001604 0.886451627505 (-0.4628212528544) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_12 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6829551867687):ℝ):ℂ) + (((-0.730460274652):ℝ):ℂ) * I)‖ ≤ 0.00000014449 := by
  have hl := lg_12
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.588079412959774732 52.588079444704295895 (-2.322597) 0.00000004448 (-0.6829551867687) (-0.730460274652) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_13 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6410366516755):ℝ):ℂ) + ((0.7675102678094:ℝ):ℂ) * I)‖ ≤ 0.00000012918 := by
  have hl := lg_13
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.2820232354548171 54.282023267199359426 2.2666445 0.00000002917 (-0.6410366516755) 0.7675102678094 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_14 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7659378589175:ℝ):ℂ) + ((0.6429146104086:ℝ):ℂ) * I)‖ ≤ 0.00000011729 := by
  have hl := lg_14
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.850370250144035786 55.850370281888578112 0.6982975 0.00000001728 0.7659378589175 0.6429146104086 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_15 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7235957448897:ℝ):ℂ) + (((-0.6902240201395):ℝ):ℂ) * I)‖ ≤ 0.00000015657 := by
  have hl := lg_15
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.310466389422379799 57.310466421166922125 (-0.7617986) 0.00000005656 0.7235957448897 (-0.6902240201395) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_16 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5284986458814):ℝ):ℂ) + (((-0.8489341442621):ℝ):ℂ) * I)‖ ≤ 0.00000015788 := by
  have hl := lg_16
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.6762951067556 58.6762951490816 (-2.1276274) 0.00000005787 (-0.5284986458814) (-0.8489341442621) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_17 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9640282277817):ℝ):ℂ) + ((0.2657998792187:ℝ):ℂ) * I)‖ ≤ 0.0000001488 := by
  have hl := lg_17
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.959293978256792742 59.959294020582813905 2.8725591 0.00000004879 (-0.9640282277817) 0.2657998792187 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_18 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0919890417222):ℝ):ℂ) + ((0.9957600193835:ℝ):ℂ) * I)‖ ≤ 0.00000015582 := by
  have hl := lg_18
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.168937495852849464 61.16893752759739179 1.6629156 0.00000005581 (-0.0919890417222) 0.9957600193835 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_19 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8684688520966:ℝ):ℂ) + ((0.4957437371647:ℝ):ℂ) * I)‖ ≤ 0.00000015956 := by
  have hl := lg_19
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.313162099595679289 62.313162131340242778 0.518691 0.00000005955 0.8684688520966 0.4957437371647 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_20 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.843607912766:ℝ):ℂ) + (((-0.5369596721529):ℝ):ℂ) * I)‖ ≤ 0.00000015376 := by
  have hl := lg_20
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.398682083218205067 63.39868212554422623 (-0.566829) 0.00000005375 0.843607912766 (-0.5369596721529) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_21 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0285750830146):ℝ):ℂ) + (((-0.9995916489399):ℝ):ℂ) * I)‖ ≤ 0.00000013877 := by
  have hl := lg_21
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.431228333037110518 64.431228364781674007 (-1.5993753) 0.00000003876 (-0.0285750830146) (-0.9995916489399) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_22 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8484670535843):ℝ):ℂ) + (((-0.5292482016116):ℝ):ℂ) * I)‖ ≤ 0.00000015339 := by
  have hl := lg_22
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.415731418417113879 65.415731460743156205 (-2.5838784) 0.00000005338 (-0.8484670535843) (-0.5292482016116) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_23 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9275408378185):ℝ):ℂ) + ((0.3737218136846:ℝ):ℂ) * I)‖ ≤ 0.00000013307 := by
  have hl := lg_23
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.356464069703652658 66.356464112029716147 2.7585743 0.00000003306 (-0.9275408378185) 0.3737218136846 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_24 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.28316144795):ℝ):ℂ) + ((0.9590722571284:ℝ):ℂ) * I)‖ ≤ 0.00000015301 := by
  have hl := lg_24
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.257153189648674732 67.257153231974695895 1.8578852 0.000000053 (-0.28316144795) 0.9590722571284 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_25 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5453671089859:ℝ):ℂ) + ((0.838197301616:ℝ):ℂ) * I)‖ ≤ 0.00000012305 := by
  have hl := lg_25
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.121069059680810134 68.12106910200685246 0.9939693 0.00000002304 0.5453671089859 0.838197301616 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_26 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9865916964454:ℝ):ℂ) + ((0.163207918022:ℝ):ℂ) * I)‖ ≤ 0.00000016685 := by
  have hl := lg_26
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.9510970121437171 68.951097054469759426 0.1639413 0.00000006684 0.9865916964454 0.163207918022 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_27 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8052156962423:ℝ):ℂ) + (((-0.5929820254654):ℝ):ℂ) * I)‖ ≤ 0.00000013153 := by
  have hl := lg_27
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.749795578745924196 69.749795610490487685 (-0.6347572) 0.00000003152 0.8052156962423 (-0.5929820254654) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_28 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1656239115252:ℝ):ℂ) + (((-0.9861889879384):ℝ):ℂ) * I)‖ ≤ 0.00000015216 := by
  have hl := lg_28
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.519444026832935786 70.519444069158978112 (-1.4044057) 0.00000005215 0.1656239115252 (-0.9861889879384) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_29 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5448808179113):ℝ):ℂ) + (((-0.838513502732):ℝ):ℂ) * I)‖ ≤ 0.00000015099 := by
  have hl := lg_29
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.262081627998842796 71.262081670324906285 (-2.1470433) 0.00000005098 (-0.5448808179113) (-0.838513502732) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_30 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.961855329363):ℝ):ℂ) + (((-0.2735586319905):ℝ):ℂ) * I)‖ ≤ 0.00000012948 := by
  have hl := lg_30
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.979540166111279799 71.979540208437322125 (-2.8645018) 0.00000002947 (-0.961855329363) (-0.2735586319905) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_31 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9143728401067):ℝ):ℂ) + ((0.4048732013118:ℝ):ℂ) * I)‖ ≤ 0.0000001427 := by
  have hl := lg_31
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.673471186514217169 72.673471228840280658 2.7247525 0.00000004269 (-0.9143728401067) 0.4048732013118 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_32 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4636040511828):ℝ):ℂ) + ((0.8860424841519:ℝ):ℂ) * I)‖ ≤ 0.00000015021 := by
  have hl := lg_32
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.3453688834445 73.345368936352 2.0528548 0.0000000502 (-0.4636040511828) 0.8860424841519 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_33 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1683564947104:ℝ):ℂ) + ((0.9857261742942:ℝ):ℂ) * I)‖ ≤ 0.0000001575 := by
  have hl := lg_33
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.996589501310188611 73.9965895436362521 1.4016342 0.00000005749 0.1683564947104 0.9857261742942 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_34 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7180109752448:ℝ):ℂ) + ((0.6960317804727:ℝ):ℂ) * I)‖ ≤ 0.00000013122 := by
  have hl := lg_34
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.628367754945692742 74.628367807853213905 0.7698559 0.00000003121 0.7180109752448 0.6960317804727 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_35 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9877955674995:ℝ):ℂ) + ((0.1557559527864:ℝ):ℂ) * I)‖ ≤ 0.00000015948 := by
  have hl := lg_35
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.241831003295540853 75.241831045621604342 0.1563927 0.00000005947 0.9877955674995 0.1557559527864 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_36 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9048421123533:ℝ):ℂ) + (((-0.4257472862063):ℝ):ℂ) * I)‖ ≤ 0.00000012873 := by
  have hl := lg_36
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.838011272541749464 75.83801131486779179 (-0.4397876) 0.00000002872 0.9048421123533 (-0.4257472862063) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_37 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.523679406367:ℝ):ℂ) + (((-0.8519154179537):ℝ):ℂ) * I)‖ ≤ 0.00000012289 := by
  have hl := lg_37
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.417855763284806046 76.417855805610869535 (-1.0196321) 0.00000002288 0.523679406367 (-0.8519154179537) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_38 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.013215488496):ℝ):ℂ) + (((-0.9999126716187):ℝ):ℂ) * I)‖ ≤ 0.00000013247 := by
  have hl := lg_38
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.982235876284579289 76.982235918610642778 (-1.5840122) 0.00000003246 (-0.013215488496) (-0.9999126716187) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_39 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5336706621332):ℝ):ℂ) + (((-0.8456923934685):ℝ):ℂ) * I)‖ ≤ 0.00000015122 := by
  have hl := lg_39
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.531955095036791832 77.531955137362855321 (-2.1337314) 0.00000005121 (-0.5336706621332) (-0.8456923934685) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_40 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8906332450908):ℝ):ℂ) + (((-0.4547223577445):ℝ):ℂ) * I)‖ ≤ 0.00000012667 := by
  have hl := lg_40
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.067755859907105067 78.06775591281462623 (-2.6695322) 0.00000002666 (-0.8906332450908) (-0.4547223577445) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_41 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9987246734953):ℝ):ℂ) + ((0.0504878795342:ℝ):ℂ) * I)‖ ≤ 0.00000017319 := by
  have hl := lg_41
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.59032562015712654 78.590325673064668866 3.0910833 0.00000007318 (-0.9987246734953) 0.0504878795342 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_42 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8469969854459):ℝ):ℂ) + ((0.5315976924081:ℝ):ℂ) * I)‖ ≤ 0.00000015873 := by
  have hl := lg_42
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.100302109726010518 79.100302152052074007 2.5811069 0.00000005872 (-0.8469969854459) 0.5315976924081 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_43 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4902134006354):ℝ):ℂ) + ((0.8716024448288:ℝ):ℂ) * I)‖ ≤ 0.00000016693 := by
  have hl := lg_43
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.59827802641794614 79.598278068744030792 2.0831309 0.00000006692 (-0.4902134006354) 0.8716024448288 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_44 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0258046085606):ℝ):ℂ) + ((0.9996670056458:ℝ):ℂ) * I)‖ ≤ 0.00000015469 := by
  have hl := lg_44
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.084805195106013879 80.084805248013556205 1.5966038 0.00000005468 (-0.0258046085606) 0.9996670056458 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_45 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4347724923867:ℝ):ℂ) + ((0.9005403266172:ℝ):ℂ) * I)‖ ≤ 0.00000014435 := by
  have hl := lg_45
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.560398249004354531 80.56039829133041802 1.1210107 0.00000004434 0.4347724923867 0.9005403266172 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_46 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7925169886635:ℝ):ℂ) + ((0.6098498361726:ℝ):ℂ) * I)‖ ≤ 0.00000014696 := by
  have hl := lg_46
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.025537846392552658 81.025537899300116147 0.6558711 0.00000004695 0.7925169886635 0.6098498361726 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_47 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9799202313511:ℝ):ℂ) + ((0.1993899199779:ℝ):ℂ) * I)‖ ≤ 0.00000012707 := by
  have hl := lg_47
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.480673667483792627 81.480673720391377279 0.2007353 0.00000002706 0.9799202313511 0.1993899199779 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_48 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9701814541561:ℝ):ℂ) + (((-0.2423797557792):ℝ):ℂ) * I)‖ ≤ 0.00000012701 := by
  have hl := lg_48
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.926226966337574732 81.926227019245095895 (-0.244818) 0.000000027 0.9701814541561 (-0.2423797557792) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
