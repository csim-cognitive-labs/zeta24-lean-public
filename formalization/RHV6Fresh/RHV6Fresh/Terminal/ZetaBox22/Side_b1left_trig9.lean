/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Base
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
namespace H22

open Complex Set

lemma cs_b1left_v21p604_12 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.961921693714):ℝ):ℂ) + ((0.2733251816475:ℝ):ℂ) * I)‖ ≤ 0.00000011946 := by
  have hl := lg_12
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.683923245172375056 53.68392327757839666 2.8647445 0.00000001945 (-0.961921693714) 0.2733251816475 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_13 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4216774806119:ℝ):ℂ) + ((0.9067458863126:ℝ):ℂ) * I)‖ ≤ 0.00000016288 := by
  have hl := lg_13
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.4131659017514468 55.413165934157490008 1.1355018 0.00000006287 0.4216774806119 0.9067458863126 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_14 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.89358521246:ℝ):ℂ) + (((-0.4488936044019):ℝ):ℂ) * I)‖ ≤ 0.00000013247 := by
  have hl := lg_14
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.014194532160456888 57.014194564566500096 (-0.4655268) 0.00000003246 0.89358521246 (-0.4488936044019) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_15 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3757931165463):ℝ):ℂ) + (((-0.9267035845153):ℝ):ℂ) * I)‖ ≤ 0.00000013687 := by
  have hl := lg_15
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.504716527764546292 58.5047165601705895 (-1.9560488) 0.00000003686 (-0.3757931165463) (-0.9267035845153) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_16 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9782914809825):ℝ):ℂ) + ((0.2072336312552:ℝ):ℂ) * I)‖ ≤ 0.00000013901 := by
  have hl := lg_16
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.8990067328048 59.8990067760128 2.9328463 0.000000039 (-0.9782914809825) 0.2072336312552 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_17 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0522918124177):ℝ):ℂ) + ((0.9986318472559:ℝ):ℂ) * I)‖ ≤ 0.00000013395 := by
  have hl := lg_17
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.208741062527040136 61.20874110573506174 1.623112 0.00000003394 (-0.0522918124177) 0.9986318472559 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_18 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9255685815121:ℝ):ℂ) + ((0.3785799795522:ℝ):ℂ) * I)‖ ≤ 0.00000013107 := by
  have hl := lg_18
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.443591440741150112 62.44359147314719332 0.3882616 0.00000003106 0.9255685815121 0.3785799795522 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_19 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7110495389558:ℝ):ℂ) + (((-0.7031419153704):ℝ):ℂ) * I)‖ ≤ 0.00000014969 := by
  have hl := lg_19
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.611659689064171212 63.611659721470236024 (-0.7798066) 0.00000004968 0.7110495389558 (-0.7031419153704) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_20 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3118606054354):ℝ):ℂ) + (((-0.9501278665399):ℝ):ℂ) * I)‖ ≤ 0.00000015641 := by
  have hl := lg_20
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.719800015396971236 64.71980005860499284 (-1.887947) 0.0000000564 (-0.3118606054354) (-0.9501278665399) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_21 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9801493468063):ℝ):ℂ) + (((-0.1982605801209):ℝ):ℂ) * I)‖ ≤ 0.00000014408 := by
  have hl := lg_21
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.773862727729231944 65.773862760135296756 (-2.9420097) 0.00000004407 (-0.9801493468063) (-0.1982605801209) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_22 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6927972810239):ℝ):ℂ) + ((0.7211323924103:ℝ):ℂ) * I)‖ ≤ 0.0000001391 := by
  have hl := lg_22
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.778881139889586932 66.77888118309763014 2.3361572 0.00000003909 (-0.6927972810239) 0.7211323924103 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_23 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1937420349973:ℝ):ℂ) + ((0.9810525082151:ℝ):ℂ) * I)‖ ≤ 0.00000016052 := by
  have hl := lg_23
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.739217018469863064 67.739217061677927876 1.3758213 0.00000006051 0.1937420349973 0.9810525082151 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_24 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8976610305751:ℝ):ℂ) + ((0.440686594063:ℝ):ℂ) * I)‖ ≤ 0.00000015062 := by
  have hl := lg_24
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.658674928373575056 68.65867497158159666 0.4563634 0.00000005061 0.8976610305751 0.440686594063 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_25 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9108097959032:ℝ):ℂ) + (((-0.4128262536307):ℝ):ℂ) * I)‖ ≤ 0.00000016224 := by
  have hl := lg_25
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.540593297989142472 69.54059334119718568 (-0.4255549) 0.00000006223 0.9108097959032 (-0.4128262536307) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_26 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2935297222886:ℝ):ℂ) + (((-0.9559499475041):ℝ):ℂ) * I)‖ ≤ 0.0000001492 := by
  have hl := lg_26
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.3879175849526468 70.387917628160690008 (-1.2728792) 0.00000004919 0.2935297222886 (-0.9559499475041) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_27 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4946438353261):ℝ):ℂ) + (((-0.869095780779):ℝ):ℂ) * I)‖ ≤ 0.00000014268 := by
  have hl := lg_27
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.203259636309925168 71.20325966871598998 (-2.0882213) 0.00000004267 (-0.4946438353261) (-0.869095780779) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_28 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.96438586164):ℝ):ℂ) + (((-0.2644993565589):ℝ):ℂ) * I)‖ ≤ 0.00000016363 := by
  have hl := lg_28
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.988946215361656888 71.988946258569700096 (-2.8739079) 0.00000006362 (-0.96438586164) (-0.2644993565589) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_29 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8821313246535):ℝ):ℂ) + ((0.4710035307373:ℝ):ℂ) * I)‖ ≤ 0.00000014563 := by
  have hl := lg_29
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.747059088564333968 72.74705913177239878 2.6511646 0.00000004562 (-0.8821313246535) 0.4710035307373 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p604_30 : ‖exp (-((((((21604:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3409799977036):ℝ):ℂ) + ((0.940070551163:ℝ):ℂ) * I)‖ ≤ 0.00000016803 := by
  have hl := lg_30
  refine (ecis_approx ((((21604:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.479468210965746292 73.4794682541737895 1.9187555 0.00000006802 (-0.3409799977036) 0.940070551163 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_2 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7871696801659):ℝ):ℂ) + (((-0.6167364871506):ℝ):ℂ) * I)‖ ≤ 0.00000015056 := by
  have hl := lg_2
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.0433732540509 15.0433732649024 (-2.4770026) 0.00000005055 (-0.7871696801659) (-0.6167364871506) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_3 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2775448645726:ℝ):ℂ) + ((0.9607126772086:ℝ):ℂ) * I)‖ ≤ 0.00000013341 := by
  have hl := lg_3
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.843182495322383292 23.843182506173904995 1.2895587 0.0000000334 0.2775448645726 0.9607126772086 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_4 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2392723148387:ℝ):ℂ) + ((0.9709525010791:ℝ):ℂ) * I)‖ ≤ 0.00000012781 := by
  have hl := lg_4
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.0867465081018 30.0867465298048 1.32918 0.0000000278 0.2392723148387 0.9709525010791 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_5 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9315615882173):ℝ):ℂ) + ((0.3635835628786:ℝ):ℂ) * I)‖ ≤ 0.00000014082 := by
  have hl := lg_5
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.929631002274077927 34.92963102397709963 2.7694808 0.00000004081 (-0.9315615882173) 0.3635835628786 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_6 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3740316594471:ℝ):ℂ) + (((-0.9274159356682):ℝ):ℂ) * I)‖ ≤ 0.00000012801 := by
  have hl := lg_6
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.886555749373283292 38.886555771076304995 (-1.1874439) 0.000000028 0.3740316594471 (-0.9274159356682) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_7 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1784519016077):ℝ):ℂ) + ((0.9839486362671:ℝ):ℂ) * I)‖ ≤ 0.00000012513 := by
  have hl := lg_7
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.232087953664263666 42.232087975367307072 1.7502092 0.00000002512 (-0.1784519016077) 0.9839486362671 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_8 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4104739231837:ℝ):ℂ) + (((-0.9118723366712):ℝ):ℂ) * I)‖ ≤ 0.00000014447 := by
  have hl := lg_8
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.1301197621527 45.1301197947072 (-1.1478226) 0.00000004446 0.4104739231837 (-0.9118723366712) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_9 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8459377496097):ℝ):ℂ) + ((0.5332816551448:ℝ):ℂ) * I)‖ ≤ 0.00000015493 := by
  have hl := lg_9
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.686364990644766584 47.68636501234780999 2.5791175 0.00000005492 (-0.8459377496097) 0.5332816551448 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_10 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9575322869198:ℝ):ℂ) + ((0.2883260645626:ℝ):ℂ) * I)‖ ≤ 0.00000013146 := by
  have hl := lg_10
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.973004256324977927 49.97300428887949963 0.2924782 0.00000003145 0.9575322869198 0.2883260645626 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_11 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2038043541709):ℝ):ℂ) + (((-0.9790116369176):ℝ):ℂ) * I)‖ ≤ 0.00000016375 := by
  have hl := lg_11
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.041521088618221699 52.041521121172765105 (-1.7760386) 0.00000006374 (-0.2038043541709) (-0.9790116369176) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_12 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.866397574514):ℝ):ℂ) + ((0.4993548265423:ℝ):ℂ) * I)‖ ≤ 0.00000016121 := by
  have hl := lg_12
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.929929003424183292 53.929929035978704995 2.6187387 0.0000000612 (-0.866397574514) 0.4993548265423 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_13 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6359388330952:ℝ):ℂ) + ((0.7717394641726:ℝ):ℂ) * I)‖ ≤ 0.00000015602 := by
  have hl := lg_13
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.6670958880629351 55.667095920617478506 0.8815719 0.00000005601 0.6359388330952 0.7717394641726 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_14 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7473088853602:ℝ):ℂ) + (((-0.6644768091225):ℝ):ℂ) * I)‖ ≤ 0.00000015692 := by
  have hl := lg_14
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.275461207715163666 57.275461240269707072 (-0.7267935) 0.00000005691 0.7473088853602 (-0.6644768091225) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_15 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6078493879151):ℝ):ℂ) + (((-0.7940523418507):ℝ):ℂ) * I)‖ ≤ 0.00000016555 := by
  have hl := lg_15
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.772813497596461219 58.772813530151004625 (-2.2241457) 0.00000006554 (-0.6078493879151) (-0.7940523418507) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_16 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8854975186752):ℝ):ℂ) + ((0.4646441050082:ℝ):ℂ) * I)‖ ≤ 0.00000015561 := by
  have hl := lg_16
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.1734930162036 60.1734930596096 2.65836 0.0000000556 (-0.8854975186752) 0.4646441050082 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_17 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2261976971865:ℝ):ℂ) + ((0.9740814143528:ℝ):ℂ) * I)‖ ≤ 0.00000015511 := by
  have hl := lg_17
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.489229183485667102 61.489229226891688805 1.3426239 0.0000000551 0.2261976971865 0.9740814143528 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_18 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9947908127088:ℝ):ℂ) + ((0.1019374266407:ℝ):ℂ) * I)‖ ≤ 0.00000012712 := by
  have hl := lg_18
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.729738244695666584 62.72973827725020999 0.1021148 0.00000002711 0.9947908127088 0.1019374266407 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_19 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4789781082544:ℝ):ℂ) + (((-0.8778268461451):ℝ):ℂ) * I)‖ ≤ 0.00000012389 := by
  have hl := lg_19
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.903159147924444909 63.903159180479010018 (-1.0713061) 0.00000002388 0.4789781082544 (-0.8778268461451) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_20 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.575919261582):ℝ):ℂ) + (((-0.8175065774222):ℝ):ℂ) * I)‖ ≤ 0.00000016143 := by
  have hl := lg_20
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.016377510375877927 65.01637755378189963 (-2.1845245) 0.00000006142 (-0.575919261582) (-0.8175065774222) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_21 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9948203372339):ℝ):ℂ) + ((0.1016488866301:ℝ):ℂ) * I)‖ ≤ 0.00000013 := by
  have hl := lg_21
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.075270448986646958 66.075270481541212067 3.0397679 0.00000002999 (-0.9948203372339) 0.1016488866301 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_22 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4433634934966):ℝ):ℂ) + ((0.8963419060996:ℝ):ℂ) * I)‖ ≤ 0.00000013632 := by
  have hl := lg_22
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.084894342669121699 67.084894386075165105 2.030144 0.00000003631 (-0.4433634934966) 0.8963419060996 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_23 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4841477825274:ℝ):ℂ) + ((0.8749862425626:ℝ):ℂ) * I)‖ ≤ 0.00000013325 := by
  have hl := lg_23
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.049630945743910298 68.049630989149975407 1.0654074 0.00000003324 0.4841477825274 0.8749862425626 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_24 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9899722432565:ℝ):ℂ) + ((0.1412620174772:ℝ):ℂ) * I)‖ ≤ 0.00000012192 := by
  have hl := lg_24
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.973302257475083292 68.973302300881104995 0.1417361 0.00000002191 0.9899722432565 0.1412620174772 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_25 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7356140580877:ℝ):ℂ) + (((-0.677400883926):ℝ):ℂ) * I)‖ ≤ 0.00000016899 := by
  have hl := lg_25
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.859262004548155854 69.85926204795419926 (-0.7442236) 0.00000006898 0.7356140580877 (-0.677400883926) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_26 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0246319816792):ℝ):ℂ) + (((-0.9996965867093):ℝ):ℂ) * I)‖ ≤ 0.00000013688 := by
  have hl := lg_26
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.7104691421138351 70.710469185519878506 (-1.5954308) 0.00000003687 (-0.0246319816792) (-0.9996965867093) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_27 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7471161200377):ℝ):ℂ) + (((-0.664693540774):ℝ):ℂ) * I)‖ ≤ 0.00000013956 := by
  have hl := lg_27
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.529547485967149876 71.529547518521714985 (-2.4145091) 0.00000003955 (-0.7471161200377) (-0.664693540774) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_28 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9980659886436):ℝ):ℂ) + ((0.0621633474416:ℝ):ℂ) * I)‖ ≤ 0.0000001244 := by
  have hl := lg_28
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.318834461766063666 72.318834505172107072 3.0793892 0.00000002439 (-0.9980659886436) 0.0621633474416 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_29 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6794450120453):ℝ):ℂ) + ((0.7337264310261:ℝ):ℂ) * I)‖ ≤ 0.0000001329 := by
  have hl := lg_29
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.080421375630056476 73.080421419036121585 2.3178023 0.00000003289 (-0.6794450120453) 0.7337264310261 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p703_30 : ‖exp (-((((((21703:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.011240336498):ℝ):ℂ) + ((0.9999368254221:ℝ):ℂ) * I)‖ ≤ 0.00000013452 := by
  have hl := lg_30
  refine (ecis_approx ((((21703:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.816186751647361219 73.816186795053404625 1.5820369 0.00000003451 (-0.011240336498) 0.9999368254221 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_2 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8276052838339):ℝ):ℂ) + (((-0.5613105148746):ℝ):ℂ) * I)‖ ≤ 0.00000012146 := by
  have hl := lg_2
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.1119948249006 15.1119948358016 (-2.5456242) 0.00000002145 (-0.8276052838339) (-0.5613105148746) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_3 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3801886248878:ℝ):ℂ) + ((0.9249089736325:ℝ):ℂ) * I)‖ ≤ 0.00000011686 := by
  have hl := lg_3
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.951945111874791528 23.95194512277581333 1.1807961 0.00000001685 0.3801886248878 0.9249089736325 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_4 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3698610183762:ℝ):ℂ) + ((0.9290870933802:ℝ):ℂ) * I)‖ ≤ 0.00000013572 := by
  have hl := lg_4
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.2239896498012 30.2239896716032 1.1919369 0.00000003571 0.3698610183762 0.9290870933802 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_5 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8620750896724):ℝ):ℂ) + ((0.5067805636411:ℝ):ℂ) * I)‖ ≤ 0.00000013429 := by
  have hl := lg_5
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.088965355553584618 35.08896537735560642 2.6101465 0.00000003428 (-0.8620750896724) 0.5067805636411 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_6 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2045150174174:ℝ):ℂ) + (((-0.9788634264548):ℝ):ℂ) * I)‖ ≤ 0.00000011551 := by
  have hl := lg_6
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.063939936775391528 39.06393995857741333 (-1.3648281) 0.0000000155 0.2045150174174 (-0.9788634264548) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_7 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0132318406558:ℝ):ℂ) + ((0.9999124553643:ℝ):ℂ) * I)‖ ≤ 0.00000012993 := by
  have hl := lg_7
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.424733058369270444 42.424733080171314048 1.5575641 0.00000002992 0.0132318406558 0.9999124553643 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_8 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2154074216828:ℝ):ℂ) + (((-0.9765242663057):ℝ):ℂ) * I)‖ ≤ 0.00000015716 := by
  have hl := lg_8
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.3359844747018 45.3359845074048 (-1.3536873) 0.00000005715 0.2154074216828 (-0.9765242663057) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_9 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7109132190082):ℝ):ℂ) + ((0.7032797416489:ℝ):ℂ) * I)‖ ≤ 0.0000001337 := by
  have hl := lg_9
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.903890223749583056 47.90389024555162666 2.3615922 0.00000003369 (-0.7109132190082) 0.7032797416489 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_10 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9979191584523:ℝ):ℂ) + ((0.0644775402277:ℝ):ℂ) * I)‖ ≤ 0.00000015574 := by
  have hl := lg_10
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.200960180454184618 50.20096021315720642 0.0645223 0.00000005573 0.9979191584523 0.0644775402277 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_11 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.428321076405):ℝ):ℂ) + (((-0.9036266128791):ℝ):ℂ) * I)‖ ≤ 0.0000001369 := by
  have hl := lg_11
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.278912720548056466 52.27891275325110007 (-2.0134303) 0.00000003689 (-0.428321076405) (-0.9036266128791) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_12 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7187040379734):ℝ):ℂ) + ((0.6953161193109:ℝ):ℂ) * I)‖ ≤ 0.00000012978 := by
  have hl := lg_12
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.175934761675991528 54.17593479437901333 2.372733 0.00000002977 (-0.7187040379734) 0.6953161193109 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_13 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8094145227061:ℝ):ℂ) + ((0.5872377120319:ℝ):ℂ) * I)‖ ≤ 0.00000014248 := by
  have hl := lg_13
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.9210258743744234 55.921025907077467004 0.6276419 0.00000004247 0.8094145227061 0.5872377120319 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_14 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5503106339425:ℝ):ℂ) + (((-0.8349600027366):ℝ):ℂ) * I)‖ ≤ 0.00000015137 := by
  have hl := lg_14
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.536727883269870444 57.536727915972914048 (-0.9880601) 0.00000005136 0.5503106339425 (-0.8349600027366) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_15 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7964770295655):ℝ):ℂ) + (((-0.6046687864663):ℝ):ℂ) * I)‖ ≤ 0.00000013553 := by
  have hl := lg_15
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.040910467428376146 59.04091050013141975 (-2.4922427) 0.00000003552 (-0.7964770295655) (-0.6046687864663) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_16 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.726405654167):ℝ):ℂ) + ((0.6872661970195:ℝ):ℂ) * I)‖ ≤ 0.00000017143 := by
  have hl := lg_16
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.4479792996024 60.4479793432064 2.3838738 0.00000007142 (-0.726405654167) 0.6872661970195 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_17 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4870078787484:ℝ):ℂ) + ((0.873397576157:ℝ):ℂ) * I)‖ ≤ 0.00000016737 := by
  have hl := lg_17
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.769717304444294068 61.76971734804831587 1.0621357 0.00000006736 0.4870078787484 0.873397576157 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_18 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9831138503295:ℝ):ℂ) + (((-0.1829949652049):ℝ):ℂ) * I)‖ ≤ 0.00000012316 := by
  have hl := lg_18
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.015885048650183056 63.01588508135322666 (-0.184032) 0.00000002315 0.9831138503295 (-0.1829949652049) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_19 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2064943490628:ℝ):ℂ) + (((-0.9784477930912):ℝ):ℂ) * I)‖ ≤ 0.00000016503 := by
  have hl := lg_19
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.194658606784718606 64.194658639487784012 (-1.3628056) 0.00000006502 0.2064943490628 (-0.9784477930912) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_20 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7896913084243):ℝ):ℂ) + (((-0.6135043906555):ℝ):ℂ) * I)‖ ≤ 0.00000016646 := by
  have hl := lg_20
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.312955005354784618 65.31295504895880642 (-2.481102) 0.00000006645 (-0.7896913084243) (-0.6135043906555) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_21 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9197974074647):ℝ):ℂ) + ((0.3923935894974:ℝ):ℂ) * I)‖ ≤ 0.00000012399 := by
  have hl := lg_21
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.376678170244061972 66.376678202947127378 2.7383602 0.00000002398 (-0.9197974074647) 0.3923935894974 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_22 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1527343262503):ℝ):ℂ) + ((0.9882672844854:ℝ):ℂ) * I)‖ ≤ 0.00000013354 := by
  have hl := lg_22
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.390907545448656466 67.39090758905270007 1.7241308 0.00000003353 (-0.1527343262503) 0.9882672844854 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_23 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7282759975436:ℝ):ℂ) + ((0.6852839348779:ℝ):ℂ) * I)‖ ≤ 0.00000013766 := by
  have hl := lg_23
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.360044873017957532 68.360044916622022938 0.7549935 0.00000003765 0.7282759975436 0.6852839348779 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_24 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9850915083163:ℝ):ℂ) + (((-0.1720311606749):ℝ):ℂ) * I)‖ ≤ 0.00000015122 := by
  have hl := lg_24
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.287929586576591528 69.28792963018061333 (-0.1728912) 0.00000005121 0.9850915083163 (-0.1720311606749) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_25 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4863468394365:ℝ):ℂ) + (((-0.8737658449322):ℝ):ℂ) * I)‖ ≤ 0.00000016788 := by
  have hl := lg_25
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.177930711107169236 70.17793075471121284 (-1.0628924) 0.00000006787 0.4863468394365 (-0.8737658449322) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_26 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3402530333004):ℝ):ℂ) + (((-0.9403339158659):ℝ):ℂ) * I)‖ ≤ 0.00000016392 := by
  have hl := lg_26
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.0330206992750234 71.033020742879067004 (-1.9179823) 0.00000006391 (-0.3402530333004) (-0.9403339158659) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_27 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9207508603423):ℝ):ℂ) + (((-0.3901510643774):ℝ):ℂ) * I)‖ ≤ 0.00000014337 := by
  have hl := lg_27
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.855835335624374584 71.85583536832743999 (-2.740797) 0.00000004336 (-0.9207508603423) (-0.3901510643774) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_28 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9241118146812):ℝ):ℂ) + ((0.3821221713238:ℝ):ℂ) * I)‖ ≤ 0.00000016563 := by
  have hl := lg_28
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.648722708170470444 72.648722751774514048 2.749501 0.00000006562 (-0.9241118146812) 0.3821221713238 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_29 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4019483631218):ℝ):ℂ) + ((0.915662335897:ℝ):ℂ) * I)‖ ≤ 0.00000012347 := by
  have hl := lg_29
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.413783662695778984 73.41378370629984439 1.98444 0.00000002346 (-0.4019483631218) 0.915662335897 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p802_30 : ‖exp (-((((((21802:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3197616570468:ℝ):ℂ) + ((0.9474980119677:ℝ):ℂ) * I)‖ ≤ 0.00000014979 := by
  have hl := lg_30
  refine (ecis_approx ((((21802:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.152905292328976146 74.15290533593301975 1.2453184 0.00000004978 0.3197616570468 0.9474980119677 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_2 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8641452861612):ℝ):ℂ) + (((-0.5032424110923):ℝ):ℂ) * I)‖ ≤ 0.00000011862 := by
  have hl := lg_2
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.1806163957503 15.1806164067008 (-2.6142458) 0.00000001861 (-0.8641452861612) (-0.5032424110923) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_3 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4783394503466:ℝ):ℂ) + ((0.8781750225565:ℝ):ℂ) * I)‖ ≤ 0.00000011067 := by
  have hl := lg_3
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.060707728427199764 24.060707739377721665 1.0720335 0.00000001066 0.4783394503466 0.8781750225565 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_4 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4934941575083:ℝ):ℂ) + ((0.8697491112414:ℝ):ℂ) * I)‖ ≤ 0.00000014441 := by
  have hl := lg_4
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.3612327915006 30.3612328134016 1.0546937 0.0000000444 0.4934941575083 0.8697491112414 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_5 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7707489287115):ℝ):ℂ) + ((0.6371389870747:ℝ):ℂ) * I)‖ ≤ 0.00000013426 := by
  have hl := lg_5
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.248299708833091309 35.24829973073411321 2.4508121 0.00000003425 (-0.7707489287115) 0.6371389870747 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_6 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0285801345403:ℝ):ℂ) + (((-0.9995915045205):ℝ):ℂ) * I)‖ ≤ 0.00000011892 := by
  have hl := lg_6
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.241324124177499764 39.241324146078521665 (-1.5422123) 0.00000001891 0.0285801345403 (-0.9995915045205) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_7 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2044260378871:ℝ):ℂ) + ((0.9788820128257:ℝ):ℂ) * I)‖ ≤ 0.00000013473 := by
  have hl := lg_7
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.617378163074277222 42.617378184975321024 1.364919 0.00000003472 0.2044260378871 0.9788820128257 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_8 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0112439898568:ℝ):ℂ) + (((-0.9999367843478):ℝ):ℂ) * I)‖ ≤ 0.00000016302 := by
  have hl := lg_8
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.5418491872509 45.5418492201024 (-1.5595521) 0.00000006301 0.0112439898568 (-0.9999367843478) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_9 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5423827404838):ℝ):ℂ) + ((0.8401315151909:ℝ):ℂ) * I)‖ ≤ 0.00000012133 := by
  have hl := lg_9
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.121415456854399528 48.12141547875544333 2.144067 0.00000002132 (-0.5423827404838) 0.8401315151909 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_10 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9866744136795:ℝ):ℂ) + (((-0.1627071030725):ℝ):ℂ) * I)‖ ≤ 0.00000015287 := by
  have hl := lg_10
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.428916104583391309 50.42891613743491321 (-0.1634337) 0.00000005286 0.9866744136795 (-0.1627071030725) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_11 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6288129088381):ℝ):ℂ) + (((-0.7775566382354):ℝ):ℂ) * I)‖ ≤ 0.00000012791 := by
  have hl := lg_11
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.516304352477891233 52.516304385329435035 (-2.2508219) 0.0000000279 (-0.6288129088381) (-0.7775566382354) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_12 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5277342213309):ℝ):ℂ) + ((0.8494095547077:ℝ):ℂ) * I)‖ ≤ 0.0000001447 := by
  have hl := lg_12
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.421940519927799764 54.421940552779321665 2.1267272 0.00000004469 (-0.5277342213309) 0.8494095547077 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_13 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9309786454768:ℝ):ℂ) + ((0.3650736386898:ℝ):ℂ) * I)‖ ≤ 0.00000012894 := by
  have hl := lg_13
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.1749558606859117 56.174955893537455502 0.3737119 0.00000002893 0.9309786454768 0.3650736386898 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_14 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.315961147341:ℝ):ℂ) + (((-0.9487721293182):ℝ):ℂ) * I)‖ ≤ 0.00000012707 := by
  have hl := lg_14
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.797994558824577222 57.797994591676121024 (-1.2493268) 0.00000002706 0.315961147341 (-0.9487721293182) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_15 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9281991605616):ℝ):ℂ) + (((-0.372083751562):ℝ):ℂ) * I)‖ ≤ 0.00000012737 := by
  have hl := lg_15
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.309007437260291073 59.309007470111834875 (-2.7603397) 0.00000002736 (-0.9281991605616) (-0.372083751562) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_16 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5129271188535):ℝ):ℂ) + ((0.8584321584947:ℝ):ℂ) * I)‖ ≤ 0.00000015502 := by
  have hl := lg_16
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.7224655830012 60.7224656268032 2.1093875 0.00000005501 (-0.5129271188535) 0.8584321584947 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_17 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7097538504478:ℝ):ℂ) + ((0.7044497652598:ℝ):ℂ) * I)‖ ≤ 0.00000014641 := by
  have hl := lg_17
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.050205425402921034 62.050205469204942935 0.7816476 0.0000000464 0.7097538504478 0.7044497652598 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_18 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8914872978765:ℝ):ℂ) + (((-0.4530456905489):ℝ):ℂ) * I)‖ ≤ 0.00000011921 := by
  have hl := lg_18
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.302031852604699528 63.30203188545624333 (-0.4701788) 0.0000000192 0.8914872978765 (-0.4530456905489) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_19 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.083411646325):ℝ):ℂ) + (((-0.9965151766315):ℝ):ℂ) * I)‖ ≤ 0.00000012672 := by
  have hl := lg_19
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.486158065644992303 64.486158098496558006 (-1.654305) 0.00000002671 (-0.083411646325) (-0.9965151766315) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_20 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9345111583816):ℝ):ℂ) + (((-0.3559338347112):ℝ):ℂ) * I)‖ ≤ 0.00000017148 := by
  have hl := lg_20
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.609532500333691309 65.60953254413571321 (-2.7776795) 0.00000007147 (-0.9345111583816) (-0.3559338347112) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_21 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7618446950874):ℝ):ℂ) + ((0.6477597243811:ℝ):ℂ) * I)‖ ≤ 0.00000014539 := by
  have hl := lg_21
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.678085891501476986 66.678085924353042689 2.4369525 0.00000004538 (-0.7618446950874) 0.6477597243811 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_22 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1520862407344:ℝ):ℂ) + ((0.9883672269856:ℝ):ℂ) * I)‖ ≤ 0.00000013076 := by
  have hl := lg_22
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.696920748228191233 67.696920792030235035 1.4181176 0.00000003075 0.1520862407344 0.9883672269856 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_23 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9027915501217:ℝ):ℂ) + ((0.4300783847496:ℝ):ℂ) * I)‖ ≤ 0.00000016513 := by
  have hl := lg_23
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.670458800292004766 68.670458844094070469 0.4445796 0.00000006512 0.9027915501217 0.4300783847496 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_24 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8834979520777:ℝ):ℂ) + (((-0.4684350207602):ℝ):ℂ) * I)‖ ≤ 0.00000016331 := by
  have hl := lg_24
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.602556915678099764 69.602556959480121665 (-0.4875186) 0.0000000633 0.8834979520777 (-0.4684350207602) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_25 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1881078292937:ℝ):ℂ) + (((-0.9821483821492):ℝ):ℂ) * I)‖ ≤ 0.00000016132 := by
  have hl := lg_25
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.496599417666182618 70.49659946146822642 (-1.3815611) 0.00000006131 0.1881078292937 (-0.9821483821492) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_26 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6207802698472):ℝ):ℂ) + (((-0.7839846022433):ℝ):ℂ) * I)‖ ≤ 0.00000012255 := by
  have hl := lg_26
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.3555722564362117 71.355572300238255502 (-2.2405339) 0.00000002254 (-0.6207802698472) (-0.7839846022433) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_27 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9972255734893):ℝ):ℂ) + (((-0.0744389350783):ℝ):ℂ) * I)‖ ≤ 0.00000013917 := by
  have hl := lg_27
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.182123185281599292 72.182123218133164995 (-3.0670848) 0.00000003916 (-0.9972255734893) (-0.0744389350783) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_28 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7504987053198):ℝ):ℂ) + ((0.6608719189671:ℝ):ℂ) * I)‖ ≤ 0.0000001316 := by
  have hl := lg_28
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.978610954574877222 72.978610998376921024 2.4196127 0.00000003159 (-0.7504987053198) 0.6608719189671 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_29 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.080195164093):ℝ):ℂ) + ((0.9967791809903:ℝ):ℂ) * I)‖ ≤ 0.00000013641 := by
  have hl := lg_29
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.747145949761501492 73.747145993563567195 1.6510777 0.0000000364 (-0.080195164093) 0.9967791809903 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p901_30 : ‖exp (-((((((21901:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6148506106213:ℝ):ℂ) + ((0.7886435992377:ℝ):ℂ) * I)‖ ≤ 0.00000015316 := by
  have hl := lg_30
  refine (ecis_approx ((((21901:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.489623833010591073 74.489623876812634875 0.9085998 0.00000005315 0.6148506106213 0.7886435992377 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_2 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8966176905623):ℝ):ℂ) + (((-0.4428055068064):ℝ):ℂ) * I)‖ ≤ 0.00000014777 := by
  have hl := lg_2
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.2492379666 15.2492379776 (-2.6828674) 0.00000004776 (-0.8966176905623) (-0.4428055068064) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_3 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5708374291683:ℝ):ℂ) + ((0.8210631093044:ℝ):ℂ) * I)‖ ≤ 0.00000012728 := by
  have hl := lg_3
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.169470344979608 24.16947035597963 0.9632709 0.00000002727 0.5708374291683 0.8210631093044 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_4 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6078464924715:ℝ):ℂ) + ((0.7940545583208:ℝ):ℂ) * I)‖ ≤ 0.00000011932 := by
  have hl := lg_4
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.4984759332 30.4984759552 0.9174506 0.00000001931 0.6078464924715 0.7940545583208 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_5 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6598968542787):ℝ):ℂ) + ((0.7513562016082:ℝ):ℂ) * I)‖ ≤ 0.00000014105 := by
  have hl := lg_5
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.407634062112598 35.40763408411262 2.2914778 0.00000004104 (-0.6598968542787) 0.7513562016082 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_6 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1482516711606):ℝ):ℂ) + (((-0.9889496660586):ℝ):ℂ) * I)‖ ≤ 0.00000013151 := by
  have hl := lg_6
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.418708311579608 39.41870833357963 (-1.7195965) 0.0000000315 (-0.1482516711606) (-0.9889496660586) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_7 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3880569826655:ℝ):ℂ) + ((0.9216353824613:ℝ):ℂ) * I)‖ ≤ 0.00000013954 := by
  have hl := lg_7
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.810023267779284 42.810023289779328 1.1722739 0.00000003953 0.3880569826655 0.9216353824613 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_8 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1933941871387):ℝ):ℂ) + (((-0.981121138484):ℝ):ℂ) * I)‖ ≤ 0.00000015047 := by
  have hl := lg_8
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.7477138998 45.7477139328 (-1.7654168) 0.00000005046 (-0.1933941871387) (-0.981121138484) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_9 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3482892589212):ℝ):ℂ) + ((0.9373871089991:ℝ):ℂ) * I)‖ ≤ 0.00000015454 := by
  have hl := lg_9
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.338940689959216 48.33894071195926 1.9265418 0.00000005453 (-0.3482892589212) 0.9373871089991 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_10 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9243798572116:ℝ):ℂ) + (((-0.3814733012695):ℝ):ℂ) * I)‖ ≤ 0.00000012874 := by
  have hl := lg_10
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.656872028712598 50.65687206171262 (-0.3913896) 0.00000002873 0.9243798572116 (-0.3814733012695) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_11 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7940342395077):ℝ):ℂ) + (((-0.6078730348044):ℝ):ℂ) * I)‖ ≤ 0.00000015999 := by
  have hl := lg_11
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.753695984407726 52.75369601740777 (-2.4882135) 0.00000005998 (-0.7940342395077) (-0.6078730348044) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_12 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3049873755209):ℝ):ℂ) + ((0.9523563937787:ℝ):ℂ) * I)‖ ≤ 0.00000014658 := by
  have hl := lg_12
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.667946278179608 54.66794631117963 1.8807215 0.00000004657 (-0.3049873755209) 0.9523563937787 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_13 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9928347214733:ℝ):ℂ) + ((0.1194956728799:ℝ):ℂ) * I)‖ ≤ 0.00000011763 := by
  have hl := lg_13
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.4288858469974 56.428885879997444 0.1197819 0.00000001762 0.9928347214733 0.1194956728799 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_14 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0601664670608:ℝ):ℂ) + (((-0.9981883570956):ℝ):ℂ) * I)‖ ≤ 0.00000013025 := by
  have hl := lg_14
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.059261234379284 58.059261267379328 (-1.5105935) 0.00000003024 0.0601664670608 (-0.9981883570956) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_15 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.993604693187):ℝ):ℂ) + (((-0.1129146280329):ℝ):ℂ) * I)‖ ≤ 0.00000015754 := by
  have hl := lg_15
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.577104407092206 59.57710444009225 (-3.0284367) 0.00000005753 (-0.993604693187) (-0.1129146280329) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_16 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2610452831803):ℝ):ℂ) + ((0.9653265562119:ℝ):ℂ) * I)‖ ≤ 0.00000013862 := by
  have hl := lg_16
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.9969518664 60.9969519104 1.8349012 0.00000003861 (-0.2610452831803) 0.9653265562119 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_17 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8770260781743:ℝ):ℂ) + ((0.4804427730772:ℝ):ℂ) * I)‖ ≤ 0.00000012545 := by
  have hl := lg_17
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.330693546361548 62.33069359036157 0.5011595 0.00000002544 0.8770260781743 0.4804427730772 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_18 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7273624849247:ℝ):ℂ) + (((-0.6862534630326):ℝ):ℂ) * I)‖ ≤ 0.00000011778 := by
  have hl := lg_18
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.588178656559216 63.58817868955926 (-0.7563256) 0.00000001777 0.7273624849247 (-0.6862534630326) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_19 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3662801343036):ℝ):ℂ) + (((-0.9305046282593):ℝ):ℂ) * I)‖ ≤ 0.00000014731 := by
  have hl := lg_19
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.777657524505266 64.777657557505332 (-1.9458045) 0.0000000473 (-0.3662801343036) (-0.9305046282593) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22_20 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9977338043496):ℝ):ℂ) + (((-0.0672848803277):ℝ):ℂ) * I)‖ ≤ 0.00000016753 := by
  have hl := lg_20
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.906109995312598 65.90611003931262 (-3.0742569) 0.00000006752 (-0.9977338043496) (-0.0672848803277) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
