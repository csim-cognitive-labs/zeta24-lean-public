/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Base
/-!
# Certificat (V2), côté b2left (b2), angles 1

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

lemma cs_b2left_v15p838_5 : ‖exp (-((((((15838:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9367618454716:ℝ):ℂ) + (((-0.3499674911597):ℝ):ℂ) * I)‖ ≤ 0.00000013603 := by
  have hl := lg_5
  refine (ecis_approx ((((15838:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.490277648897242142 25.49027766473525798 (-0.3575364) 0.00000003602 0.9367618454716 (-0.3499674911597) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p838_6 : ‖exp (-((((((15838:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9946432234617):ℝ):ℂ) + ((0.1033675846294:ℝ):ℂ) * I)‖ ≤ 0.00000014535 := by
  have hl := lg_6
  refine (ecis_approx ((((15838:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.377886465399901432 28.37788648123791727 3.0380401 0.00000004534 (-0.9946432234617) 0.1033675846294 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p838_7 : ‖exp (-((((((15838:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8272497262512:ℝ):ℂ) + ((0.5618343976808:ℝ):ℂ) * I)‖ ≤ 0.00000011246 := by
  have hl := lg_7
  refine (ecis_approx ((((15838:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.819324932504013636 30.819324948342045312 0.5966016 0.00000001245 0.8272497262512 0.5618343976808 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p838_8 : ‖exp (-((((((15838:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0525035747084:ℝ):ℂ) + (((-0.9986207361369):ℝ):ℂ) * I)‖ ≤ 0.00000011265 := by
  have hl := lg_8
  refine (ecis_approx ((((15838:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.9341951247742 32.9341951485312 (-1.5182686) 0.00000001264 0.0525035747084 (-0.9986207361369) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p838_9 : ‖exp (-((((((15838:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9708309867681):ℝ):ℂ) + ((0.2397648741073:ℝ):ℂ) * I)‖ ≤ 0.00000012039 := by
  have hl := lg_9
  refine (ecis_approx ((((15838:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.799642847617002864 34.79964286345503454 2.899469 0.00000002038 (-0.9708309867681) 0.2397648741073 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v15p838_10 : ‖exp (-((((((15838:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3335127602051:ℝ):ℂ) + ((0.9427455853943:ℝ):ℂ) * I)‖ ≤ 0.0000001526 := by
  have hl := lg_10
  refine (ecis_approx ((((15838:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.468342690488642142 36.46834271424565798 1.2307691 0.00000005259 0.3335127602051 0.9427455853943 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p259_2 : ‖exp (-((((((16259:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2708786855383:ℝ):ℂ) + ((0.9626134934235:ℝ):ℂ) * I)‖ ≤ 0.00000010988 := by
  have hl := lg_2
  refine (ecis_approx ((((16259:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.2698800044977 11.2698800126272 1.2964906 0.00000000987 0.2708786855383 0.9626134934235 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p259_3 : ‖exp (-((((((16259:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5510129744086:ℝ):ℂ) + ((0.8344966758672:ℝ):ℂ) * I)‖ ≤ 0.00000012433 := by
  have hl := lg_3
  refine (ecis_approx ((((16259:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.862337197228338476 17.862337205357854735 0.9872187 0.00000002432 0.5510129744086 0.8344966758672 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p259_4 : ‖exp (-((((((16259:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8532494754232):ℝ):ℂ) + ((0.5215029555181:ℝ):ℂ) * I)‖ ≤ 0.00000011974 := by
  have hl := lg_4
  refine (ecis_approx ((((16259:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.5397600089954 22.5397600252544 2.5929812 0.00000001973 (-0.8532494754232) 0.5215029555181 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p259_5 : ‖exp (-((((((16259:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5104315166982:ℝ):ℂ) + (((-0.8599184070371):ℝ):ℂ) * I)‖ ≤ 0.00000011892 := by
  have hl := lg_5
  refine (ecis_approx ((((16259:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.167851009813124131 26.16785102607214039 (-1.0351098) 0.00000001891 0.5104315166982 (-0.8599184070371) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p259_6 : ‖exp (-((((((16259:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6540400901827):ℝ):ℂ) + ((0.7564598868523:ℝ):ℂ) * I)‖ ≤ 0.00000013419 := by
  have hl := lg_6
  refine (ecis_approx ((((16259:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.132217201726038476 29.132217217985054735 2.2837093 0.00000003418 (-0.6540400901827) 0.7564598868523 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p259_7 : ‖exp (-((((((16259:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9753208816919:ℝ):ℂ) + (((-0.2207921595883):ℝ):ℂ) * I)‖ ≤ 0.00000013088 := by
  have hl := lg_7
  refine (ecis_approx ((((16259:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.638553105037426298 31.638553121296458816 (-0.2226266) 0.00000003087 0.9753208816919 (-0.2207921595883) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p259_8 : ‖exp (-((((((16259:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7331328733388):ℝ):ℂ) + (((-0.6800854284573):ℝ):ℂ) * I)‖ ≤ 0.00000012242 := by
  have hl := lg_8
  refine (ecis_approx ((((16259:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.8096400134931 33.8096400378816 (-2.3937135) 0.00000002241 (-0.7331328733388) (-0.6800854284573) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p259_9 : ‖exp (-((((((16259:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3927694040669):ℝ):ℂ) + ((0.9196369910056:ℝ):ℂ) * I)‖ ≤ 0.00000014864 := by
  have hl := lg_9
  refine (ecis_approx ((((16259:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.724674394456676952 35.72467441071570947 1.9744374 0.00000004863 (-0.3927694040669) 0.9196369910056 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p259_10 : ‖exp (-((((((16259:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9660340801577:ℝ):ℂ) + ((0.258414697674:ℝ):ℂ) * I)‖ ≤ 0.00000012878 := by
  have hl := lg_10
  refine (ecis_approx ((((16259:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.437731014310824131 37.43773103869934039 0.2613808 0.00000002877 0.9660340801577 0.258414697674 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p68_2 : ‖exp (-((((((16680:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5363620326395:ℝ):ℂ) + ((0.8439880152839:ℝ):ℂ) * I)‖ ≤ 0.00000014697 := by
  have hl := lg_2
  refine (ecis_approx ((((16680:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.561694967404 11.561694975744 1.0046756 0.00000004696 0.5363620326395 0.8439880152839 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p68_3 : ‖exp (-((((((16680:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8654728138141:ℝ):ℂ) + ((0.5009558948139:ℝ):ℂ) * I)‖ ≤ 0.00000015091 := by
  have hl := lg_3
  refine (ecis_approx ((((16680:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.32485297064817552 18.3248529789881922 0.5247029 0.0000000509 0.8654728138141 0.5009558948139 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p68_4 : ‖exp (-((((((16680:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4246316304224):ℝ):ℂ) + ((0.9053662123367:ℝ):ℂ) * I)‖ ≤ 0.00000012278 := by
  have hl := lg_4
  refine (ecis_approx ((((16680:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.123389934808 23.123389951488 2.0093513 0.00000002277 (-0.4246316304224) 0.9053662123367 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p68_5 : ‖exp (-((((((16680:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1414112771592):ℝ):ℂ) + (((-0.9899509334768):ℝ):ℂ) * I)‖ ≤ 0.000000158 := by
  have hl := lg_5
  refine (ecis_approx ((((16680:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.84542437072900612 26.8454243874090228 (-1.7126832) 0.00000005799 (-0.1414112771592) (-0.9899509334768) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p68_6 : ‖exp (-((((((16680:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0414058862885:ℝ):ℂ) + ((0.9991424085587:ℝ):ℂ) * I)‖ ≤ 0.00000011885 := by
  have hl := lg_6
  refine (ecis_approx ((((16680:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.88654793805217552 29.8865479547321922 1.5293786 0.00000001884 0.0414058862885 0.9991424085587 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p68_7 : ‖exp (-((((((16680:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.504619800019:ℝ):ℂ) + (((-0.8633416805812):ℝ):ℂ) * I)‖ ≤ 0.00000015834 := by
  have hl := lg_7
  refine (ecis_approx ((((16680:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.45778127757083896 32.45778129425087232 (-1.0418548) 0.00000005833 0.504619800019 (-0.8633416805812) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p68_8 : ‖exp (-((((((16680:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9918745168834):ℝ):ℂ) + ((0.1272200547414:ℝ):ℂ) * I)‖ ≤ 0.00000014088 := by
  have hl := lg_8
  refine (ecis_approx ((((16680:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.685084902212 34.685084927232 3.0140269 0.00000004087 (-0.9918745168834) 0.1272200547414 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p68_9 : ‖exp (-((((((16680:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4980862961897:ℝ):ℂ) + ((0.8671274655713:ℝ):ℂ) * I)‖ ≤ 0.00000011491 := by
  have hl := lg_9
  refine (ecis_approx ((((16680:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.64970594129635104 36.6497059579763844 1.0494059 0.0000000149 0.4980862961897 0.8671274655713 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v16p68_10 : ‖exp (-((((((16680:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7596591485507:ℝ):ℂ) + (((-0.6503214420755):ℝ):ℂ) * I)‖ ≤ 0.00000012009 := by
  have hl := lg_10
  refine (ecis_approx ((((16680:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.40711933813300612 38.4071193631530228 (-0.7080075) 0.00000002008 0.7596591485507 (-0.6503214420755) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v17p101_2 : ‖exp (-((((((17101:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7564940746004:ℝ):ℂ) + ((0.6540005467081:ℝ):ℂ) * I)‖ ≤ 0.00000012452 := by
  have hl := lg_2
  refine (ecis_approx ((((17101:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.8535099303103 11.8535099388608 0.7128607 0.00000002451 0.7564940746004 0.6540005467081 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v17p101_3 : ‖exp (-((((((17101:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.998066999148:ℝ):ℂ) + ((0.0621471255305:ℝ):ℂ) * I)‖ ≤ 0.00000013109 := by
  have hl := lg_3
  refine (ecis_approx ((((17101:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.787368744068012564 18.787368752618529665 0.0621872 0.00000003108 0.998066999148 0.0621471255305 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v17p101_4 : ‖exp (-((((((17101:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1445665698109:ℝ):ℂ) + ((0.9894950767402:ℝ):ℂ) * I)‖ ≤ 0.00000014902 := by
  have hl := lg_4
  refine (ecis_approx ((((17101:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.7070198606206 23.7070198777216 1.4257214 0.00000004901 0.1445665698109 0.9894950767402 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v17p101_5 : ‖exp (-((((((17101:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7307774419198):ℝ):ℂ) + (((-0.6826157999576):ℝ):ℂ) * I)‖ ≤ 0.00000012004 := by
  have hl := lg_5
  refine (ecis_approx ((((17101:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.522997731644888109 27.52299774874590521 (-2.3902565) 0.00000002003 (-0.7307774419198) (-0.6826157999576) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v17p663_2 : ‖exp (-((((((17663:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9481883692982:ℝ):ℂ) + ((0.3177086972803:ℝ):ℂ) * I)‖ ≤ 0.00000014013 := by
  have hl := lg_2
  refine (ecis_approx ((((17663:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.2430586456389 12.2430586544704 0.323312 0.00000004012 0.9481883692982 0.3177086972803 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v17p663_3 : ‖exp (-((((((17663:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.849777692126:ℝ):ℂ) + (((-0.5271412277227):ℝ):ℂ) * I)‖ ≤ 0.00000013746 := by
  have hl := lg_3
  refine (ecis_approx ((((17663:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.404788850153400732 19.404788858984918395 (-0.5552329) 0.00000003745 0.849777692126 (-0.5271412277227) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v17p663_4 : ‖exp (-((((((17663:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7981224275945:ℝ):ℂ) + ((0.6024953033599:ℝ):ℂ) * I)‖ ≤ 0.00000013746 := by
  have hl := lg_4
  refine (ecis_approx ((((17663:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.4861172912778 24.4861173089408 0.6466239 0.00000003745 0.7981224275945 0.6024953033599 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v17p663_5 : ‖exp (-((((((17663:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9882927038774):ℝ):ℂ) + ((0.1525697580571:ℝ):ℂ) * I)‖ ≤ 0.00000011992 := by
  have hl := lg_5
  refine (ecis_approx ((((17663:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.427501838140673567 28.42750185580369123 2.9884247 0.00000001991 (-0.9882927038774) 0.1525697580571 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p225_2 : ‖exp (-((((((18225:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9978071450673:ℝ):ℂ) + (((-0.0661883770205):ℝ):ℂ) * I)‖ ≤ 0.00000015341 := by
  have hl := lg_2
  refine (ecis_approx ((((18225:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.6326073609675 12.63260737008 (-0.0662368) 0.0000000534 0.9978071450673 (-0.0661883770205) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p225_3 : ‖exp (-((((((18225:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3877075628152:ℝ):ℂ) + (((-0.9217824286326):ℝ):ℂ) * I)‖ ≤ 0.00000014383 := by
  have hl := lg_3
  refine (ecis_approx ((((18225:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.0222089562387889 20.022208965351307125 (-1.172653) 0.00000004382 0.3877075628152 (-0.9217824286326) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p225_4 : ‖exp (-((((((18225:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9912382107034:ℝ):ℂ) + (((-0.1320863718991):ℝ):ℂ) * I)‖ ≤ 0.00000011146 := by
  have hl := lg_4
  refine (ecis_approx ((((18225:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.265214721935 25.26521474016 (-0.1324735) 0.00000001145 0.9912382107034 (-0.1320863718991) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p225_5 : ‖exp (-((((((18225:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4909015521596):ℝ):ℂ) + ((0.8712150515696:ℝ):ℂ) * I)‖ ≤ 0.00000012698 := by
  have hl := lg_5
  refine (ecis_approx ((((18225:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.332005944636459025 29.33200596286147725 2.0839206 0.00000002697 (-0.4909015521596) 0.8712150515696 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p787_2 : ‖exp (-((((((18787:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8979155534484:ℝ):ℂ) + (((-0.4401677621946):ℝ):ℂ) * I)‖ ≤ 0.00000013808 := by
  have hl := lg_2
  refine (ecis_approx ((((18787:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.0221560762961 13.0221560856896 (-0.4557855) 0.00000003807 0.8979155534484 (-0.4401677621946) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p787_3 : ‖exp (-((((((18787:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2175237708848):ℝ):ℂ) + (((-0.9760550236022):ℝ):ℂ) * I)‖ ≤ 0.00000015019 := by
  have hl := lg_3
  refine (ecis_approx ((((18787:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.639629062324177068 20.639629071717695855 (-1.7900731) 0.00000005018 (-0.2175237708848) (-0.9760550236022) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p787_4 : ‖exp (-((((((18787:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.612504761296:ℝ):ℂ) + (((-0.7904668983517):ℝ):ℂ) * I)‖ ≤ 0.00000014268 := by
  have hl := lg_4
  refine (ecis_approx ((((18787:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.0443121525922 26.0443121713792 (-0.9115709) 0.00000004267 0.612504761296 (-0.7904668983517) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p787_5 : ‖exp (-((((((18787:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3814642670973:ℝ):ℂ) + ((0.9243835853843:ℝ):ℂ) * I)‖ ≤ 0.00000013404 := by
  have hl := lg_5
  refine (ecis_approx ((((18787:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.236510051132244483 30.23651006991926327 1.1794165 0.00000003403 0.3814642670973 0.9243835853843 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p787_6 : ‖exp (-((((((18787:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6249459326388):ℝ):ℂ) + (((-0.7806680352518):ℝ):ℂ) * I)‖ ≤ 0.00000012152 := by
  have hl := lg_6
  refine (ecis_approx ((((18787:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.661785138620277068 33.661785157407295855 (-2.2458586) 0.00000002151 (-0.6249459326388) (-0.7806680352518) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p787_7 : ‖exp (-((((((18787:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4164148371467:ℝ):ℂ) + ((0.9091747265538:ℝ):ℂ) * I)‖ ≤ 0.00000013626 := by
  have hl := lg_7
  refine (ecis_approx ((((18787:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.557813960534973114 36.557813979322010688 1.1412979 0.00000003625 0.4164148371467 0.9091747265538 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p787_8 : ‖exp (-((((((18787:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2020395059925:ℝ):ℂ) + (((-0.9793773726293):ℝ):ℂ) * I)‖ ≤ 0.0000001142 := by
  have hl := lg_8
  refine (ecis_approx ((((18787:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.0664682288883 39.0664682570688 (-1.3673564) 0.00000001419 0.2020395059925 (-0.9793773726293) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p787_9 : ‖exp (-((((((18787:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9053667726517):ℝ):ℂ) + ((0.4246304356208:ℝ):ℂ) * I)‖ ≤ 0.00000012562 := by
  have hl := lg_9
  refine (ecis_approx ((((18787:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.279258124648354136 41.27925814343539171 2.703039 0.00000002561 (-0.9053667726517) 0.4246304356208 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v18p787_10 : ‖exp (-((((((18787:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7494065526995:ℝ):ℂ) + ((0.6621101258636:ℝ):ℂ) * I)‖ ≤ 0.00000012284 := by
  have hl := lg_10
  refine (ecis_approx ((((18787:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.258666127428344483 43.25866615560886327 0.723631 0.00000002283 0.7494065526995 0.6621101258636 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p208_2 : ‖exp (-((((((19208:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7333224211121:ℝ):ℂ) + (((-0.6798810386342):ℝ):ℂ) * I)‖ ≤ 0.00000013446 := by
  have hl := lg_2
  refine (ecis_approx ((((19208:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.3139710392024 13.3139710488064 (-0.7476004) 0.00000003445 0.7333224211121 (-0.6798810386342) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p208_3 : ‖exp (-((((((19208:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6301858690353):ℝ):ℂ) + (((-0.7764443125256):ℝ):ℂ) * I)‖ ≤ 0.00000012382 := by
  have hl := lg_3
  refine (ecis_approx ((((19208:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.102144835744014112 21.10214484534803332 (-2.2525889) 0.00000002381 (-0.6301858690353) (-0.7764443125256) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p208_4 : ‖exp (-((((((19208:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.075523446897:ℝ):ℂ) + (((-0.9971440261911):ℝ):ℂ) * I)‖ ≤ 0.00000015033 := by
  have hl := lg_4
  refine (ecis_approx ((((19208:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.6279420784048 26.6279420976128 (-1.4952009) 0.00000005032 0.075523446897 (-0.9971440261911) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p208_5 : ‖exp (-((((((19208:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8766974425992:ℝ):ℂ) + ((0.4810421958:ℝ):ℂ) * I)‖ ≤ 0.00000012386 := by
  have hl := lg_5
  refine (ecis_approx ((((19208:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.914083412048126472 30.91408343125614568 0.5018431 0.00000002385 0.8766974425992 0.4810421958 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p208_6 : ‖exp (-((((((19208:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9900191927022):ℝ):ℂ) + (((-0.1409325997572):ℝ):ℂ) * I)‖ ≤ 0.00000015827 := by
  have hl := lg_6
  refine (ecis_approx ((((19208:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.416115874946414112 34.41611589415443332 (-3.0001893) 0.00000005826 (-0.9900191927022) (-0.1409325997572) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p208_7 : ‖exp (-((((((19208:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9485823270375:ℝ):ℂ) + ((0.3165305180107:ℝ):ℂ) * I)‖ ≤ 0.00000011002 := by
  have hl := lg_7
  refine (ecis_approx ((((19208:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.377042133068385776 37.377042152276424192 0.3220697 0.00000001001 0.9485823270375 0.3165305180107 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p208_8 : ‖exp (-((((((19208:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6225562792643):ℝ):ℂ) + (((-0.7825750309936):ℝ):ℂ) * I)‖ ≤ 0.00000012549 := by
  have hl := lg_8
  refine (ecis_approx ((((19208:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.9419131176072 39.9419131464192 (-2.2428013) 0.00000002548 (-0.6225562792643) (-0.7825750309936) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p208_9 : ‖exp (-((((((19208:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.205731533907):ℝ):ℂ) + ((0.9786084691823:ℝ):ℂ) * I)‖ ≤ 0.00000014045 := by
  have hl := lg_9
  refine (ecis_approx ((((19208:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.204289671488028224 42.20428969069606664 1.7780075 0.00000004044 (-0.205731533907) 0.9786084691823 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p208_10 : ‖exp (-((((((19208:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.969953358897:ℝ):ℂ) + (((-0.2432909401611):ℝ):ℂ) * I)‖ ≤ 0.00000012982 := by
  have hl := lg_10
  refine (ecis_approx ((((19208:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.228054451250526472 44.22805448006254568 (-0.2457573) 0.00000002981 0.969953358897 (-0.2432909401611) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p629_2 : ‖exp (-((((((19629:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5067243322131:ℝ):ℂ) + (((-0.8621081435314):ℝ):ℂ) * I)‖ ≤ 0.00000011227 := by
  have hl := lg_2
  refine (ecis_approx ((((19629:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.6057860021087 13.6057860119232 (-1.0394154) 0.00000001226 0.5067243322131 (-0.8621081435314) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p629_3 : ‖exp (-((((((19629:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9104242104312):ℝ):ℂ) + (((-0.4136759080868):ℝ):ℂ) * I)‖ ≤ 0.00000011239 := by
  have hl := lg_3
  refine (ecis_approx ((((19629:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.564660609163851156 21.564660618978370785 (-2.7151047) 0.00000001238 (-0.9104242104312) (-0.4136759080868) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p629_4 : ‖exp (-((((((19629:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4864609022863):ℝ):ℂ) + (((-0.8737023466496):ℝ):ℂ) * I)‖ ≤ 0.00000012452 := by
  have hl := lg_4
  refine (ecis_approx ((((19629:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.2115720042174 27.2115720238464 (-2.0788308) 0.00000002451 (-0.4864609022863) (-0.8737023466496) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p629_5 : ‖exp (-((((((19629:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.98459914263:ℝ):ℂ) + (((-0.1748271384319):ℝ):ℂ) * I)‖ ≤ 0.00000015671 := by
  have hl := lg_5
  refine (ecis_approx ((((19629:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.591656772964008461 31.59165679259302809 (-0.1757302) 0.0000000567 0.98459914263 (-0.1748271384319) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p629_6 : ‖exp (-((((((19629:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.817967465143):ℝ):ℂ) + ((0.5752644834429:ℝ):ℂ) * I)‖ ≤ 0.00000013182 := by
  have hl := lg_6
  refine (ecis_approx ((((19629:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.170446611272551156 35.170446630901570785 2.5286652 0.00000003181 (-0.817967465143) 0.5752644834429 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p629_7 : ‖exp (-((((((19629:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.878941304873:ℝ):ℂ) + (((-0.4769299556414):ℝ):ℂ) * I)‖ ≤ 0.00000013749 := by
  have hl := lg_7
  refine (ecis_approx ((((19629:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.196270305601798438 38.196270325230837696 (-0.4971585) 0.00000003748 0.878941304873 (-0.4769299556414) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p629_8 : ‖exp (-((((((19629:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997274836215):ℝ):ℂ) + (((-0.0233443325059):ℝ):ℂ) * I)‖ ≤ 0.00000013677 := by
  have hl := lg_8
  refine (ecis_approx ((((19629:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.8173580063261 40.8173580357696 (-3.1182462) 0.00000003676 (-0.9997274836215) (-0.0233443325059) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p629_9 : ‖exp (-((((((19629:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6577444914304:ℝ):ℂ) + ((0.7532411194252:ℝ):ℂ) * I)‖ ≤ 0.00000013194 := by
  have hl := lg_9
  refine (ecis_approx ((((19629:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.129321218327702312 43.12932123795674157 0.8529759 0.00000003193 0.6577444914304 0.7532411194252 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v19p629_10 : ‖exp (-((((((19629:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3482004432944:ℝ):ℂ) + (((-0.93742010395):ℝ):ℂ) * I)‖ ≤ 0.00000015427 := by
  have hl := lg_10
  refine (ecis_approx ((((19629:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.197442775072708461 45.19744280451622809 (-1.2151456) 0.00000005426 0.3482004432944 (-0.93742010395) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_2 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2372809722585:ℝ):ℂ) + (((-0.9714410636802):ℝ):ℂ) * I)‖ ≤ 0.00000014936 := by
  have hl := lg_2
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.897600965015 13.89760097504 (-1.3312304) 0.00000004935 0.2372809722585 (-0.9714410636802) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_3 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993510667888):ℝ):ℂ) + ((0.0360200597591:ℝ):ℂ) * I)‖ ≤ 0.00000014615 := by
  have hl := lg_3
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.0271763825836882 22.02717639260870825 3.1055648 0.00000004614 (-0.9993510667888) 0.0360200597591 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_4 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8873954342783):ℝ):ℂ) + (((-0.4610090488472):ℝ):ℂ) * I)‖ ≤ 0.00000012138 := by
  have hl := lg_4
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.79520193003 27.79520195008 (-2.6624607) 0.00000002137 (-0.8873954342783) (-0.4610090488472) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_5 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6574976190033:ℝ):ℂ) + (((-0.753456621847):ℝ):ℂ) * I)‖ ≤ 0.00000011805 := by
  have hl := lg_5
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.26923013387989045 32.2692301539299105 (-0.8533036) 0.00000001804 0.6574976190033 (-0.753456621847) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_6 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2021357253285):ℝ):ℂ) + ((0.979357518246:ℝ):ℂ) * I)‖ ≤ 0.00000012459 := by
  have hl := lg_6
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.9247773475986882 35.92477736764870825 1.7743345 0.00000002458 (-0.2021357253285) 0.979357518246 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_7 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2516741790086:ℝ):ℂ) + (((-0.9678120208079):ℝ):ℂ) * I)‖ ≤ 0.00000015512 := by
  have hl := lg_7
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.0154984781352111 39.0154984981852512 (-1.3163866) 0.00000005511 0.2516741790086 (-0.9678120208079) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_8 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6584051668571):ℝ):ℂ) + ((0.7526636939816:ℝ):ℂ) * I)‖ ≤ 0.00000015523 := by
  have hl := lg_8
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.692802895045 41.69280292512 2.2894942 0.00000005522 (-0.6584051668571) 0.7526636939816 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_9 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9974051182667:ℝ):ℂ) + (((-0.0719932639581):ℝ):ℂ) * I)‖ ≤ 0.00000013498 := by
  have hl := lg_9
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.0543527651673764 44.0543527852174165 (-0.0720556) 0.00000003497 0.9974051182667 (-0.0719932639581) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_10 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5759270278685):ℝ):ℂ) + (((-0.8175011061523):ℝ):ℂ) * I)‖ ≤ 0.00000015138 := by
  have hl := lg_10
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.16683109889489045 46.1668311289699105 (-2.184534) 0.00000005137 (-0.5759270278685) (-0.8175011061523) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_11 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5784978265485):ℝ):ℂ) + ((0.815683924488:ℝ):ℂ) * I)‖ ≤ 0.00000015348 := by
  have hl := lg_11
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.07780020397158665 48.07780023404662675 2.1876822 0.00000005347 (-0.5784978265485) 0.815683924488 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_12 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9034251478145:ℝ):ℂ) + ((0.428745848139:ℝ):ℂ) * I)‖ ≤ 0.00000014484 := by
  have hl := lg_12
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.8223783126136882 49.82237834268870825 0.4431041 0.00000004483 0.9034251478145 0.428745848139 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_13 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3977324947942:ℝ):ℂ) + (((-0.9175014237508):ℝ):ℂ) * I)‖ ≤ 0.00000015598 := by
  have hl := lg_13
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.427234601468085 51.4272346315431251 (-1.1617522) 0.00000005597 0.3977324947942 (-0.9175014237508) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_14 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8804548450221):ℝ):ℂ) + (((-0.474130009365):ℝ):ℂ) * I)‖ ≤ 0.0000001158 := by
  have hl := lg_14
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.9130994431502111 52.9130994732252512 (-2.647617) 0.00000001579 (-0.8804548450221) (-0.474130009365) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p05_15 : ‖exp (-((((((20050:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6299313944017):ℝ):ℂ) + ((0.7766507827411:ℝ):ℂ) * I)‖ ≤ 0.00000014817 := by
  have hl := lg_15
  refine (ecis_approx ((((20050:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.29640651646357865 54.29640654653861875 2.2522612 0.00000004816 (-0.6299313944017) 0.7766507827411 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_2 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0212230332689:ℝ):ℂ) + (((-0.9997747660642):ℝ):ℂ) * I)‖ ≤ 0.00000012265 := by
  have hl := lg_2
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.1159423268095 14.115942336992 (-1.5495717) 0.00000002264 0.0212230332689 (-0.9997747660642) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_3 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9278871403617):ℝ):ℂ) + ((0.3728611733549:ℝ):ℂ) * I)‖ ≤ 0.00000013491 := by
  have hl := lg_3
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.37323925343225986 22.373239263614780225 2.759502 0.0000000349 (-0.9278871403617) 0.3728611733549 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_4 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9990991654343):ℝ):ℂ) + (((-0.042436505975):ℝ):ℂ) * I)‖ ≤ 0.00000014528 := by
  have hl := lg_4
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.231884653619 28.231884673984 (-3.0991434) 0.00000004527 (-0.9990991654343) (-0.042436505975) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_5 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2089681805417:ℝ):ℂ) + (((-0.9779224404425):ℝ):ℂ) * I)‖ ≤ 0.00000015978 := by
  have hl := lg_5
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.776203076132866285 32.77620309649788665 (-1.3602766) 0.00000005977 0.2089681805417 (-0.9779224404425) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_6 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3530846127971:ℝ):ℂ) + ((0.9355913938285:ℝ):ℂ) * I)‖ ≤ 0.00000015754 := by
  have hl := lg_6
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.48918158024175986 36.489181600606780225 1.2099303 0.00000005753 0.3530846127971 0.9355913938285 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_7 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3509186607499):ℝ):ℂ) + (((-0.9364059448418):ℝ):ℂ) * I)‖ ≤ 0.00000015223 := by
  have hl := lg_7
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.62846017492386903 39.62846019528890976 (-1.9293483) 0.00000005222 (-0.3509186607499) (-0.9364059448418) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_8 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0636308557698):ℝ):ℂ) + ((0.9979735037533:ℝ):ℂ) * I)‖ ≤ 0.00000016073 := by
  have hl := lg_8
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.3478269804285 42.347827010976 1.6344702 0.00000006072 (-0.0636308557698) 0.9979735037533 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_9 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.721949026459:ℝ):ℂ) + (((-0.691946242995):ℝ):ℂ) * I)‖ ≤ 0.00000014341 := by
  have hl := lg_9
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.74647850686451972 44.74647852722956045 (-0.7641814) 0.0000000434 0.721949026459 (-0.691946242995) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_10 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9732672403613):ℝ):ℂ) + (((-0.22967559416):ℝ):ℂ) * I)‖ ≤ 0.00000014733 := by
  have hl := lg_10
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.892145402942366285 46.89214543348988665 (-2.9098483) 0.00000004732 (-0.9732672403613) (-0.22967559416) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_11 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1380092288512:ℝ):ℂ) + ((0.9904309429495:ℝ):ℂ) * I)‖ ≤ 0.00000014279 := by
  have hl := lg_11
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.833137214657424545 48.833137245204965275 1.4323452 0.00000004278 0.1380092288512 0.9904309429495 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_12 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9428741600658:ℝ):ℂ) + (((-0.3331490931702):ℝ):ℂ) * I)‖ ≤ 0.0000001504 := by
  have hl := lg_12
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.60512390705125986 50.605123937598780225 (-0.3396415) 0.00000005039 0.9428741600658 (-0.3331490931702) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_13 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3884186452705):ℝ):ℂ) + (((-0.9214830199212):ℝ):ℂ) * I)‖ ≤ 0.00000012195 := by
  have hl := lg_13
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.2351936488228205 52.23519367937036123 (-1.9697112) 0.00000002194 (-0.3884186452705) (-0.9214830199212) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_14 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9436425573206):ℝ):ℂ) + ((0.3309663484794:ℝ):ℂ) * I)‖ ≤ 0.0000001629 := by
  have hl := lg_14
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.74440250173336903 53.74440253228090976 2.8042652 0.00000006289 (-0.9436425573206) 0.3309663484794 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p365_15 : ‖exp (-((((((20365:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1707304211942:ℝ):ℂ) + ((0.9853177778153:ℝ):ℂ) * I)‖ ≤ 0.00000013507 := by
  have hl := lg_15
  refine (ecis_approx ((((20365:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.149442329565126145 55.149442360112666875 1.3992254 0.00000003506 0.1707304211942 0.9853177778153 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_2 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1418778253115):ℝ):ℂ) + (((-0.9898841763986):ℝ):ℂ) * I)‖ ≤ 0.00000015301 := by
  have hl := lg_2
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.2795250613603 14.2795250716608 (-1.7131545) 0.000000053 (-0.1418778253115) (-0.9898841763986) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_3 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8012809437943):ℝ):ℂ) + ((0.5982882658571:ℝ):ℂ) * I)‖ ≤ 0.00000013509 := by
  have hl := lg_3
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.632511753496586564 22.632511763797107165 2.5002295 0.00000003508 (-0.8012809437943) 0.5982882658571 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_4 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9597413913555):ℝ):ℂ) + ((0.2808851393127:ℝ):ℂ) * I)‖ ≤ 0.00000011319 := by
  have hl := lg_4
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.5590501227206 28.5590501433216 2.8568764 0.00000001318 (-0.9597413913555) 0.2808851393127 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_5 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1684998632627):ℝ):ℂ) + (((-0.9857016770198):ℝ):ℂ) * I)‖ ≤ 0.00000011257 := by
  have hl := lg_5
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.156030423344619609 33.15603044394564021 (-1.7401039) 0.00000001256 (-0.1684998632627) (-0.9857016770198) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_6 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7059200850951:ℝ):ℂ) + ((0.708291489049:ℝ):ℂ) * I)‖ ≤ 0.00000012824 := by
  have hl := lg_6
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.912036814856886564 36.912036835457907165 0.787075 0.00000002823 0.7059200850951 0.708291489049 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_7 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7296341299873):ℝ):ℂ) + (((-0.6838377266051):ℝ):ℂ) * I)‖ ≤ 0.00000014752 := by
  have hl := lg_7
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.087694969978228622 40.087694990579269824 (-2.3885831) 0.00000004751 (-0.7296341299873) (-0.6838377266051) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_8 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.41420968537:ℝ):ℂ) + ((0.9101814854993:ℝ):ℂ) * I)‖ ≤ 0.00000016474 := by
  have hl := lg_8
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.8385751840809 42.8385752149824 1.143722 0.00000006473 0.41420968537 0.9101814854993 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_9 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2841022128131:ℝ):ℂ) + (((-0.9587939990815):ℝ):ℂ) * I)‖ ≤ 0.00000014328 := by
  have hl := lg_9
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.265023506993173128 45.26502352759421433 (-1.2827264) 0.00000004327 0.2841022128131 (-0.9587939990815) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_10 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9518241269554):ℝ):ℂ) + ((0.306644470254:ℝ):ℂ) * I)‖ ≤ 0.00000015818 := by
  have hl := lg_10
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.435555484704919609 47.43555551560644021 2.829927 0.00000005817 (-0.9518241269554) 0.306644470254 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_11 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6475420185204:ℝ):ℂ) + ((0.7620297463029:ℝ):ℂ) * I)‖ ≤ 0.0000001586 := by
  have hl := lg_11
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.399040498853798333 49.399040529755339535 0.8664419 0.00000005859 0.6475420185204 0.7620297463029 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_12 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6009722106977:ℝ):ℂ) + (((-0.7992699180935):ℝ):ℂ) * I)‖ ≤ 0.0000001497 := by
  have hl := lg_12
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.191561876217186564 51.191561907118707165 (-0.9260794) 0.00000004969 0.6009722106977 (-0.7992699180935) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_13 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8437558917043):ℝ):ℂ) + (((-0.5367271142249):ℝ):ℂ) * I)‖ ≤ 0.00000016045 := by
  have hl := lg_13
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.8405216969997017 52.840521727901242902 (-2.5750393) 0.00000006044 (-0.8437558917043) (-0.5367271142249) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_14 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5734012352884):ℝ):ℂ) + ((0.8192746934695:ℝ):ℂ) * I)‖ ≤ 0.00000013329 := by
  have hl := lg_14
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.367220031338528622 54.367220062240069824 2.1814477 0.00000003328 (-0.5734012352884) 0.8192746934695 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_15 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7247494764904:ℝ):ℂ) + ((0.6890124790793:ℝ):ℂ) * I)‖ ≤ 0.00000014314 := by
  have hl := lg_15
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.788542176841206173 55.788542207742747375 0.7601256 0.00000004313 0.7247494764904 0.6890124790793 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_16 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8422070807638:ℝ):ℂ) + (((-0.5391541830603):ℝ):ℂ) * I)‖ ≤ 0.00000012204 := by
  have hl := lg_16
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.1181002454412 57.1181002866432 (-0.5694325) 0.00000002203 0.8422070807638 (-0.5391541830603) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_17 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2450429308927):ℝ):ℂ) + (((-0.9695122289164):ℝ):ℂ) * I)‖ ≤ 0.00000015608 := by
  have hl := lg_17
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.367028079481556834 58.367028120683577435 (-1.8183603) 0.00000005607 (-0.2450429308927) (-0.9695122289164) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_18 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9894027975434):ℝ):ℂ) + (((-0.1451967761796):ℝ):ℂ) * I)‖ ≤ 0.00000013465 := by
  have hl := lg_18
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.544548568353473128 59.54454859925501433 (-2.9958808) 0.00000003464 (-0.9894027975434) (-0.1451967761796) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_19 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5668435878599):ℝ):ℂ) + ((0.8238254347205:ℝ):ℂ) * I)‖ ≤ 0.00000015286 := by
  have hl := lg_19
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.658387393742408403 60.658387424643970206 2.1734657 0.00000005285 (-0.5668435878599) 0.8238254347205 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p601_20 : ‖exp (-((((((20601:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4385852462133:ℝ):ℂ) + ((0.898689591463:ℝ):ℂ) * I)‖ ≤ 0.00000012575 := by
  have hl := lg_20
  refine (ecis_approx ((((20601:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.715080546065219609 61.71508058726724021 1.1167725 0.00000002574 0.4385852462133 0.898689591463 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_2 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2619528642039):ℝ):ℂ) + (((-0.9650806686148):ℝ):ℂ) * I)‖ ≤ 0.00000010832 := by
  have hl := lg_2
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.4022121122734 14.4022121226624 (-1.8358415) 0.00000000831 (-0.2619528642039) (-0.9650806686148) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_3 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6705714087953):ℝ):ℂ) + ((0.7418449876402:ℝ):ℂ) * I)‖ ≤ 0.00000011023 := by
  have hl := lg_3
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.826966128544831592 22.82696613893385237 2.3057751 0.00000001022 (-0.6705714087953) 0.7418449876402 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_4 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8627613902196):ℝ):ℂ) + ((0.505611296812:ℝ):ℂ) * I)‖ ≤ 0.00000011137 := by
  have hl := lg_4
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.8044242245468 28.8044242453248 2.6115023 0.00000001136 (-0.8627613902196) 0.505611296812 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_5 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4387238606388):ℝ):ℂ) + (((-0.8986219305704):ℝ):ℂ) * I)‖ ≤ 0.00000011865 := by
  have hl := lg_5
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.440900933753434602 33.44090095453145538 (-2.0249744) 0.00000001864 (-0.4387238606388) (-0.8986219305704) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_6 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8915983578792:ℝ):ℂ) + ((0.4528270842464:ℝ):ℂ) * I)‖ ≤ 0.00000011853 := by
  have hl := lg_6
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.229178240818231592 37.22917826159625237 0.4699336 0.00000001852 0.8915983578792 0.4528270842464 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_7 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9176845510478):ℝ):ℂ) + (((-0.3973097842098):ℝ):ℂ) * I)‖ ≤ 0.00000014398 := by
  have hl := lg_7
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.432121066268998316 40.432121087047039872 (-2.7330092) 0.00000004397 (-0.9176845510478) (-0.3973097842098) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_8 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7139585057287:ℝ):ℂ) + ((0.7001880119637:ℝ):ℂ) * I)‖ ≤ 0.00000011775 := by
  have hl := lg_8
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.2066363368202 43.2066363679872 0.7756608 0.00000001774 0.7139585057287 0.7001880119637 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_9 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1006679642634):ℝ):ℂ) + (((-0.9949200776799):ℝ):ℂ) * I)‖ ≤ 0.00000012763 := by
  have hl := lg_9
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.653932257089663184 45.65393227786770474 (-1.6716351) 0.00000002762 (-0.1006679642634) (-0.9949200776799) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_10 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7523176769651):ℝ):ℂ) + ((0.6588005106946:ℝ):ℂ) * I)‖ ≤ 0.00000011977 := by
  have hl := lg_10
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.843113046026834602 47.84311307719385538 2.4223694 0.00000001976 (-0.7523176769651) 0.6588005106946 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_11 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9038917729123:ℝ):ℂ) + ((0.4277612217831:ℝ):ℂ) * I)‖ ≤ 0.00000013575 := by
  have hl := lg_11
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.823467962001078674 49.82346799316812023 0.4420145 0.00000003574 0.9038917729123 0.4277612217831 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_12 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2034579216659:ℝ):ℂ) + (((-0.979083691066):ℝ):ℂ) * I)‖ ≤ 0.00000012684 := by
  have hl := lg_12
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.631390353091631592 51.63139038425865237 (-1.3659079) 0.00000002683 0.2034579216659 (-0.979083691066) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_13 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9936721058637):ℝ):ℂ) + (((-0.1123198360686):ℝ):ℂ) * I)‖ ≤ 0.00000012432 := by
  have hl := lg_13
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.2945177331323626 53.294517764299404156 (-3.0290353) 0.00000002431 (-0.9936721058637) (-0.1123198360686) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_14 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1430458885649):ℝ):ℂ) + ((0.9897160571417:ℝ):ℂ) * I)‖ ≤ 0.00000014511 := by
  have hl := lg_14
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.834333178542398316 54.834333209709439872 1.7143346 0.0000000451 (-0.1430458885649) 0.9897160571417 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_15 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9608338522905:ℝ):ℂ) + ((0.2771250769827:ℝ):ℂ) * I)‖ ≤ 0.00000012886 := by
  have hl := lg_15
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.267867062298266194 56.26786709346530775 0.2808007 0.00000002885 0.9608338522905 0.2771250769827 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_16 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4887144392443:ℝ):ℂ) + (((-0.8724438072874):ℝ):ℂ) * I)‖ ≤ 0.00000012605 := by
  have hl := lg_16
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.6088484490936 57.6088484906496 (-1.0601807) 0.00000002604 0.4887144392443 (-0.8724438072874) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_17 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6809380556499):ℝ):ℂ) + (((-0.7323410164308):ℝ):ℂ) * I)‖ ≤ 0.00000012344 := by
  have hl := lg_17
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.868506841195465652 58.86850688275148643 (-2.3198391) 0.00000002343 (-0.6809380556499) (-0.7323410164308) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_18 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.93380786959):ℝ):ℂ) + ((0.3577748768781:ℝ):ℂ) * I)‖ ≤ 0.00000012875 := by
  have hl := lg_18
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.056144369363063184 60.05614440053010474 2.7757087 0.00000002874 (-0.93380786959) 0.3577748768781 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_19 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0814134670761):ℝ):ℂ) + ((0.9966804138631:ℝ):ℂ) * I)‖ ≤ 0.0000001523 := by
  have hl := lg_19
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.179553092916837134 61.179553124083899468 1.6523 0.00000005229 (-0.0814134670761) 0.9966804138631 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p778_20 : ‖exp (-((((((20778:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8328674076378:ℝ):ℂ) + ((0.553472565982:ℝ):ℂ) * I)‖ ≤ 0.00000012808 := by
  have hl := lg_20
  refine (ecis_approx ((((20778:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.245325158300234602 62.24532519985625538 0.5865279 0.00000002807 0.8328674076378 0.553472565982 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_2 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3490344652416):ℝ):ℂ) + (((-0.937109887938):ℝ):ℂ) * I)‖ ≤ 0.00000013618 := by
  have hl := lg_2
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.493707540073 14.493707550528 (-1.9273369) 0.00000003617 (-0.3490344652416) (-0.937109887938) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_3 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5563294244993):ℝ):ℂ) + ((0.8309618351207:ℝ):ℂ) * I)‖ ≤ 0.00000013237 := by
  have hl := lg_3
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.97198295061470924 22.97198296106973015 2.1607583 0.00000003236 (-0.5563294244993) 0.8309618351207 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_4 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7563498140277):ℝ):ℂ) + ((0.654167378264:ℝ):ℂ) * I)‖ ≤ 0.00000015577 := by
  have hl := lg_4
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.987415080146 28.987415101056 2.4285114 0.00000005576 (-0.7563498140277) 0.654167378264 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_5 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6183361716661):ℝ):ℂ) + (((-0.785913722234):ℝ):ℂ) * I)‖ ≤ 0.00000012315 := by
  have hl := lg_5
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.65334673812611019 33.6533467590361311 (-2.2374202) 0.00000002314 (-0.6183361716661) (-0.785913722234) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_6 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9728807185058:ℝ):ℂ) + ((0.231307387603:ℝ):ℂ) * I)‖ ≤ 0.0000001524 := by
  have hl := lg_6
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.46569049068770924 37.46569051159773015 0.2334213 0.00000005239 0.9728807185058 0.231307387603 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_7 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9885120899679):ℝ):ℂ) + (((-0.1511418128648):ℝ):ℂ) * I)‖ ≤ 0.00000013722 := by
  have hl := lg_7
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.68898120587567402 40.68898122678571584 (-2.9898694) 0.00000003721 (-0.9885120899679) (-0.1511418128648) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_8 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8770188714341:ℝ):ℂ) + ((0.4804559284144:ℝ):ℂ) * I)‖ ≤ 0.00000013005 := by
  have hl := lg_8
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.481122620219 43.481122651584 0.5011745 0.00000003004 0.8770188714341 0.4804559284144 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_9 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3809952286913):ℝ):ℂ) + (((-0.9245770036679):ℝ):ℂ) * I)‖ ≤ 0.00000014904 := by
  have hl := lg_9
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.94396590122941848 45.9439659221394603 (-1.9616688) 0.00000004903 (-0.3809952286913) (-0.9245770036679) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_10 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5206668790327):ℝ):ℂ) + ((0.8537599200426:ℝ):ℂ) * I)‖ ≤ 0.00000015214 := by
  have hl := lg_10
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.14705427819911019 48.1470543095641311 2.1184282 0.00000005213 (-0.5206668790327) 0.8537599200426 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_11 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9921361696264:ℝ):ℂ) + ((0.125163177169:ℝ):ℂ) * I)‖ ≤ 0.00000011954 := by
  have hl := lg_11
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.13999013790752503 50.13999016927256685 0.1254923 0.00000001953 0.9921361696264 0.125163177169 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_12 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1228084612513):ℝ):ℂ) + (((-0.9924303914354):ℝ):ℂ) * I)‖ ≤ 0.00000012669 := by
  have hl := lg_12
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.95939803076070924 51.95939806212573015 (-1.6939156) 0.00000002668 (-0.1228084612513) (-0.9924303914354) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_13 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9745669382091):ℝ):ℂ) + ((0.2240965922461:ℝ):ℂ) * I)‖ ≤ 0.00000011642 := by
  have hl := lg_13
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.633091048214347 53.63309107957938882 2.9155767 0.00000001641 (-0.9745669382091) 0.2240965922461 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_14 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2033883083013:ℝ):ℂ) + ((0.9790981544494:ℝ):ℂ) * I)‖ ≤ 0.00000011868 := by
  have hl := lg_14
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.18268874594867402 55.18268877731371584 1.365979 0.00000001867 0.2033883083013 0.9790981544494 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_15 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9970629154156:ℝ):ℂ) + (((-0.0765868311321):ℝ):ℂ) * I)‖ ≤ 0.0000001555 := by
  have hl := lg_15
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.62532968874081943 56.62532972010586125 (-0.0766619) 0.00000005549 0.9970629154156 (-0.0765868311321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_16 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1441301884385:ℝ):ℂ) + (((-0.9895587343764):ℝ):ℂ) * I)‖ ≤ 0.00000013751 := by
  have hl := lg_16
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.974830160292 57.974830202112 (-1.4261624) 0.0000000375 0.1441301884385 (-0.9895587343764) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_17 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9014151156064):ℝ):ℂ) + (((-0.4329558744701):ℝ):ℂ) * I)‖ ≤ 0.00000016216 := by
  have hl := lg_17
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.24249100247363494 59.24249104429365585 (-2.6938233) 0.00000006215 (-0.9014151156064) (-0.4329558744701) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_18 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7334497815093):ℝ):ℂ) + ((0.6797436413634:ℝ):ℂ) * I)‖ ≤ 0.00000013051 := by
  have hl := lg_18
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.43767344130241848 60.4376734726674603 2.3941796 0.0000000305 (-0.7334497815093) 0.6797436413634 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_19 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3023550003921:ℝ):ℂ) + ((0.9531953911648:ℝ):ℂ) * I)‖ ≤ 0.00000013375 := by
  have hl := lg_19
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.56821903806386873 61.56821906942893146 1.263634 0.00000003374 0.3023550003921 0.9531953911648 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v20p91_20 : ‖exp (-((((((20910:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9817975676872:ℝ):ℂ) + ((0.1899303453464:ℝ):ℂ) * I)‖ ≤ 0.00000015354 := by
  have hl := lg_20
  refine (ecis_approx ((((20910:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.64076181827211019 62.6407618600921311 0.1910912 0.00000005353 0.9817975676872 0.1899303453464 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_2 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4331962842238):ℝ):ℂ) + (((-0.9012996057531):ℝ):ℂ) * I)‖ ≤ 0.0000001465 := by
  have hl := lg_2
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.5852029678726 14.5852029783936 (-2.0188324) 0.00000004649 (-0.4331962842238) (-0.9012996057531) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_3 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4304083924042):ℝ):ℂ) + ((0.9026342646632:ℝ):ℂ) * I)‖ ≤ 0.0000001545 := by
  have hl := lg_3
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.116999772684586888 23.11699978320560793 2.0157415 0.00000005449 (-0.4304083924042) 0.9026342646632 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_4 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6246820311498):ℝ):ℂ) + ((0.7808792223797:ℝ):ℂ) * I)‖ ≤ 0.0000001209 := by
  have hl := lg_4
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.1704059357452 29.1704059567872 2.2455206 0.00000002089 (-0.6246820311498) 0.7808792223797 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_5 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7701457866552):ℝ):ℂ) + (((-0.6378679073743):ℝ):ℂ) * I)‖ ≤ 0.00000012766 := by
  have hl := lg_5
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.865792542498785778 33.86579256354080682 (-2.449866) 0.00000002765 (-0.7701457866552) (-0.6378679073743) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_6 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999952231724:ℝ):ℂ) + (((-0.0030908950784):ℝ):ℂ) * I)‖ ≤ 0.00000011854 := by
  have hl := lg_6
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.702202740557186888 37.70220276159920793 (-0.0030909) 0.00000001853 0.9999952231724 (-0.0030908950784) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_7 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9944782099869):ℝ):ℂ) + ((0.1049432675039:ℝ):ℂ) * I)‖ ≤ 0.00000011628 := by
  have hl := lg_7
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.945841345482349724 40.945841366524391808 3.0364558 0.00000001627 (-0.9944782099869) 0.1049432675039 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_8 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9744160699967:ℝ):ℂ) + ((0.224751690833:ℝ):ℂ) * I)‖ ≤ 0.00000014665 := by
  have hl := lg_8
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.7556089036178 43.7556089351808 0.2266882 0.00000004664 0.9744160699967 0.224751690833 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_9 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6294973036165):ℝ):ℂ) + (((-0.7770026671285):ℝ):ℂ) * I)‖ ≤ 0.00000011617 := by
  have hl := lg_9
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.233999545369173776 46.23399956641121586 (-2.2517024) 0.00000001616 (-0.6294973036165) (-0.7770026671285) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_10 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2412857934003):ℝ):ℂ) + ((0.9704541029343:ℝ):ℂ) * I)‖ ≤ 0.00000014708 := by
  have hl := lg_10
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.450995510371385778 48.45099554193440682 1.8144869 0.00000004707 (-0.2412857934003) 0.9704541029343 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_11 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9818092085728:ℝ):ℂ) + (((-0.1898701607987):ℝ):ℂ) * I)‖ ≤ 0.00000014364 := by
  have hl := lg_11
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.456512313813971386 50.45651234537701347 (-0.1910299) 0.00000004363 0.9818092085728 (-0.1898701607987) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_12 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4359800374354):ℝ):ℂ) + (((-0.8999563361373):ℝ):ℂ) * I)‖ ≤ 0.00000014902 := by
  have hl := lg_12
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.287405708429786888 52.28740573999280793 (-2.0219233) 0.00000004901 (-0.4359800374354) (-0.8999563361373) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_13 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8448084492781):ℝ):ℂ) + ((0.5350688590804:ℝ):ℂ) * I)‖ ≤ 0.00000013026 := by
  have hl := lg_13
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.9716643632963314 53.971664394859373484 2.5770034 0.00000003025 (-0.8448084492781) 0.5350688590804 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_14 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5253895912259:ℝ):ℂ) + ((0.8508617851517:ℝ):ℂ) * I)‖ ≤ 0.00000015128 := by
  have hl := lg_14
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.531044313354949724 55.531044344917991808 1.0176234 0.00000005127 0.5253895912259 0.8508617851517 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_15 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9072385974389:ℝ):ℂ) + (((-0.4206163659643):ℝ):ℂ) * I)‖ ≤ 0.00000014945 := by
  have hl := lg_15
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.982792315183372666 56.98279234674641475 (-0.4341246) 0.00000004944 0.9072385974389 (-0.4206163659643) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_16 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2195447129097):ℝ):ℂ) + (((-0.9756024390254):ℝ):ℂ) * I)‖ ≤ 0.00000014897 := by
  have hl := lg_16
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.3408118714904 58.3408119135744 (-1.7921441) 0.00000004896 (-0.2195447129097) (-0.9756024390254) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_17 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9972791027074):ℝ):ℂ) + (((-0.0737183205068):ℝ):ℂ) * I)‖ ≤ 0.00000014123 := by
  have hl := lg_17
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.616475163751804228 59.61647520583582527 (-3.0678074) 0.00000004122 (-0.9972791027074) (-0.0737183205068) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_18 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4276162982152):ℝ):ℂ) + ((0.9039603428784:ℝ):ℂ) * I)‖ ≤ 0.00000015857 := by
  have hl := lg_18
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.819202513241773776 60.81920254480481586 2.0126505 0.00000005856 (-0.4276162982152) 0.9039603428784 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_19 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6410213424749:ℝ):ℂ) + ((0.7675230540457:ℝ):ℂ) * I)‖ ≤ 0.00000014299 := by
  have hl := lg_19
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.956884983210900326 61.956885014773963452 0.8749681 0.00000004298 0.6410213424749 0.7675230540457 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p042_20 : ‖exp (-((((((21042:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9791940298085:ℝ):ℂ) + (((-0.2029262230157):ℝ):ℂ) * I)‖ ≤ 0.00000014855 := by
  have hl := lg_20
  refine (ecis_approx ((((21042:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.036198478243985778 63.03619852032800682 (-0.2043454) 0.00000004854 0.9791940298085 (-0.2029262230157) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_2 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5137340757373):ℝ):ℂ) + (((-0.8579494736985):ℝ):ℂ) * I)‖ ≤ 0.0000001187 := by
  have hl := lg_2
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.6766983956722 14.6766984062592 (-2.1103278) 0.00000001869 (-0.5137340757373) (-0.8579494736985) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_3 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2954516826769):ℝ):ℂ) + ((0.9553576833845:ℝ):ℂ) * I)‖ ≤ 0.00000013398 := by
  have hl := lg_3
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.262016594754464536 23.26201660534148571 1.8707246 0.00000003397 (-0.2954516826769) 0.9553576833845 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_4 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4721545925233):ℝ):ℂ) + ((0.8815157631908:ℝ):ℂ) * I)‖ ≤ 0.00000014457 := by
  have hl := lg_4
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.3533967913444 29.3533968125184 2.0625297 0.00000004456 (-0.4721545925233) 0.8815157631908 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_5 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8873267801938):ℝ):ℂ) + (((-0.4611411769164):ℝ):ℂ) * I)‖ ≤ 0.00000013216 := by
  have hl := lg_5
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.078238346871461366 34.07823836804548254 (-2.6623118) 0.00000003215 (-0.8873267801938) (-0.4611411769164) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_6 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.971432218783:ℝ):ℂ) + (((-0.2373171808157):ℝ):ℂ) * I)‖ ≤ 0.00000015267 := by
  have hl := lg_6
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.938714990426664536 37.93871501160068571 (-0.2396032) 0.00000005266 0.971432218783 (-0.2373171808157) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_7 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9351914826988):ℝ):ℂ) + ((0.3541424720619:ℝ):ℂ) * I)‖ ≤ 0.00000015602 := by
  have hl := lg_7
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.202701485089025428 41.202701506263067776 2.7795957 0.00000005601 (-0.9351914826988) 0.3541424720619 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_8 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9988578882876:ℝ):ℂ) + (((-0.0477799016908):ℝ):ℂ) * I)‖ ≤ 0.00000016326 := by
  have hl := lg_8
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.0300951870166 44.0300952187776 (-0.0477981) 0.00000006325 0.9988578882876 (-0.0477799016908) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_9 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8254165458879):ℝ):ℂ) + (((-0.5645241586631):ℝ):ℂ) * I)‖ ≤ 0.00000016044 := by
  have hl := lg_9
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.524033189508929072 46.52403321068297142 (-2.541736) 0.00000006043 (-0.8254165458879) (-0.5645241586631) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_10 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0602141803955:ℝ):ℂ) + ((0.9981854799982:ℝ):ℂ) * I)‖ ≤ 0.00000011688 := by
  have hl := lg_10
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.754936742543661366 48.75493677430468254 1.5105457 0.00000001687 0.0602141803955 0.9981854799982 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_11 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8739369493041:ℝ):ℂ) + (((-0.4860393077119):ℝ):ℂ) * I)‖ ≤ 0.00000016406 := by
  have hl := lg_11
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.773034489720417742 50.77303452148146009 (-0.507552) 0.00000006405 0.8739369493041 (-0.4860393077119) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_12 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7026639122839):ℝ):ℂ) + (((-0.7115219085521):ℝ):ℂ) * I)‖ ≤ 0.00000016044 := by
  have hl := lg_12
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.615413386098864536 52.61541341785988571 (-2.3499309) 0.00000006043 (-0.7026639122839) (-0.7115219085521) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_13 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6191295504794):ℝ):ℂ) + ((0.7852888638645:ℝ):ℂ) * I)‖ ≤ 0.00000014554 := by
  have hl := lg_13
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.3102376783783158 54.310237710139358148 2.2384301 0.00000004553 (-0.6191295504794) 0.7852888638645 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_14 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7842760796287:ℝ):ℂ) + ((0.6204119848312:ℝ):ℂ) * I)‖ ≤ 0.00000014792 := by
  have hl := lg_14
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.879399880761225428 55.879399912522267776 0.6692679 0.00000004791 0.7842760796287 0.6204119848312 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_15 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7027169568469:ℝ):ℂ) + (((-0.7114695204714):ℝ):ℂ) * I)‖ ≤ 0.00000012301 := by
  have hl := lg_15
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.340254941625925902 57.34025497338696825 (-0.7915872) 0.000000023 0.7027169568469 (-0.7114695204714) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_16 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5541399922989):ℝ):ℂ) + (((-0.8324234913348):ℝ):ℂ) * I)‖ ≤ 0.00000016044 := by
  have hl := lg_16
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.7067935826888 58.7067936250368 (-2.1581258) 0.00000006043 (-0.5541399922989) (-0.8324234913348) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_17 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9552776753333):ℝ):ℂ) + ((0.2957102683229:ℝ):ℂ) * I)‖ ≤ 0.00000014678 := by
  have hl := lg_17
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.990459325029973516 59.99045936737799469 2.8413937 0.00000004677 (-0.9552776753333) 0.2957102683229 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_18 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0602885913725):ℝ):ℂ) + ((0.9981809884735:ℝ):ℂ) * I)‖ ≤ 0.00000014516 := by
  have hl := lg_18
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.200731585181129072 61.20073161694217142 1.6311215 0.00000004515 (-0.0602885913725) 0.9981809884735 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_19 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8840671494079:ℝ):ℂ) + ((0.4673598991546:ℝ):ℂ) * I)‖ ≤ 0.00000014345 := by
  have hl := lg_19
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.345550928357931922 62.345550960118995444 0.4863021 0.00000004344 0.8840671494079 0.4673598991546 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p174_20 : ‖exp (-((((((21174:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.82545863091:ℝ):ℂ) + (((-0.5644626193612):ℝ):ℂ) * I)‖ ≤ 0.0000001336 := by
  have hl := lg_20
  refine (ecis_approx ((((21174:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.431635138215861366 63.43163518056388254 (-0.5997821) 0.00000003359 0.82545863091 (-0.5644626193612) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_2 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6148679183681):ℝ):ℂ) + (((-0.7886301052765):ℝ):ℂ) * I)‖ ≤ 0.00000014292 := by
  have hl := lg_2
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.7993854465853 14.7993854572608 (-2.2330148) 0.00000004291 (-0.6148679183681) (-0.7886301052765) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_3 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1052785198662):ℝ):ℂ) + ((0.9944427752537:ℝ):ℂ) * I)‖ ≤ 0.00000015177 := by
  have hl := lg_3
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.456470969802709564 23.456470980478230915 1.6762703 0.00000005176 (-0.1052785198662) 0.9944427752537 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_4 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2438747819774):ℝ):ℂ) + ((0.9698067285363:ℝ):ℂ) * I)‖ ≤ 0.00000014274 := by
  have hl := lg_4
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.5987708931706 29.5987709145216 1.8171556 0.00000004273 (-0.2438747819774) 0.9698067285363 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_5 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9811617526011):ℝ):ℂ) + (((-0.1931880299109):ℝ):ℂ) * I)‖ ≤ 0.00000014275 := by
  have hl := lg_5
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.363108857280276359 34.36310887863129771 (-2.9471823) 0.00000004274 (-0.9811617526011) (-0.1931880299109) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_6 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8489798420641:ℝ):ℂ) + (((-0.5284252338495):ℝ):ℂ) * I)‖ ≤ 0.0000001267 := by
  have hl := lg_6
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.255856416388009564 38.255856437739030915 (-0.5567446) 0.00000002669 0.8489798420641 (-0.5284252338495) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_7 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7606885940368):ℝ):ℂ) + ((0.6491169870414:ℝ):ℂ) * I)‖ ≤ 0.00000015249 := by
  have hl := lg_7
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.547127581379795122 41.547127602730837824 2.4351696 0.00000005248 (-0.7606885940368) 0.6491169870414 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_8 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9147695619684:ℝ):ℂ) + (((-0.4039760494091):ℝ):ℂ) * I)‖ ≤ 0.00000012154 := by
  have hl := lg_8
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.3981563397559 44.3981563717824 (-0.4158592) 0.00000002153 0.9147695619684 (-0.4039760494091) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_9 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.977832885819):ℝ):ℂ) + (((-0.2093868360231):ℝ):ℂ) * I)‖ ≤ 0.00000011071 := by
  have hl := lg_9
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.912941939605419128 46.91294196095646183 (-2.9306448) 0.0000000107 (-0.977832885819) (-0.2093868360231) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_10 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4509310836561:ℝ):ℂ) + ((0.8925587699377:ℝ):ℂ) * I)‖ ≤ 0.00000015359 := by
  have hl := lg_10
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.162494303865576359 49.16249433589209771 1.1029881 0.00000005358 0.4509310836561 0.8925587699377 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_11 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5962460053686:ℝ):ℂ) + (((-0.8028017819375):ℝ):ℂ) * I)‖ ≤ 0.00000012747 := by
  have hl := lg_11
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.197461952867698083 51.197461984894240785 (-0.9319795) 0.00000002746 0.5962460053686 (-0.8028017819375) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_12 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9387425159727):ℝ):ℂ) + (((-0.3446193385876):ℝ):ℂ) * I)‖ ≤ 0.00000013758 := by
  have hl := lg_12
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.055241862973309564 53.055241894999830915 (-2.7897594) 0.00000003757 (-0.9387425159727) (-0.3446193385876) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_13 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2120162696134):ℝ):ℂ) + ((0.9772661364328:ℝ):ℂ) * I)‖ ≤ 0.00000015012 := by
  have hl := lg_13
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.7642337145109767 54.764233746537519402 1.784434 0.00000005011 (-0.2120162696134) 0.9772661364328 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_14 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.979636230273:ℝ):ℂ) + ((0.2007806174322:ℝ):ℂ) * I)‖ ≤ 0.00000013667 := by
  have hl := lg_14
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.346513027965095122 56.346513059991637824 0.2021547 0.00000003666 0.979636230273 0.2007806174322 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_15 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2954096023138:ℝ):ℂ) + (((-0.9553706960446):ℝ):ℂ) * I)‖ ≤ 0.00000013755 := by
  have hl := lg_15
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.819579827082985923 57.819579859109528625 (-1.2709121) 0.00000003754 0.2954096023138 (-0.9553706960446) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_16 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.881050130706):ℝ):ℂ) + (((-0.4730229033416):ℝ):ℂ) * I)‖ ≤ 0.00000016444 := by
  have hl := lg_16
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.1975417863412 59.1975418290432 (-2.648874) 0.00000006443 (-0.881050130706) (-0.4730229033416) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_17 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6955022544398):ℝ):ℂ) + ((0.7185239133433:ℝ):ℂ) * I)‖ ≤ 0.00000015767 := by
  have hl := lg_17
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.491938086743882334 60.491938129445903685 2.339915 0.00000005766 (-0.6955022544398) 0.7185239133433 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_18 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4361093148948:ℝ):ℂ) + ((0.8998936967565:ℝ):ℂ) * I)‖ ≤ 0.00000014644 := by
  have hl := lg_18
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.712327386190719128 61.71232741821726183 1.1195257 0.00000004643 0.4361093148948 0.8998936967565 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_19 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9993923262521:ℝ):ℂ) + (((-0.0348565378157):ℝ):ℂ) * I)‖ ≤ 0.00000014428 := by
  have hl := lg_19
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.866716627532360653 62.866716659558924706 (-0.0348636) 0.00000004427 0.9993923262521 (-0.0348565378157) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p351_20 : ‖exp (-((((((21351:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4266356599726:ℝ):ℂ) + (((-0.9044235808733):ℝ):ℂ) * I)‖ ≤ 0.00000012137 := by
  have hl := lg_20
  refine (ecis_approx ((((21351:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.961879750450876359 63.96187979315289771 (-1.1300267) 0.00000002136 0.4266356599726 (-0.9044235808733) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_2 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7067583815438):ℝ):ℂ) + (((-0.7074550092357):ℝ):ℂ) * I)‖ ≤ 0.00000011688 := by
  have hl := lg_2
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.9220724974984 14.9220725082624 (-2.3557019) 0.00000001687 (-0.7067583815438) (-0.7074550092357) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_3 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0888630559381:ℝ):ℂ) + ((0.9960438530955:ℝ):ℂ) * I)‖ ≤ 0.00000012691 := by
  have hl := lg_3
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.650925344850954592 23.65092535561497612 1.4818159 0.0000000269 0.0888630559381 0.9960438530955 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_4 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0009851730458):ℝ):ℂ) + ((0.9999995147168:ℝ):ℂ) * I)‖ ≤ 0.00000014092 := by
  have hl := lg_4
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.8441449949968 29.8441450165248 1.5717815 0.00000004091 (-0.0009851730458) 0.9999995147168 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_5 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9959112694076):ℝ):ℂ) + ((0.0903368306608:ℝ):ℂ) * I)‖ ≤ 0.00000014615 := by
  have hl := lg_5
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.647979367689091352 34.64797938921711288 3.0511325 0.00000004614 (-0.9959112694076) 0.0903368306608 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_6 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6418515037107:ℝ):ℂ) + (((-0.7668289556246):ℝ):ℂ) * I)‖ ≤ 0.00000012081 := by
  have hl := lg_6
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.572997842349354592 38.57299786387737612 (-0.873886) 0.0000000208 0.6418515037107 (-0.7668289556246) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_7 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4968342930445):ℝ):ℂ) + ((0.8678454270484:ℝ):ℂ) * I)‖ ≤ 0.00000014896 := by
  have hl := lg_7
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.891553677670564816 41.891553699198607872 2.0907435 0.00000004895 (-0.4968342930445) 0.8678454270484 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_8 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7081509452412:ℝ):ℂ) + (((-0.7060610729632):ℝ):ℂ) * I)‖ ≤ 0.00000015778 := by
  have hl := lg_8
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.7662174924952 44.7662175247872 (-0.7839204) 0.00000005777 0.7081509452412 (-0.7060610729632) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_9 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9842067144301):ℝ):ℂ) + ((0.1770230010957:ℝ):ℂ) * I)‖ ≤ 0.00000015381 := by
  have hl := lg_9
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.301850689701909184 47.30185071122995224 2.9636318 0.0000000538 (-0.9842067144301) 0.1770230010957 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_10 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7677778806255:ℝ):ℂ) + ((0.640716104076:ℝ):ℂ) * I)‖ ≤ 0.00000014006 := by
  have hl := lg_10
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.570051865187491352 49.57005189747951288 0.6954306 0.00000004005 0.7677778806255 0.640716104076 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_11 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2127507752509:ℝ):ℂ) + (((-0.9771064975887):ℝ):ℂ) * I)‖ ≤ 0.00000014144 := by
  have hl := lg_11
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.621889416014978424 51.62188944830702148 (-1.356407) 0.00000004143 0.2127507752509 (-0.9771064975887) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_12 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9961309149905):ℝ):ℂ) + ((0.0878817370253:ℝ):ℂ) * I)‖ ≤ 0.00000012478 := by
  have hl := lg_12
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.495070339847754592 53.49507037213977612 3.0535974 0.00000002477 (-0.9961309149905) 0.0878817370253 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_13 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2380506675827:ℝ):ℂ) + ((0.9712527372746:ℝ):ℂ) * I)‖ ≤ 0.00000011833 := by
  have hl := lg_13
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.2182297506436376 55.218229782935680656 1.330438 0.00000001832 0.2380506675827 0.9712527372746 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_14 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9651033954718:ℝ):ℂ) + (((-0.2618691200749):ℝ):ℂ) * I)‖ ≤ 0.00000014286 := by
  have hl := lg_14
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.813626175168964816 56.813626207461007872 (-0.2649584) 0.00000004285 0.9651033954718 (-0.2618691200749) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p528_15 : ‖exp (-((((((21528:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1784792553109):ℝ):ℂ) + (((-0.983943674924):ℝ):ℂ) * I)‖ ≤ 0.00000015209 := by
  have hl := lg_15
  refine (ecis_approx ((((21528:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.298904712540045944 58.298904744832089 (-1.750237) 0.00000005208 (-0.1784792553109) (-0.983943674924) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_2 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8125352297438):ℝ):ℂ) + (((-0.5829120863139):ℝ):ℂ) * I)‖ ≤ 0.00000012859 := by
  have hl := lg_2
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.0856552320492 15.0856552429312 (-2.5192846) 0.00000002858 (-0.8125352297438) (-0.5829120863139) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_3 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3412561320868:ℝ):ℂ) + ((0.9399703465074:ℝ):ℂ) * I)‖ ≤ 0.00000012709 := by
  have hl := lg_3
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.910197844915281296 23.91019785579730306 1.2225434 0.00000002708 0.3412561320868 0.9399703465074 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_4 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3204270059887:ℝ):ℂ) + ((0.9472732097094:ℝ):ℂ) * I)‖ ≤ 0.00000014998 := by
  have hl := lg_4
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.1713104640984 30.1713104858624 1.2446161 0.00000004997 0.3204270059887 0.9472732097094 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_5 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8914380222289):ℝ):ℂ) + ((0.4531426402553:ℝ):ℂ) * I)‖ ≤ 0.00000012819 := by
  have hl := lg_5
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.027806714900844676 35.02780673666486644 2.6713051 0.00000002818 (-0.8914380222289) 0.4531426402553 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_6 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2706374460937:ℝ):ℂ) + (((-0.9626813453952):ℝ):ℂ) * I)‖ ≤ 0.00000015567 := by
  have hl := lg_6
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.995853076964481296 38.99585309872850306 (-1.2967412) 0.00000005566 0.2706374460937 (-0.9626813453952) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_7 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0606750825222):ℝ):ℂ) + ((0.998157569906:ℝ):ℂ) * I)‖ ≤ 0.00000014425 := by
  have hl := lg_7
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.350788472724924408 42.350788494488967936 1.6315087 0.00000004424 (-0.0606750825222) 0.998157569906 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_8 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2918186764315:ℝ):ℂ) + (((-0.9564736588562):ℝ):ℂ) * I)‖ ≤ 0.00000015412 := by
  have hl := lg_8
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.2569656961476 45.2569657287936 (-1.2746686) 0.00000005411 0.2918186764315 (-0.9564736588562) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_9 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7670885046194):ℝ):ℂ) + ((0.6415412894291:ℝ):ℂ) * I)‖ ≤ 0.00000015417 := by
  have hl := lg_9
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.820395689830562592 47.82039571159460612 2.4450868 0.00000005416 (-0.7670885046194) 0.6415412894291 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_10 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.988467120106:ℝ):ℂ) + ((0.1514356380427:ℝ):ℂ) * I)‖ ≤ 0.00000012217 := by
  have hl := lg_10
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.113461946950044676 50.11346197959606644 0.1520205 0.00000002216 0.988467120106 0.1514356380427 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_11 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3443195990486):ℝ):ℂ) + (((-0.938852498377):ℝ):ℂ) * I)‖ ≤ 0.00000015724 := by
  have hl := lg_11
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.187792700211352212 52.18779273285739574 (-1.9223103) 0.00000005723 (-0.3443195990486) (-0.938852498377) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_12 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7810609840343):ℝ):ℂ) + ((0.6244547535065:ℝ):ℂ) * I)‖ ≤ 0.00000015562 := by
  have hl := lg_12
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.081508309013681296 54.08150834165970306 2.4671594 0.00000005561 (-0.7810609840343) 0.6244547535065 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_13 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.748426538861:ℝ):ℂ) + ((0.663217698745:ℝ):ℂ) * I)‖ ≤ 0.00000016581 := by
  have hl := lg_13
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.8235577988205188 55.823557831466562328 0.7251099 0.0000000658 0.748426538861 0.663217698745 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_14 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6311386761248:ℝ):ℂ) + (((-0.7756700145677):ℝ):ℂ) * I)‖ ≤ 0.00000015986 := by
  have hl := lg_14
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.436443704774124408 57.436443737420167936 (-0.887776) 0.00000005985 0.6311386761248 (-0.7756700145677) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v21p764_15 : ‖exp (-((((((21764:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7301493311937):ℝ):ℂ) + (((-0.6832876071816):ℝ):ℂ) * I)‖ ≤ 0.00000012786 := by
  have hl := lg_15
  refine (ecis_approx ((((21764:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.938004559816125972 58.9380045924621695 (-2.3893368) 0.00000002785 (-0.7301493311937) (-0.6832876071816) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_2 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8966176905623):ℝ):ℂ) + (((-0.4428055068064):ℝ):ℂ) * I)‖ ≤ 0.00000014777 := by
  have hl := lg_2
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.2492379666 15.2492379776 (-2.6828674) 0.00000004776 (-0.8966176905623) (-0.4428055068064) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_3 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5708374291683:ℝ):ℂ) + ((0.8210631093044:ℝ):ℂ) * I)‖ ≤ 0.00000012728 := by
  have hl := lg_3
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.169470344979608 24.16947035597963 0.9632709 0.00000002727 0.5708374291683 0.8210631093044 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_4 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6078464924715:ℝ):ℂ) + ((0.7940545583208:ℝ):ℂ) * I)‖ ≤ 0.00000011932 := by
  have hl := lg_4
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.4984759332 30.4984759552 0.9174506 0.00000001931 0.6078464924715 0.7940545583208 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_5 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6598968542787):ℝ):ℂ) + ((0.7513562016082:ℝ):ℂ) * I)‖ ≤ 0.00000014105 := by
  have hl := lg_5
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.407634062112598 35.40763408411262 2.2914778 0.00000004104 (-0.6598968542787) 0.7513562016082 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_6 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1482516711606):ℝ):ℂ) + (((-0.9889496660586):ℝ):ℂ) * I)‖ ≤ 0.00000013151 := by
  have hl := lg_6
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.418708311579608 39.41870833357963 (-1.7195965) 0.0000000315 (-0.1482516711606) (-0.9889496660586) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_7 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3880569826655:ℝ):ℂ) + ((0.9216353824613:ℝ):ℂ) * I)‖ ≤ 0.00000013954 := by
  have hl := lg_7
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.810023267779284 42.810023289779328 1.1722739 0.00000003953 0.3880569826655 0.9216353824613 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_8 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1933941871387):ℝ):ℂ) + (((-0.981121138484):ℝ):ℂ) * I)‖ ≤ 0.00000015047 := by
  have hl := lg_8
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.7477138998 45.7477139328 (-1.7654168) 0.00000005046 (-0.1933941871387) (-0.981121138484) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_9 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3482892589212):ℝ):ℂ) + ((0.9373871089991:ℝ):ℂ) * I)‖ ≤ 0.00000015454 := by
  have hl := lg_9
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.338940689959216 48.33894071195926 1.9265418 0.00000005453 (-0.3482892589212) 0.9373871089991 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_10 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9243798572116:ℝ):ℂ) + (((-0.3814733012695):ℝ):ℂ) * I)‖ ≤ 0.00000012874 := by
  have hl := lg_10
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.656872028712598 50.65687206171262 (-0.3913896) 0.00000002873 0.9243798572116 (-0.3814733012695) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_11 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7940342395077):ℝ):ℂ) + (((-0.6078730348044):ℝ):ℂ) * I)‖ ≤ 0.00000015999 := by
  have hl := lg_11
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.753695984407726 52.75369601740777 (-2.4882135) 0.00000005998 (-0.7940342395077) (-0.6078730348044) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_12 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3049873755209):ℝ):ℂ) + ((0.9523563937787:ℝ):ℂ) * I)‖ ≤ 0.00000014658 := by
  have hl := lg_12
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.667946278179608 54.66794631117963 1.8807215 0.00000004657 (-0.3049873755209) 0.9523563937787 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_13 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9928347214733:ℝ):ℂ) + ((0.1194956728799:ℝ):ℂ) * I)‖ ≤ 0.00000011763 := by
  have hl := lg_13
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.4288858469974 56.428885879997444 0.1197819 0.00000001762 0.9928347214733 0.1194956728799 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_14 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0601664670608:ℝ):ℂ) + (((-0.9981883570956):ℝ):ℂ) * I)‖ ≤ 0.00000013025 := by
  have hl := lg_14
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.059261234379284 58.059261267379328 (-1.5105935) 0.00000003024 0.0601664670608 (-0.9981883570956) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b2left_v22_15 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.993604693187):ℝ):ℂ) + (((-0.1129146280329):ℝ):ℂ) * I)‖ ≤ 0.00000015754 := by
  have hl := lg_15
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.577104407092206 59.57710444009225 (-3.0284367) 0.00000005753 (-0.993604693187) (-0.1129146280329) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
