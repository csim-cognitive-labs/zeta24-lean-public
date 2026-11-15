/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 10

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

lemma cs_b1left_v22p774_17 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1206565852346):ℝ):ℂ) + (((-0.9926943076491):ℝ):ℂ) * I)‖ ≤ 0.00000014762 := by
  have hl := lg_17
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.523600673856267916 64.52360071940429069 (-1.6917476) 0.00000004761 (-0.1206565852346) (-0.9926943076491) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_18 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9890503693283):ℝ):ℂ) + (((-0.1475783403314):ℝ):ℂ) * I)‖ ≤ 0.00000015895 := by
  have hl := lg_18
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.825326396567253872 65.82532643072829942 (-2.9934733) 0.00000005894 (-0.9890503693283) (-0.1475783403314) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_19 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4684970174897):ℝ):ℂ) + ((0.8834650783127:ℝ):ℂ) * I)‖ ≤ 0.00000014898 := by
  have hl := lg_19
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.056653293776496722 67.056653327937565044 2.0583851 0.00000004897 (-0.4684970174897) 0.8834650783127 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p774_20 : ‖exp (-((((((22774:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6292320398782:ℝ):ℂ) + ((0.7772174985104:ℝ):ℂ) * I)‖ ≤ 0.00000014083 := by
  have hl := lg_20
  refine (ecis_approx ((((22774:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.224806774238595766 68.22480681978661854 0.8902316 0.00000004082 0.6292320398782 0.7772174985104 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_2 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9799755533433):ℝ):ℂ) + ((0.1991178408013:ℝ):ℂ) * I)‖ ≤ 0.00000012502 := by
  have hl := lg_2
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.9084209350653 15.9084209465408 2.941135 0.00000002501 (-0.9799755533433) 0.1991178408013 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_3 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9966799476087:ℝ):ℂ) + (((-0.081419174859):ℝ):ℂ) * I)‖ ≤ 0.00000011403 := by
  have hl := lg_3
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.214250631255771964 25.214250642731294915 (-0.0815094) 0.00000001402 0.9966799476087 (-0.081419174859) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_4 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9207041736234:ℝ):ℂ) + (((-0.3902612261965):ℝ):ℂ) * I)‖ ≤ 0.0000001572 := by
  have hl := lg_4
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.8168418701306 31.8168418930816 (-0.4009153) 0.00000005719 0.9207041736234 (-0.3902612261965) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_5 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7242141019444:ℝ):ℂ) + ((0.6895751841132:ℝ):ℂ) * I)‖ ≤ 0.00000012675 := by
  have hl := lg_5
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.938209516343010759 36.93820953929403371 0.7609023 0.00000002674 0.7242141019444 0.6895751841132 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_6 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9605099728981):ℝ):ℂ) + ((0.2782455601234:ℝ):ℂ) * I)‖ ≤ 0.00000013903 := by
  have hl := lg_6
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.122671566321071964 41.122671589272094915 2.8596256 0.00000003902 (-0.9605099728981) 0.2782455601234 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_7 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7786488880699:ℝ):ℂ) + (((-0.6274598864529):ℝ):ℂ) * I)‖ ≤ 0.00000013124 := by
  have hl := lg_7
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.660583819036470322 44.660583841987516224 (-0.6782867) 0.00000003123 0.7786488880699 (-0.6274598864529) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_8 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8245595527722):ℝ):ℂ) + ((0.5657751707811:ℝ):ℂ) * I)‖ ≤ 0.00000015226 := by
  have hl := lg_8
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.7252628051959 47.7252628396224 2.5402196 0.00000005225 (-0.8245595527722) 0.5657751707811 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_9 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9867418359306:ℝ):ℂ) + (((-0.1622977178657):ℝ):ℂ) * I)‖ ≤ 0.00000012804 := by
  have hl := lg_9
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.428501262511543928 50.42850128546258983 (-0.1630188) 0.00000002803 0.9867418359306 (-0.1622977178657) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_10 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8470188333956):ℝ):ℂ) + (((-0.531562880383):ℝ):ℂ) * I)‖ ≤ 0.00000012841 := by
  have hl := lg_10
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.846630451408310759 52.84663048583483371 (-2.581148) 0.0000000284 (-0.8470188333956) (-0.531562880383) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_11 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0561933112001:ℝ):ℂ) + ((0.998419907542:ℝ):ℂ) * I)‖ ≤ 0.00000015792 := by
  have hl := lg_11
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.034094388097350883 55.034094422523896785 1.5145734 0.00000005791 0.0561933112001 0.998419907542 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_12 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8858725941209:ℝ):ℂ) + (((-0.4639286011721):ℝ):ℂ) * I)‖ ≤ 0.00000016324 := by
  have hl := lg_12
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.031092501386371964 57.031092535812894915 (-0.4824248) 0.00000006323 0.8858725941209 (-0.4639286011721) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_13 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6806786177529):ℝ):ℂ) + (((-0.7325821587462):ℝ):ℂ) * I)‖ ≤ 0.00000015503 := by
  have hl := lg_13
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.8681526852016967 58.868152719628242602 (-2.3194849) 0.00000005502 (-0.6806786177529) (-0.7325821587462) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_14 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6381184171678):ℝ):ℂ) + ((0.7699382349616:ℝ):ℂ) * I)‖ ≤ 0.00000011771 := by
  have hl := lg_14
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.569004754101770322 60.569004788528316224 2.2628483 0.0000000177 (-0.6381184171678) 0.7699382349616 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v22p951_15 : ‖exp (-((((((22951:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7779543156772:ℝ):ℂ) + ((0.6283208437727:ℝ):ℂ) * I)‖ ≤ 0.00000012421 := by
  have hl := lg_15
  refine (ecis_approx ((((22951:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.152460147598782723 62.152460182025328625 0.6793929 0.0000000242 0.7779543156772 0.6283208437727 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_2 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9482414916058):ℝ):ℂ) + ((0.3175501116334:ℝ):ℂ) * I)‖ ≤ 0.00000013558 := by
  have hl := lg_2
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.0311079859784 16.0311079975424 2.8184479 0.00000003557 (-0.9482414916058) 0.3175501116334 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_3 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9621630337275:ℝ):ℂ) + (((-0.2724743960966):ℝ):ℂ) * I)‖ ≤ 0.00000012243 := by
  have hl := lg_3
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.408705006304016992 25.40870501786804012 (-0.2759638) 0.00000002242 0.9621630337275 (-0.2724743960966) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_4 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7983239176186:ℝ):ℂ) + (((-0.6022282977062):ℝ):ℂ) * I)‖ ≤ 0.0000001592 := by
  have hl := lg_4
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.0622159719568 32.0622159950848 (-0.6462894) 0.00000005919 0.7983239176186 (-0.6022282977062) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_5 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8888203665216:ℝ):ℂ) + ((0.4582557758025:ℝ):ℂ) * I)‖ ≤ 0.00000011634 := by
  have hl := lg_5
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.223080026751825752 37.22308004987984888 0.4760318 0.00000001633 0.8888203665216 0.4582557758025 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_6 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8258386353979):ℝ):ℂ) + ((0.5639065066336:ℝ):ℂ) * I)‖ ≤ 0.00000015799 := by
  have hl := lg_6
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.439812992282416992 41.43981301541044012 2.5424841 0.00000005798 (-0.8258386353979) 0.5639065066336 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_7 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5210524296469:ℝ):ℂ) + (((-0.85352467191):ℝ):ℂ) * I)‖ ≤ 0.00000013494 := by
  have hl := lg_7
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.005009915327240016 45.005009938455286272 (-1.0227128) 0.00000003493 0.5210524296469 (-0.85352467191) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_8 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5657661992552):ℝ):ℂ) + ((0.8245657085828:ℝ):ℂ) * I)‖ ≤ 0.00000013521 := by
  have hl := lg_8
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.0933239579352 48.0933239926272 2.1721585 0.0000000352 (-0.5657661992552) 0.8245657085828 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_9 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8515154069436:ℝ):ℂ) + (((-0.5243295831228):ℝ):ℂ) * I)‖ ≤ 0.00000014484 := by
  have hl := lg_9
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.817410012608033984 50.81741003573608024 (-0.5519276) 0.00000004483 0.8515154069436 (-0.5243295831228) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_10 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9883355217312):ℝ):ℂ) + (((-0.1522921406208):ℝ):ℂ) * I)‖ ≤ 0.00000014472 := by
  have hl := lg_10
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.254188012730225752 53.25418804742224888 (-2.9887056) 0.00000004471 (-0.9883355217312) (-0.1522921406208) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_11 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4623560030865:ℝ):ℂ) + ((0.8866943816275:ℝ):ℂ) * I)‖ ≤ 0.00000012134 := by
  have hl := lg_11
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.458521851244631224 55.45852188593667748 1.0901459 0.00000002133 0.4623560030865 0.8866943816275 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_12 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6040259707434:ℝ):ℂ) + (((-0.7969646332601):ℝ):ℂ) * I)‖ ≤ 0.00000014835 := by
  have hl := lg_12
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.470920978260816992 57.47092101295284012 (-0.9222532) 0.00000004834 0.6040259707434 (-0.7969646332601) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_13 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9330085380779):ℝ):ℂ) + (((-0.3598542311946):ℝ):ℂ) * I)‖ ≤ 0.0000001433 := by
  have hl := lg_13
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.3221487213343576 59.322148756026403856 (-2.773481) 0.00000004329 (-0.9330085380779) (-0.3598542311946) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_14 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2230467756756):ℝ):ℂ) + ((0.9748077430241:ℝ):ℂ) * I)‖ ≤ 0.00000016422 := by
  have hl := lg_14
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.036117901305640016 61.036117935997686272 1.7957352 0.00000006421 (-0.2230467756756) 0.9748077430241 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p128_15 : ‖exp (-((((((23128:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9800530660608:ℝ):ℂ) + ((0.198735974863:ℝ):ℂ) * I)‖ ≤ 0.00000013876 := by
  have hl := lg_15
  refine (ecis_approx ((((23128:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.631785033055842744 62.631785067747889 0.200068 0.00000003875 0.9800530660608 0.198735974863 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_2 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9022523182956):ℝ):ℂ) + ((0.4312084809129:ℝ):ℂ) * I)‖ ≤ 0.00000012702 := by
  have hl := lg_2
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.1537950368915 16.153795048544 2.6957609 0.00000002701 (-0.9022523182956) 0.4312084809129 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_3 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8913788131926:ℝ):ℂ) + (((-0.4532590996234):ℝ):ℂ) * I)‖ ≤ 0.00000014738 := by
  have hl := lg_3
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.60315938135226202 25.603159393004785325 (-0.4704182) 0.00000004737 0.8913788131926 (-0.4532590996234) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_4 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6281184974534:ℝ):ℂ) + (((-0.7781176987814):ℝ):ℂ) * I)‖ ≤ 0.00000016121 := by
  have hl := lg_4
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.307590073783 32.307590097088 (-0.8916635) 0.0000000612 0.6281184974534 (-0.7781176987814) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_5 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9817842511578:ℝ):ℂ) + ((0.1899991688892:ℝ):ℂ) * I)‖ ≤ 0.0000001174 := by
  have hl := lg_5
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.507950537160640745 37.50795056046566405 0.1911613 0.00000001739 0.9817842511578 0.1899991688892 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_6 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6087994328753):ℝ):ℂ) + ((0.7933241774444:ℝ):ℂ) * I)‖ ≤ 0.00000013203 := by
  have hl := lg_6
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.75695441824376202 41.756954441548785325 2.2253427 0.00000003202 (-0.6087994328753) 0.7933241774444 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_7 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2022525157905:ℝ):ℂ) + (((-0.9793334058718):ℝ):ℂ) * I)‖ ≤ 0.00000013865 := by
  have hl := lg_7
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.34943601161800971 45.34943603492305632 (-1.3671389) 0.00000003864 0.2022525157905 (-0.9793334058718) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_8 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2311903223102):ℝ):ℂ) + ((0.9729085439387:ℝ):ℂ) * I)‖ ≤ 0.00000014678 := by
  have hl := lg_8
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.4613851106745 48.461385145632 1.8040973 0.00000004677 (-0.2311903223102) 0.9729085439387 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_9 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5891124580223:ℝ):ℂ) + (((-0.8080510576708):ℝ):ℂ) * I)‖ ≤ 0.00000012859 := by
  have hl := lg_9
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.20631876270452404 51.20631878600957065 (-0.9408363) 0.00000002858 0.5891124580223 (-0.8080510576708) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_10 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9677463696107):ℝ):ℂ) + ((0.2519265048451:ℝ):ℂ) * I)‖ ≤ 0.00000014441 := by
  have hl := lg_10
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.661745574052140745 53.66174560900966405 2.8869222 0.0000000444 (-0.9677463696107) 0.2519265048451 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_11 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7864732868223:ℝ):ℂ) + ((0.6176242944662:ℝ):ℂ) * I)‖ ≤ 0.00000015024 := by
  have hl := lg_11
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.882949314391911565 55.882949349349458175 0.6657184 0.00000005023 0.7864732868223 0.6176242944662 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_12 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2072025932536:ℝ):ℂ) + (((-0.9782980554764):ℝ):ℂ) * I)‖ ≤ 0.00000012549 := by
  have hl := lg_12
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.91074945513526202 57.910749490092785325 (-1.3620817) 0.00000002548 0.2072025932536 (-0.9782980554764) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_13 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9963142050811):ℝ):ℂ) + ((0.0857788100404:ℝ):ℂ) * I)‖ ≤ 0.00000012064 := by
  have hl := lg_13
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.7761447574670185 59.77614479242456511 3.0557083 0.00000002063 (-0.9963142050811) 0.0857788100404 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_14 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2398140690558:ℝ):ℂ) + ((0.9708188359745:ℝ):ℂ) * I)‖ ≤ 0.0000001233 := by
  have hl := lg_14
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.50323104850950971 61.50323108346705632 1.328622 0.00000002329 0.2398140690558 0.9708188359745 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_15 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9612605328281:ℝ):ℂ) + (((-0.2756414120322):ℝ):ℂ) * I)‖ ≤ 0.0000001533 := by
  have hl := lg_15
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.111109918512902765 63.111109953470449375 (-0.2792569) 0.00000005329 0.9612605328281 (-0.2756414120322) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_16 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2109344040638):ℝ):ℂ) + (((-0.977500218507):ℝ):ℂ) * I)‖ ≤ 0.00000012424 := by
  have hl := lg_16
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.615180147566 64.615180194176 (-1.7833271) 0.00000002423 (-0.2109344040638) (-0.977500218507) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_17 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9985102672786):ℝ):ℂ) + ((0.0545641418508:ℝ):ℂ) * I)‖ ≤ 0.00000012665 := by
  have hl := lg_17
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.02803695899799437 66.028037005608017675 3.0870014 0.00000002664 (-0.9985102672786) 0.0545641418508 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_18 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1830896118781):ℝ):ℂ) + ((0.9830962282613:ℝ):ℂ) * I)‖ ≤ 0.00000015559 := by
  have hl := lg_18
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.36011379959602404 67.36011383455357065 1.7549246 0.00000005558 (-0.1830896118781) 0.9830962282613 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_19 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8800219078619:ℝ):ℂ) + ((0.4749330917963:ℝ):ℂ) * I)‖ ≤ 0.0000001473 := by
  have hl := lg_19
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.620150391299782915 68.62015042625735283 0.494888 0.00000004729 0.8800219078619 0.4749330917963 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p305_20 : ‖exp (-((((((23305:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7645185002669:ℝ):ℂ) + (((-0.6446017861824):ℝ):ℂ) * I)‖ ≤ 0.00000016805 := by
  have hl := lg_20
  refine (ecis_approx ((((23305:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.815540610943640745 69.81554065755366405 (-0.7005023) 0.00000006804 0.7645185002669 (-0.6446017861824) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_2 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8426993254464):ℝ):ℂ) + ((0.5383844786235:ℝ):ℂ) * I)‖ ≤ 0.00000013375 := by
  have hl := lg_2
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.2764820878046 16.2764820995456 2.5730738 0.00000003374 (-0.8426993254464) 0.5383844786235 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_3 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7869954537715:ℝ):ℂ) + (((-0.6169587958227):ℝ):ℂ) * I)‖ ≤ 0.00000013944 := by
  have hl := lg_3
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.797613756400507048 25.79761376814153053 (-0.6648725) 0.00000003943 0.7869954537715 (-0.6169587958227) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_4 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4202843127865:ℝ):ℂ) + (((-0.9073924709989):ℝ):ℂ) * I)‖ ≤ 0.0000001603 := by
  have hl := lg_4
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.5529641756092 32.5529641990912 (-1.1370377) 0.00000006029 0.4202843127865 (-0.9073924709989) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_5 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9956125050288:ℝ):ℂ) + (((-0.0935721103232):ℝ):ℂ) * I)‖ ≤ 0.00000012799 := by
  have hl := lg_5
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.792821047569455738 37.79282107105147922 (-0.0937092) 0.00000002798 0.9956125050288 (-0.0935721103232) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_6 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3310394983909):ℝ):ℂ) + ((0.9436168981652:ℝ):ℂ) * I)‖ ≤ 0.00000011745 := by
  have hl := lg_6
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.074095844205107048 42.07409586768713053 1.9082013 0.00000001744 (-0.3310394983909) 0.9436168981652 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_7 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1403042258478):ℝ):ℂ) + (((-0.990108440631):ℝ):ℂ) * I)‖ ≤ 0.00000014236 := by
  have hl := lg_7
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.693862107908779404 45.693862131390826368 (-1.711565) 0.00000004235 (-0.1403042258478) (-0.990108440631) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_8 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1343526164592:ℝ):ℂ) + ((0.9909335873057:ℝ):ℂ) * I)‖ ≤ 0.00000014122 := by
  have hl := lg_8
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.8294462634138 48.8294462986368 1.4360362 0.00000004121 0.1343526164592 0.9909335873057 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_9 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2387235914052:ℝ):ℂ) + (((-0.971087558826):ℝ):ℂ) * I)‖ ≤ 0.00000014465 := by
  have hl := lg_9
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.595227512801014096 51.59522753628306106 (-1.3297451) 0.00000004464 0.2387235914052 (-0.971087558826) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_10 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7886242145678):ℝ):ℂ) + ((0.6148754736954:ℝ):ℂ) * I)‖ ≤ 0.00000012926 := by
  have hl := lg_10
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.069303135374055738 54.06930317059707922 2.4793646 0.00000002925 (-0.7886242145678) 0.6148754736954 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_11 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9710302913914:ℝ):ℂ) + ((0.2389564253171:ℝ):ℂ) * I)‖ ≤ 0.00000014816 := by
  have hl := lg_11
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.307376777539191906 56.30737681276223887 0.241291 0.00000004815 0.9710302913914 0.2389564253171 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_12 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2290619227918):ℝ):ℂ) + (((-0.973411852982):ℝ):ℂ) * I)‖ ≤ 0.00000013262 := by
  have hl := lg_12
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.350577932009707048 58.35057796723273053 (-1.8019102) 0.00000003261 (-0.2290619227918) (-0.973411852982) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_13 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8577701897303):ℝ):ℂ) + ((0.5140333661652:ℝ):ℂ) * I)‖ ≤ 0.00000015704 := by
  have hl := lg_13
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.2301407935996794 60.230140828822726364 2.6017123 0.00000005703 (-0.8577701897303) 0.5140333661652 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_14 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6512932172269:ℝ):ℂ) + ((0.7588261626975:ℝ):ℂ) * I)‖ ≤ 0.00000015916 := by
  have hl := lg_14
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.970344195713379404 61.970344230936426368 0.8615089 0.00000005915 0.6512932172269 0.7588261626975 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_15 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7258123786681:ℝ):ℂ) + (((-0.6878927176328):ℝ):ℂ) * I)‖ ≤ 0.00000016741 := by
  have hl := lg_15
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.590434803969962786 63.59043483919300975 (-0.7585817) 0.0000000674 0.7258123786681 (-0.6878927176328) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_16 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6467221165769):ℝ):ℂ) + (((-0.7627257068658):ℝ):ℂ) * I)‖ ≤ 0.0000001264 := by
  have hl := lg_16
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.1059283512184 65.1059283981824 (-2.2740753) 0.00000002639 (-0.6467221165769) (-0.7627257068658) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_17 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8493360962152):ℝ):ℂ) + ((0.5278524373274:ℝ):ℂ) * I)‖ ≤ 0.00000015828 := by
  have hl := lg_17
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.529515720711903188 66.52951576767592667 2.5855226 0.00000005827 (-0.8493360962152) 0.5278524373274 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_18 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3216461649583:ℝ):ℂ) + ((0.9468599392558:ℝ):ℂ) * I)‖ ≤ 0.00000015687 := by
  have hl := lg_18
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.871709600605614096 67.87170963582866106 1.2433288 0.00000005686 0.3216461649583 0.9468599392558 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_19 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9996547611082:ℝ):ℂ) + (((-0.0262746759024):ℝ):ℂ) * I)‖ ≤ 0.00000014674 := by
  have hl := lg_19
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.141316090474211646 69.141316125697282092 (-0.0262777) 0.00000004673 0.9996547611082 (-0.0262746759024) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p482_20 : ‖exp (-((((((23482:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3335336890749:ℝ):ℂ) + (((-0.9427381811787):ℝ):ℂ) * I)‖ ≤ 0.00000015581 := by
  have hl := lg_20
  refine (ecis_approx ((((23482:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.345785223178655738 70.34578527014267922 (-1.2307469) 0.0000000558 0.3335336890749 (-0.9427381811787) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_2 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.770477883802):ℝ):ℂ) + ((0.6374667289614:ℝ):ℂ) * I)‖ ≤ 0.00000012902 := by
  have hl := lg_2
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.3991691387177 16.3991691505472 2.4503868 0.00000002901 (-0.770477883802) 0.6374667289614 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_3 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6529474241568:ℝ):ℂ) + (((-0.7574032355932):ℝ):ℂ) * I)‖ ≤ 0.00000011457 := by
  have hl := lg_3
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.992068131448752076 25.992068143278275735 (-0.8593269) 0.00000001456 0.6529474241568 (-0.7574032355932) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_4 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1872722476998:ℝ):ℂ) + (((-0.9823080500746):ℝ):ℂ) * I)‖ ≤ 0.00000015848 := by
  have hl := lg_4
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.7983382774354 32.7983383010944 (-1.3824118) 0.00000005847 0.1872722476998 (-0.9823080500746) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_5 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9291905170669:ℝ):ℂ) + (((-0.3696011133545):ℝ):ℂ) * I)‖ ≤ 0.00000013857 := by
  have hl := lg_5
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.077691557978270731 38.07769158163729439 (-0.3785797) 0.00000003856 0.9291905170669 (-0.3696011133545) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_6 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0202621864879):ℝ):ℂ) + ((0.9997947008254:ℝ):ℂ) * I)‖ ≤ 0.00000014358 := by
  have hl := lg_6
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.391237270166452076 42.391237293825475735 1.5910599 0.00000004357 (-0.0202621864879) 0.9997947008254 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_7 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4663806615797):ℝ):ℂ) + (((-0.8845841274291):ℝ):ℂ) * I)‖ ≤ 0.00000014607 := by
  have hl := lg_7
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.038288204199549098 46.038288227858596416 (-2.0559911) 0.00000004606 (-0.4663806615797) (-0.8845841274291) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_8 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4818995744313:ℝ):ℂ) + ((0.8762264548408:ℝ):ℂ) * I)‖ ≤ 0.0000001413 := by
  have hl := lg_8
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.1975074161531 49.1975074516416 1.067975 0.00000004129 0.4818995744313 0.8762264548408 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_9 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1473193225741):ℝ):ℂ) + (((-0.9890889834568):ℝ):ℂ) * I)‖ ≤ 0.00000012913 := by
  have hl := lg_9
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.984136262897504152 51.98413628655655147 (-1.7186538) 0.00000002912 (-0.1473193225741) (-0.9890889834568) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_10 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4803123304864):ℝ):ℂ) + ((0.877097523185:ℝ):ℂ) * I)‖ ≤ 0.00000016758 := by
  have hl := lg_10
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.476860696695970731 54.47686073218449439 2.0718071 0.00000006757 (-0.4803123304864) 0.877097523185 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_11 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9832773281095:ℝ):ℂ) + (((-0.1821145134959):ℝ):ℂ) * I)‖ ≤ 0.00000012394 := by
  have hl := lg_11
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.731804240686472247 56.731804276175019565 (-0.1831365) 0.00000002393 0.9832773281095 (-0.1821145134959) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_12 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6217243637229):ℝ):ℂ) + (((-0.7832361173615):ℝ):ℂ) * I)‖ ≤ 0.00000015575 := by
  have hl := lg_12
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.790406408884152076 58.790406444372675735 (-2.2417387) 0.00000005574 (-0.6217243637229) (-0.7832361173615) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_13 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5454449302453):ℝ):ℂ) + ((0.8381466626202:ℝ):ℂ) * I)‖ ≤ 0.00000014208 := by
  have hl := lg_13
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.6841368297323403 60.684136865220887618 2.1477162 0.00000004207 (-0.5454449302453) 0.8381466626202 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_14 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9232289354082:ℝ):ℂ) + ((0.3842503517565:ℝ):ℂ) * I)‖ ≤ 0.00000012889 := by
  have hl := lg_14
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.437457342917249098 62.437457378405796416 0.3943957 0.00000002888 0.9232289354082 0.3842503517565 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_15 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3267754755362:ℝ):ℂ) + (((-0.9451019990393):ℝ):ℂ) * I)‖ ≤ 0.00000015313 := by
  have hl := lg_15
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.069759689427022807 64.069759724915570125 (-1.2379066) 0.00000005312 0.3267754755362 (-0.9451019990393) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_16 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9298581736387):ℝ):ℂ) + (((-0.3679181658438):ℝ):ℂ) * I)‖ ≤ 0.00000013041 := by
  have hl := lg_16
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.5966765548708 65.5966766021888 (-2.7648235) 0.0000000304 (-0.9298581736387) (-0.3679181658438) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_17 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4910089692437):ℝ):ℂ) + ((0.8711545167858:ℝ):ℂ) * I)‖ ≤ 0.00000015078 := by
  have hl := lg_17
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.030994482425812006 67.030994529743835665 2.0840439 0.00000005077 (-0.4910089692437) 0.8711545167858 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_18 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7440175988591:ℝ):ℂ) + ((0.6681600201957:ℝ):ℂ) * I)‖ ≤ 0.00000015814 := by
  have hl := lg_18
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.383305401615204152 68.38330543710375147 0.731733 0.00000005813 0.7440175988591 0.6681600201957 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_19 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8538580366379:ℝ):ℂ) + (((-0.5205059589178):ℝ):ℂ) * I)‖ ≤ 0.00000014618 := by
  have hl := lg_19
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.662481789648640377 69.662481825137211354 (-0.5474434) 0.00000004617 0.8538580366379 (-0.5205059589178) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p659_20 : ‖exp (-((((((23659:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1890505522923):ℝ):ℂ) + (((-0.9819673562177):ℝ):ℂ) * I)‖ ≤ 0.00000014358 := by
  have hl := lg_20
  refine (ecis_approx ((((23659:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.876029835413670731 70.87602988273169439 (-1.7609915) 0.00000004357 (-0.1890505522923) (-0.9819673562177) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_2 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7090111400585):ℝ):ℂ) + ((0.7051972796655:ℝ):ℂ) * I)‖ ≤ 0.00000015504 := by
  have hl := lg_2
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.4906645665173 16.4906645784128 2.3588913 0.00000005503 (-0.7090111400585) 0.7051972796655 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_3 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5366421227144:ℝ):ℂ) + (((-0.8438099502427):ℝ):ℂ) * I)‖ ≤ 0.00000013671 := by
  have hl := lg_3
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.137084953518629724 26.137084965414153515 (-1.0043437) 0.0000000367 0.5366421227144 (-0.8438099502427) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_4 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0053937006423:ℝ):ℂ) + (((-0.9999854538908):ℝ):ℂ) * I)‖ ≤ 0.00000012094 := by
  have hl := lg_4
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.9813291330346 32.9813291568256 (-1.5654026) 0.00000002093 0.0053937006423 (-0.9999854538908) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_5 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8303696940417:ℝ):ℂ) + (((-0.5572128598813):ℝ):ℂ) * I)‖ ≤ 0.00000014308 := by
  have hl := lg_5
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.290137362350946319 38.29013738614197011 (-0.5910255) 0.00000004307 0.8303696940417 (-0.5572128598813) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_6 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2145672382469:ℝ):ℂ) + ((0.9767092199171:ℝ):ℂ) * I)‖ ≤ 0.00000013024 := by
  have hl := lg_6
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.627749520035929724 42.627749543826953515 1.3545476 0.00000003023 0.2145672382469 0.9767092199171 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_7 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6758039462208):ℝ):ℂ) + (((-0.7370814244385):ℝ):ℂ) * I)‖ ≤ 0.00000011736 := by
  have hl := lg_7
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.295148343806224802 46.295148367597272384 (-2.3128512) 0.00000001735 (-0.6758039462208) (-0.7370814244385) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_8 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7013628279617:ℝ):ℂ) + ((0.712804449729:ℝ):ℂ) * I)‖ ≤ 0.0000001579 := by
  have hl := lg_8
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.4719936995519 49.4719937352384 0.7934887 0.00000005789 0.7013628279617 0.712804449729 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_9 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.424030554822):ℝ):ℂ) + (((-0.9056478833264):ℝ):ℂ) * I)‖ ≤ 0.00000015041 := by
  have hl := lg_9
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.274169907037259448 52.27416993082830703 (-2.0086875) 0.0000000504 (-0.424030554822) (-0.9056478833264) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_10 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1957963704547):ℝ):ℂ) + ((0.980644574408:ℝ):ℂ) * I)‖ ≤ 0.00000013576 := by
  have hl := lg_10
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.780801928868246319 54.78080196455477011 1.7678658 0.00000003575 (-0.1957963704547) 0.980644574408 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_11 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8777461387106:ℝ):ℂ) + (((-0.4791259917585):ℝ):ℂ) * I)‖ ≤ 0.00000014804 := by
  have hl := lg_11
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.048326416592918603 57.048326452279466185 (-0.4996587) 0.00000004803 0.8777461387106 (-0.4791259917585) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_12 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8409031891129):ℝ):ℂ) + (((-0.5411855748923):ℝ):ℂ) * I)‖ ≤ 0.00000015764 := by
  have hl := lg_12
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.118414086553229724 59.118414122239753515 (-2.5697463) 0.00000005763 (-0.8409031891129) (-0.5411855748923) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_13 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2360962660064):ℝ):ℂ) + ((0.9717296708327:ℝ):ℂ) * I)‖ ≤ 0.000000127 := by
  have hl := lg_13
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.0227101448143247 61.022710180500872282 1.8091429 0.00000002699 (-0.2360962660064) 0.9717296708327 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_14 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9989403417948:ℝ):ℂ) + ((0.0460238365943:ℝ):ℂ) * I)‖ ≤ 0.00000016149 := by
  have hl := lg_14
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.785812910323524802 62.785812946010072384 0.0460401 0.00000006148 0.9989403417948 0.0460238365943 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_15 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0245705002926):ℝ):ℂ) + (((-0.9996980996857):ℝ):ℂ) * I)‖ ≤ 0.00000015594 := by
  have hl := lg_15
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.427222315869576043 64.427222351556123625 (-1.5953693) 0.00000005593 (-0.0245705002926) (-0.9996980996857) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_16 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999418156593):ℝ):ℂ) + (((-0.0107872440748):ℝ):ℂ) * I)‖ ≤ 0.00000014187 := by
  have hl := lg_16
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.9626582660692 65.9626583136512 (-3.1308052) 0.00000004186 (-0.9999418156593) (-0.0107872440748) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_17 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1388136572154):ℝ):ℂ) + ((0.9903185187453:ℝ):ℂ) * I)‖ ≤ 0.00000013529 := by
  have hl := lg_17
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.404978643703981294 67.404978691286005085 1.7100597 0.00000003528 (-0.1388136572154) 0.9903185187453 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_18 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9393027764576:ℝ):ℂ) + ((0.3430893384222:ℝ):ℂ) * I)‖ ≤ 0.00000013028 := by
  have hl := lg_18
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.764834473554559448 68.76483450924110703 0.3502039 0.00000003027 0.9393027764576 0.3430893384222 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_19 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5929254389135:ℝ):ℂ) + (((-0.8052573650016):ℝ):ℂ) * I)‖ ≤ 0.00000014419 := by
  have hl := lg_19
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.051147734795671973 70.051147770482243346 (-0.9361094) 0.00000004418 0.5929254389135 (-0.8052573650016) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_20 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5527259890497):ℝ):ℂ) + (((-0.8333630547488):ℝ):ℂ) * I)‖ ≤ 0.00000016401 := by
  have hl := lg_20
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.271466495385546319 71.27146654296757011 (-2.1564281) 0.000000064 (-0.5527259890497) (-0.8333630547488) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_21 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9846215029253):ℝ):ℂ) + ((0.1747011609008:ℝ):ℂ) * I)‖ ≤ 0.00000014687 := by
  have hl := lg_21
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.432233297324854526 72.432233333011425899 2.9659904 0.00000004686 (-0.9846215029253) 0.1747011609008 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_22 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2844535403494):ℝ):ℂ) + ((0.9586898264721:ℝ):ℂ) * I)‖ ≤ 0.00000014455 := by
  have hl := lg_22
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.538990983110218603 73.538991030692266185 1.8592327 0.00000004454 (-0.2844535403494) 0.9586898264721 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_23 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6954999936684:ℝ):ℂ) + ((0.7185261016882:ℝ):ℂ) * I)‖ ≤ 0.00000012787 := by
  have hl := lg_23
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.596542866432906506 74.596542914014977879 0.8016808 0.00000002786 0.6954999936684 0.7185261016882 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_24 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.977852324049:ℝ):ℂ) + (((-0.2092960399816):ℝ):ℂ) * I)‖ ≤ 0.0000001331 := by
  have hl := lg_24
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.609078653070529724 75.609078700652553515 (-0.210855) 0.00000003309 0.977852324049 (-0.2092960399816) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_25 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3790275650273:ℝ):ℂ) + (((-0.9253853818542):ℝ):ℂ) * I)‖ ≤ 0.00000016147 := by
  have hl := lg_25
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.580274724701892638 76.58027477228394022 (-1.1820511) 0.00000006146 0.3790275650273 (-0.9253853818542) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_26 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5178661460421):ℝ):ℂ) + (((-0.8554616617806):ℝ):ℂ) * I)‖ ≤ 0.00000017277 := by
  have hl := lg_26
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.5133747113316247 77.513374758913672282 (-2.115151) 0.00000007276 (-0.5178661460421) (-0.8554616617806) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_27 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9917473522152):ℝ):ℂ) + (((-0.1282076009713):ℝ):ℂ) * I)‖ ≤ 0.00000012561 := by
  have hl := lg_27
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.411254860555889172 78.411254896242460545 (-3.0130312) 0.0000000256 (-0.9917473522152) (-0.1282076009713) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_28 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7407157821334):ℝ):ℂ) + ((0.6718185246529:ℝ):ℂ) * I)‖ ≤ 0.0000001311 := by
  have hl := lg_28
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.276477476840824802 79.276477524422872384 2.4049315 0.00000003109 (-0.7407157821334) 0.6718185246529 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_29 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.000722426732:ℝ):ℂ) + ((0.9999997390497:ℝ):ℂ) * I)‖ ≤ 0.00000012688 := by
  have hl := lg_29
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.111335066470749372 80.111335114052820745 1.5700739 0.00000002687 0.000722426732 0.9999997390497 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p791_30 : ‖exp (-((((((23791:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7224050696768:ℝ):ℂ) + ((0.6914701116499:ℝ):ℂ) * I)‖ ≤ 0.00000013665 := by
  have hl := lg_30
  refine (ecis_approx ((((23791:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.917886882386876043 80.917886929968923625 0.7635221 0.00000003664 0.7224050696768 0.6914701116499 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_2 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6416131778712):ℝ):ℂ) + ((0.7670283762457:ℝ):ℂ) * I)‖ ≤ 0.00000012724 := by
  have hl := lg_2
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.5821599943169 16.5821600062784 2.2673959 0.00000002723 (-0.6416131778712) 0.7670283762457 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_3 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4090709786064:ℝ):ℂ) + (((-0.9125025668249):ℝ):ℂ) * I)‖ ≤ 0.00000015314 := by
  have hl := lg_3
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.282101775588507372 26.282101787550031295 (-1.1493606) 0.00000005313 0.4090709786064 (-0.9125025668249) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_4 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1766650528935):ℝ):ℂ) + (((-0.9842710292828):ℝ):ℂ) * I)‖ ≤ 0.00000014728 := by
  have hl := lg_4
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.1643199886338 33.1643200125568 (-1.7483935) 0.00000004727 (-0.1766650528935) (-0.9842710292828) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_5 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6942123585227:ℝ):ℂ) + (((-0.7197702420039):ℝ):ℂ) * I)‖ ≤ 0.00000014758 := by
  have hl := lg_5
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.502583166723621907 38.50258319064664583 (-0.8034713) 0.00000004757 0.6942123585227 (-0.7197702420039) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_6 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4374499416766:ℝ):ℂ) + ((0.899242763956:ℝ):ℂ) * I)‖ ≤ 0.00000014359 := by
  have hl := lg_6
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.864261769905407372 42.864261793828431295 1.1180354 0.00000004358 0.4374499416766 0.899242763956 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_7 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8408842471027):ℝ):ℂ) + (((-0.5412150061724):ℝ):ℂ) * I)‖ ≤ 0.00000015709 := by
  have hl := lg_7
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.552008483412900506 46.552008507335948352 (-2.5697113) 0.00000005708 (-0.8408842471027) (-0.5412150061724) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_8 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8683143857902:ℝ):ℂ) + ((0.4960142411562:ℝ):ℂ) * I)‖ ≤ 0.00000016141 := by
  have hl := lg_8
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.7464799829507 49.7464800188352 0.5190025 0.0000000614 0.8683143857902 0.4960142411562 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_9 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6653217942663):ℝ):ℂ) + (((-0.7465567025053):ℝ):ℂ) * I)‖ ≤ 0.00000011768 := by
  have hl := lg_9
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.564203551177014744 52.56420357510006259 (-2.2987211) 0.00000001767 (-0.6653217942663) (-0.7465567025053) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_10 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1066684025304:ℝ):ℂ) + ((0.994294650444:ℝ):ℂ) * I)‖ ≤ 0.00000013232 := by
  have hl := lg_10
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.084743161040521907 55.08474319692504583 1.4639246 0.00000003231 0.1066684025304 0.994294650444 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_11 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6850086171204:ℝ):ℂ) + (((-0.7285349644806):ℝ):ℂ) * I)‖ ≤ 0.00000016378 := by
  have hl := lg_11
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.364848592499364959 57.364848628383912805 (-0.8161808) 0.00000006377 0.6850086171204 (-0.7285349644806) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_12 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9704183624954):ℝ):ℂ) + (((-0.2414294958333):ℝ):ℂ) * I)‖ ≤ 0.00000013551 := by
  have hl := lg_12
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.446421764222307372 59.446421800106831295 (-2.897754) 0.0000000355 (-0.9704183624954) (-0.2414294958333) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_13 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1000590081842:ℝ):ℂ) + ((0.9949815047935:ℝ):ℂ) * I)‖ ≤ 0.000000124 := by
  have hl := lg_13
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.3612834598963091 61.361283495780856946 1.4705696 0.00000002399 0.1000590081842 0.9949815047935 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_14 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9546496814353:ℝ):ℂ) + (((-0.2977313986389):ℝ):ℂ) * I)‖ ≤ 0.00000014183 := by
  have hl := lg_14
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.134168477729800506 63.134168513614348352 (-0.3023154) 0.00000004182 0.9546496814353 (-0.2977313986389) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_15 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3728100644913):ℝ):ℂ) + (((-0.9279076763403):ℝ):ℂ) * I)‖ ≤ 0.0000001295 := by
  have hl := lg_15
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.784684942312129279 64.784684978196677125 (-1.9528319) 0.00000002949 (-0.3728100644913) (-0.9279076763403) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_16 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9375789503938):ℝ):ℂ) + ((0.3477724997815:ℝ):ℂ) * I)‖ ≤ 0.00000014615 := by
  have hl := lg_16
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.3286399772676 66.3286400251136 2.7863984 0.00000004614 (-0.9375789503938) 0.3477724997815 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_17 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2325713792387:ℝ):ℂ) + ((0.9725793302137:ℝ):ℂ) * I)‖ ≤ 0.00000017387 := by
  have hl := lg_17
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.778962804982150582 67.778962852828174505 1.3360756 0.00000007386 0.2325713792387 0.9725793302137 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_18 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9995094060415:ℝ):ℂ) + (((-0.0313200771811):ℝ):ℂ) * I)‖ ≤ 0.0000001335 := by
  have hl := lg_18
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.146363545493914744 69.14636358137846259 (-0.0313252) 0.00000003349 0.9995094060415 (-0.0313200771811) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_19 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.243546734388:ℝ):ℂ) + (((-0.9698891628268):ℝ):ℂ) * I)‖ ≤ 0.00000013687 := by
  have hl := lg_19
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.439813679942703569 70.439813715827275338 (-1.3247753) 0.00000003686 0.243546734388 (-0.9698891628268) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_20 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8310920599677):ℝ):ℂ) + (((-0.5561348647546):ℝ):ℂ) * I)‖ ≤ 0.00000012424 := by
  have hl := lg_20
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.666903155357421907 71.66690320320344583 (-2.5518648) 0.00000002423 (-0.8310920599677) (-0.5561348647546) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_21 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8378414202995):ℝ):ℂ) + ((0.5459136876502:ℝ):ℂ) * I)‖ ≤ 0.00000012717 := by
  have hl := lg_21
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.834110259001407878 72.834110294885979647 2.5641134 0.00000002716 (-0.8378414202995) 0.5459136876502 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_22 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1192964351495:ℝ):ℂ) + ((0.9928586810622:ℝ):ℂ) * I)‖ ≤ 0.00000014852 := by
  have hl := lg_22
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.947008586816264959 73.947008634662312805 1.4512151 0.00000004851 0.1192964351495 0.9928586810622 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_23 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9257448992798:ℝ):ℂ) + ((0.3781486235034:ℝ):ℂ) * I)‖ ≤ 0.0000001645 := by
  have hl := lg_23
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.010428102798302818 75.010428150644374587 0.3877956 0.00000006449 0.9257448992798 0.3781486235034 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_24 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8078164837699:ℝ):ℂ) + (((-0.5894340748121):ℝ):ℂ) * I)‖ ≤ 0.00000012763 := by
  have hl := lg_24
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.028581758539207372 76.028581806385231295 (-0.6303581) 0.00000002762 0.8078164837699 (-0.5894340748121) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_25 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0361385024833):ℝ):ℂ) + (((-0.999346790978):ℝ):ℂ) * I)‖ ≤ 0.00000015272 := by
  have hl := lg_25
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.005166333447243814 77.00516638129329166 (-1.6069427) 0.00000005271 (-0.0361385024833) (-0.999346790978) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_26 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8273782221949):ℝ):ℂ) + (((-0.5616451525442):ℝ):ℂ) * I)‖ ≤ 0.00000013196 := by
  have hl := lg_26
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.9434434542132091 77.943443502059256946 (-2.5452198) 0.00000003195 (-0.8273782221949) (-0.5616451525442) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_27 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9533987425527):ℝ):ℂ) + ((0.3017131708863:ℝ):ℂ) * I)‖ ≤ 0.00000016658 := by
  have hl := lg_27
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.846305326765522116 78.846305362650093885 2.8351036 0.00000006657 (-0.9533987425527) 0.3017131708863 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_28 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.384147384603):ℝ):ℂ) + ((0.923271783875:ℝ):ℂ) * I)‖ ≤ 0.00000012657 := by
  have hl := lg_28
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.716328472046700506 79.716328519892748352 1.9650805 0.00000002656 (-0.384147384603) 0.923271783875 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_29 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4306432916329:ℝ):ℂ) + ((0.9025222187689:ℝ):ℂ) * I)‖ ≤ 0.00000017042 := by
  have hl := lg_29
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.555818115891712716 80.555818163737784485 1.1255909 0.00000007041 0.4306432916329 0.9025222187689 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v23p923_30 : ‖exp (-((((((23923:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9509313685199:ℝ):ℂ) + ((0.3094018945721:ℝ):ℂ) * I)‖ ≤ 0.00000015672 := by
  have hl := lg_30
  refine (ecis_approx ((((23923:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.366844936629029279 81.366844984475077125 0.314564 0.00000005671 0.9509313685199 0.3094018945721 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_2 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5875097823178):ℝ):ℂ) + ((0.8092170633828:ℝ):ℂ) * I)‖ ≤ 0.00000015565 := by
  have hl := lg_2
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.6507815651666 16.6507815771776 2.1987744 0.00000005564 (-0.5875097823178) 0.8092170633828 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_3 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3076032518811:ℝ):ℂ) + (((-0.9515147079432):ℝ):ℂ) * I)‖ ≤ 0.00000013659 := by
  have hl := lg_3
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.390864392140915608 26.39086440415193963 (-1.2581232) 0.00000003658 0.3076032518811 (-0.9515147079432) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_4 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.309664599618):ℝ):ℂ) + (((-0.9508458527761):ℝ):ℂ) * I)‖ ≤ 0.00000011847 := by
  have hl := lg_4
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.3015631303332 33.3015631543552 (-1.8856366) 0.00000001846 (-0.309664599618) (-0.9508458527761) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_5 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5712193259452:ℝ):ℂ) + (((-0.8207974668983):ℝ):ℂ) * I)‖ ≤ 0.00000012309 := by
  have hl := lg_5
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.661917520003128598 38.66191754402515262 (-0.9628057) 0.00000002308 0.5712193259452 (-0.8207974668983) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_6 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5892620181801:ℝ):ℂ) + ((0.8079419991128:ℝ):ℂ) * I)‖ ≤ 0.00000013109 := by
  have hl := lg_6
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.041645957307515608 43.04164598132953963 0.9406512 0.00000003108 0.5892620181801 0.8079419991128 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_7 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9289476538253):ℝ):ℂ) + (((-0.3702110969362):ℝ):ℂ) * I)‖ ≤ 0.0000001619 := by
  have hl := lg_7
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.744653588117907284 46.744653612139955328 (-2.7623564) 0.00000006189 (-0.9289476538253) (-0.3702110969362) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_8 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9513717010378:ℝ):ℂ) + ((0.3080452669081:ℝ):ℂ) * I)‖ ≤ 0.00000016195 := by
  have hl := lg_8
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.9523446954998 49.9523447315328 0.3131377 0.00000006194 0.9513717010378 0.3080452669081 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_9 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8107604203151):ℝ):ℂ) + (((-0.5853781177982):ℝ):ℂ) * I)‖ ≤ 0.00000015088 := by
  have hl := lg_9
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.781728784281831216 52.78172880830387926 (-2.5162463) 0.00000005087 (-0.8107604203151) (-0.5853781177982) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_10 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3286063739584:ℝ):ℂ) + ((0.9444669665975:ℝ):ℂ) * I)‖ ≤ 0.0000001566 := by
  have hl := lg_10
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.312699085169728598 55.31269912120275262 1.2359687 0.00000005659 0.3286063739584 0.9444669665975 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_11 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4944690098243:ℝ):ℂ) + (((-0.8691952590318):ℝ):ℂ) * I)‖ ≤ 0.0000001402 := by
  have hl := lg_11
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.602240224429199726 57.60224026046224777 (-1.0535725) 0.00000004019 0.4944690098243 (-0.8691952590318) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_12 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999976513831):ℝ):ℂ) + ((0.0021671515908:ℝ):ℂ) * I)‖ ≤ 0.00000014934 := by
  have hl := lg_12
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.692427522474115608 59.69242755850713963 3.1394255 0.00000004933 (-0.9999976513831) 0.0021671515908 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_13 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3467995495822:ℝ):ℂ) + ((0.9379392690412:ℝ):ℂ) * I)‖ ≤ 0.0000001256 := by
  have hl := lg_13
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.6152134462077974 61.615213482240845444 1.2166396 0.00000002559 0.3467995495822 0.9379392690412 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_14 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8453469172571:ℝ):ℂ) + (((-0.5342177360252):ℝ):ℂ) * I)‖ ≤ 0.00000011853 := by
  have hl := lg_14
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.395435153284507284 63.395435189317555328 (-0.5635821) 0.00000001852 0.8453469172571 (-0.5342177360252) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_15 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6052919397972):ℝ):ℂ) + (((-0.7960035600449):ℝ):ℂ) * I)‖ ≤ 0.00000015967 := by
  have hl := lg_15
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.052781912144044206 65.05278194817709225 (-2.2209289) 0.00000005966 (-0.6052919397972) (-0.7960035600449) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_16 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8082156672479):ℝ):ℂ) + ((0.5888866063705:ℝ):ℂ) * I)‖ ≤ 0.00000012975 := by
  have hl := lg_16
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.6031262606664 66.6031263087104 2.5119121 0.00000002974 (-0.8082156672479) 0.5888866063705 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_17 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4927166657542:ℝ):ℂ) + ((0.8701897995771:ℝ):ℂ) * I)‖ ≤ 0.00000015305 := by
  have hl := lg_17
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.059450925940777548 68.05945097398480157 1.0555874 0.00000005304 0.4927166657542 0.8701897995771 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_18 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.950027608323:ℝ):ℂ) + (((-0.3121658908722):ℝ):ℂ) * I)‖ ≤ 0.00000012954 := by
  have hl := lg_18
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.432510349448431216 69.43251038548147926 (-0.317472) 0.00000002953 0.950027608323 (-0.3121658908722) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_19 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0454627977029):ℝ):ℂ) + (((-0.9989660324679):ℝ):ℂ) * I)‖ ≤ 0.00000014019 := by
  have hl := lg_19
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.731313138802977266 70.731313174836049332 (-1.6162748) 0.00000004018 (-0.0454627977029) (-0.9989660324679) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_20 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9573382711507):ℝ):ℂ) + (((-0.2889696080313):ℝ):ℂ) * I)‖ ≤ 0.00000012865 := by
  have hl := lg_20
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.963480650336328598 71.96348069838035262 (-2.8484423) 0.00000002864 (-0.9573382711507) (-0.2889696080313) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_21 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6380086174879):ℝ):ℂ) + ((0.7700292228193:ℝ):ℂ) * I)‖ ≤ 0.00000013015 := by
  have hl := lg_21
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.135517980258822892 73.135518016291894958 2.2627057 0.00000003014 (-0.6380086174879) 0.7700292228193 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_22 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4128622547002:ℝ):ℂ) + ((0.910793477493:ℝ):ℂ) * I)‖ ≤ 0.0000001515 := by
  have hl := lg_22
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.253021789595799726 74.25302183763984777 1.1452019 0.00000005149 0.4128622547002 0.910793477493 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_23 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9970075376547:ℝ):ℂ) + ((0.0773043974156:ℝ):ℂ) * I)‖ ≤ 0.0000001561 := by
  have hl := lg_23
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.320842030072350052 75.320842078116422118 0.0773816 0.00000005609 0.9970075376547 0.0773043974156 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_24 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.585754712211:ℝ):ℂ) + (((-0.8104883818554):ℝ):ℂ) * I)‖ ≤ 0.00000014954 := by
  have hl := lg_24
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.343209087640715608 76.34320913568473963 (-0.9449854) 0.00000004953 0.585754712211 (-0.8104883818554) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_25 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3474169633335):ℝ):ℂ) + (((-0.9377107515571):ℝ):ℂ) * I)‖ ≤ 0.00000014616 := by
  have hl := lg_25
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.323835040006257196 77.32383508805030524 (-1.9256114) 0.00000004615 (-0.3474169633335) (-0.9377107515571) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_26 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9627445867813):ℝ):ℂ) + (((-0.2704123894732):ℝ):ℂ) * I)‖ ≤ 0.00000017328 := by
  have hl := lg_26
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.2659950113743974 78.265995059418445444 (-2.8677713) 0.00000007327 (-0.9627445867813) (-0.2704123894732) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_27 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8063884263537):ℝ):ℂ) + ((0.5913862576955:ℝ):ℂ) * I)‖ ≤ 0.00000011914 := by
  have hl := lg_27
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.172593176422746824 79.17259321245581889 2.5088158 0.00000001913 (-0.8063884263537) 0.5913862576955 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_28 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0643514757848):ℝ):ℂ) + ((0.9979272957305:ℝ):ℂ) * I)‖ ≤ 0.00000017318 := by
  have hl := lg_28
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.046216718451107284 80.046216766495155328 1.6351923 0.00000007317 (-0.0643514757848) 0.9979272957305 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_29 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.702260475781:ℝ):ℂ) + ((0.7119200967495:ℝ):ℂ) * I)‖ ≤ 0.00000015768 := by
  have hl := lg_29
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.889180402957435224 80.88918045100150729 0.7922286 0.00000005767 0.702260475781 0.7119200967495 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p022_30 : ‖exp (-((((((24022:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997545991025:ℝ):ℂ) + (((-0.0221526877256):ℝ):ℂ) * I)‖ ≤ 0.00000013204 := by
  have hl := lg_30
  refine (ecis_approx ((((24022:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.703563477310644206 81.70356352535469225 (-0.0221545) 0.00000003203 0.9997545991025 (-0.0221526877256) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_2 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.530640856603):ℝ):ℂ) + ((0.8475967681014:ℝ):ℂ) * I)‖ ≤ 0.00000012655 := by
  have hl := lg_2
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.7194031360163 16.7194031480768 2.1301528 0.00000002654 (-0.530640856603) 0.8475967681014 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_3 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2025003785948:ℝ):ℂ) + (((-0.9792821843927):ℝ):ℂ) * I)‖ ≤ 0.00000012004 := by
  have hl := lg_3
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.499627008693323844 26.499627020753847965 (-1.3668858) 0.00000002003 0.2025003785948 (-0.9792821843927) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_4 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4368405561484):ℝ):ℂ) + (((-0.8995389532976):ℝ):ℂ) * I)‖ ≤ 0.00000016027 := by
  have hl := lg_4
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.4388062720326 33.4388062961536 (-2.0228797) 0.00000006026 (-0.4368405561484) (-0.8995389532976) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_5 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4337552351754:ℝ):ℂ) + (((-0.9010307408507):ℝ):ℂ) * I)‖ ≤ 0.00000015434 := by
  have hl := lg_5
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.821251873282635289 38.82125189740365941 (-1.12214) 0.00000005433 0.4337552351754 (-0.9010307408507) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_6 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7225814401948:ℝ):ℂ) + ((0.6912858036196:ℝ):ℂ) * I)‖ ≤ 0.00000011859 := by
  have hl := lg_6
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.219030144709623844 43.219030168830647965 0.763267 0.00000001858 0.7225814401948 0.6912858036196 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_7 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9826423376914):ℝ):ℂ) + (((-0.1855102041243):ℝ):ℂ) * I)‖ ≤ 0.00000015745 := by
  have hl := lg_7
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.937298692822914062 46.937298716943962304 (-2.9550016) 0.00000005744 (-0.9826423376914) (-0.1855102041243) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_8 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9942517672227:ℝ):ℂ) + ((0.107067377733:ℝ):ℂ) * I)‖ ≤ 0.0000001494 := by
  have hl := lg_8
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.1582094080489 50.1582094442304 0.107273 0.00000004939 0.9942517672227 0.107067377733 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_9 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.917987193294):ℝ):ℂ) + (((-0.3966100261067):ℝ):ℂ) * I)‖ ≤ 0.00000014007 := by
  have hl := lg_9
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.999254017386647688 52.99925404150769593 (-2.7337716) 0.00000004006 (-0.917987193294) (-0.3966100261067) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_10 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5335425789367:ℝ):ℂ) + ((0.8457732062802:ℝ):ℂ) * I)‖ ≤ 0.00000015533 := by
  have hl := lg_10
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.540655009298935289 55.54065504548045941 1.0080127 0.00000005532 0.5335425789367 0.8457732062802 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_11 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2761944053243:ℝ):ℂ) + (((-0.9611017898576):ℝ):ℂ) * I)‖ ≤ 0.00000012794 := by
  have hl := lg_11
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.839631856359034493 57.839631892540582735 (-1.2909641) 0.00000002793 0.2761944053243 (-0.9611017898576) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_12 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9693628472717):ℝ):ℂ) + ((0.2456332022762:ℝ):ℂ) * I)‖ ≤ 0.00000014513 := by
  have hl := lg_12
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.938433280725923844 59.938433316907447965 2.8934198 0.00000004512 (-0.9693628472717) 0.2456332022762 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_13 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.571298201944:ℝ):ℂ) + ((0.8207425689311:ℝ):ℂ) * I)‖ ≤ 0.00000013929 := by
  have hl := lg_13
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.8691434325192857 61.869143468700833942 0.9627096 0.00000003928 0.571298201944 0.8207425689311 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_14 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6786680214917:ℝ):ℂ) + (((-0.7344451760374):ℝ):ℂ) * I)‖ ≤ 0.00000014297 := by
  have hl := lg_14
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.656701828839214062 63.656701865020762304 (-0.8248488) 0.00000004296 0.6786680214917 (-0.7344451760374) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_15 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7945277527553):ℝ):ℂ) + (((-0.6072278403157):ℝ):ℂ) * I)‖ ≤ 0.00000014638 := by
  have hl := lg_15
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.320878881975959133 65.320878918157507375 (-2.4890258) 0.00000004637 (-0.7945277527553) (-0.6072278403157) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_16 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6183405727732):ℝ):ℂ) + ((0.7859102595391:ℝ):ℂ) * I)‖ ≤ 0.00000013493 := by
  have hl := lg_16
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.8776125440652 66.8776125923072 2.2374258 0.00000003492 (-0.6183405727732) 0.7859102595391 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_17 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7143515487275:ℝ):ℂ) + ((0.6997870139054:ℝ):ℂ) * I)‖ ≤ 0.00000013209 := by
  have hl := lg_17
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.339939046899404514 68.339939095141428635 0.7750993 0.00000003208 0.7143515487275 0.6997870139054 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_18 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8232868870133:ℝ):ℂ) + (((-0.5676254942054):ℝ):ℂ) * I)‖ ≤ 0.00000012559 := by
  have hl := lg_18
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.718657153402947688 69.71865718958449593 (-0.6036188) 0.00000002558 0.8232868870133 (-0.5676254942054) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_19 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3306364494328):ℝ):ℂ) + (((-0.943758199066):ℝ):ℂ) * I)‖ ≤ 0.00000015488 := by
  have hl := lg_19
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.022812597663250963 71.022812633844823326 (-1.9077742) 0.00000005487 (-0.3306364494328) (-0.943758199066) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_20 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999941269764):ℝ):ℂ) + ((0.0034271465794:ℝ):ℂ) * I)‖ ≤ 0.00000014085 := by
  have hl := lg_20
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.260058145315235289 72.26005819355725941 3.1381655 0.00000004084 (-0.9999941269764) 0.0034271465794 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_21 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3806523693541):ℝ):ℂ) + ((0.9247182131342:ℝ):ℂ) * I)‖ ≤ 0.00000015156 := by
  have hl := lg_21
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.436925701516237906 73.436925737697810269 1.961298 0.00000005155 (-0.3806523693541) 0.9247182131342 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_22 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6680667350737:ℝ):ℂ) + ((0.7441013623748:ℝ):ℂ) * I)‖ ≤ 0.00000015448 := by
  have hl := lg_22
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.559034992375334493 74.559035040617382735 0.8391887 0.00000005447 0.6680667350737 0.7441013623748 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_23 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9729706234686:ℝ):ℂ) + (((-0.2309289195122):ℝ):ℂ) * I)‖ ≤ 0.00000012882 := by
  have hl := lg_23
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.631255957346397286 75.631256005588469649 (-0.2330323) 0.00000002881 0.9729706234686 (-0.2309289195122) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_24 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3061855348247:ℝ):ℂ) + (((-0.951971857916):ℝ):ℂ) * I)‖ ≤ 0.00000016943 := by
  have hl := lg_24
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.657836416742223844 76.657836464984247965 (-1.2596128) 0.00000006942 0.3061855348247 (-0.951971857916) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_25 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.62371287008):ℝ):ℂ) + (((-0.7816535394166):ℝ):ℂ) * I)‖ ≤ 0.0000001396 := by
  have hl := lg_25
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.642503746565270578 77.64250379480731882 (-2.2442801) 0.00000003959 (-0.62371287008) (-0.7816535394166) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_26 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9988129158529):ℝ):ℂ) + ((0.048710969501:ℝ):ℂ) * I)‖ ≤ 0.00000012481 := by
  have hl := lg_26
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.5885465685355857 78.588546616777633942 3.0928624 0.0000000248 (-0.9988129158529) 0.048710969501 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_27 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5742858811088):ℝ):ℂ) + ((0.8186548275977:ℝ):ℂ) * I)‖ ≤ 0.00000016727 := by
  have hl := lg_27
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.498881026079971532 79.498881062261543895 2.1825279 0.00000006726 (-0.5742858811088) 0.8186548275977 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_28 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2623843772865:ℝ):ℂ) + ((0.9649634389737:ℝ):ℂ) * I)‖ ≤ 0.00000012849 := by
  have hl := lg_28
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.376104964855514062 80.376105013097562304 1.305304 0.00000002848 0.2623843772865 0.9649634389737 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_29 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8965552255494:ℝ):ℂ) + ((0.4429319671689:ℝ):ℂ) * I)‖ ≤ 0.00000014495 := by
  have hl := lg_29
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.222542690023157732 81.222542738265230095 0.4588663 0.00000004494 0.8965552255494 0.4429319671689 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p121_30 : ‖exp (-((((((24121:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9362932423:ℝ):ℂ) + (((-0.3512192540612):ℝ):ℂ) * I)‖ ≤ 0.00000017291 := by
  have hl := lg_30
  refine (ecis_approx ((((24121:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.040282017992259133 82.040282066234307375 (-0.358873) 0.0000000729 0.9362932423 (-0.3512192540612) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_2 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4712741638105):ℝ):ℂ) + ((0.8819867700366:ℝ):ℂ) * I)‖ ≤ 0.00000011469 := by
  have hl := lg_2
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.788024706866 16.788024718976 2.0615312 0.00000001468 (-0.4712741638105) 0.8819867700366 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_3 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0950044273733:ℝ):ℂ) + (((-0.9954768499465):ℝ):ℂ) * I)‖ ≤ 0.00000010865 := by
  have hl := lg_3
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.60838962524573208 26.6083896373557563 (-1.4756484) 0.00000000864 0.0950044273733 (-0.9954768499465) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_4 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5558013190805):ℝ):ℂ) + (((-0.8313151590699):ℝ):ℂ) * I)‖ ≤ 0.00000012218 := by
  have hl := lg_4
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.576049413732 33.576049437952 (-2.1601229) 0.00000002217 (-0.5558013190805) (-0.8313151590699) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_5 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2853023999207:ℝ):ℂ) + (((-0.9584375517474):ℝ):ℂ) * I)‖ ≤ 0.00000011653 := by
  have hl := lg_5
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.98058622656214198 38.9805862507821662 (-1.2814744) 0.00000001652 0.2853023999207 (-0.9584375517474) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_6 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8332242794648:ℝ):ℂ) + ((0.5529351680897:ℝ):ℂ) * I)‖ ≤ 0.00000011816 := by
  have hl := lg_6
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.39641433211173208 43.3964143563317563 0.5858828 0.00000001815 0.8332242794648 0.5529351680897 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_7 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.999981673939):ℝ):ℂ) + ((0.0060540163089:ℝ):ℂ) * I)‖ ≤ 0.00000015992 := by
  have hl := lg_7
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.12994379752792084 47.12994382174796928 3.1355386 0.00000005991 (-0.999981673939) 0.0060540163089 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_8 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9951437739321:ℝ):ℂ) + (((-0.0984320537438):ℝ):ℂ) * I)‖ ≤ 0.00000013685 := by
  have hl := lg_8
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.364074120598 50.364074156928 (-0.0985917) 0.00000003684 0.9951437739321 (-0.0984320537438) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_9 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9819483174192):ℝ):ℂ) + (((-0.189149416019):ℝ):ℂ) * I)‖ ≤ 0.00000011729 := by
  have hl := lg_9
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.21677925049146416 53.2167792747115126 (-2.9512968) 0.00000001728 (-0.9819483174192) (-0.189149416019) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_10 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7108735905945:ℝ):ℂ) + ((0.7033197979549:ℝ):ℂ) * I)‖ ≤ 0.0000001312 := by
  have hl := lg_10
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.76861093342814198 55.7686109697581662 0.7800568 0.00000003119 0.7108735905945 0.7033197979549 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_11 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.042427887218:ℝ):ℂ) + (((-0.9990995317715):ℝ):ℂ) * I)‖ ≤ 0.00000016002 := by
  have hl := lg_11
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.07702348828886926 58.0770235246189177 (-1.5283557) 0.00000006001 0.042427887218 (-0.9990995317715) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_12 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8803585784896):ℝ):ℂ) + ((0.4743087319281:ℝ):ℂ) * I)‖ ≤ 0.00000013283 := by
  have hl := lg_12
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.18443903897773208 60.1844390753077563 2.647414 0.00000003282 (-0.8803585784896) 0.4743087319281 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_13 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7591568089842:ℝ):ℂ) + ((0.650907781005:ℝ):ℂ) * I)‖ ≤ 0.00000015298 := by
  have hl := lg_13
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.123073418830774 62.12307345516082244 0.7087796 0.00000005297 0.7591568089842 0.650907781005 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_14 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4659259711678:ℝ):ℂ) + (((-0.8848237052607):ℝ):ℂ) * I)‖ ≤ 0.00000016742 := by
  have hl := lg_14
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.91796850439392084 63.91796854072396928 (-1.0861155) 0.00000006741 0.4659259711678 (-0.8848237052607) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_15 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9269974037011):ℝ):ℂ) + (((-0.3750677450502):ℝ):ℂ) * I)‖ ≤ 0.00000012 := by
  have hl := lg_15
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.58897585180787406 65.5889758881379225 (-2.7571228) 0.00000001999 (-0.9269974037011) (-0.3750677450502) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_16 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3821697807813):ℝ):ℂ) + ((0.9240921267139:ℝ):ℂ) * I)‖ ≤ 0.00000015153 := by
  have hl := lg_16
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.152098827464 67.152098875904 1.9629395 0.00000005152 (-0.3821697807813) 0.9240921267139 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_17 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8801533356271:ℝ):ℂ) + ((0.474689483541:ℝ):ℂ) * I)‖ ≤ 0.00000013734 := by
  have hl := lg_17
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.62042716785803148 68.6204272162980557 0.4946112 0.00000003733 0.8801533356271 0.474689483541 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_18 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6295941548986:ℝ):ℂ) + (((-0.7769241920017):ℝ):ℂ) * I)‖ ≤ 0.00000012163 := by
  have hl := lg_18
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.00480395735746416 70.0048039936875126 (-0.8897656) 0.00000002162 0.6295941548986 (-0.7769241920017) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_19 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5879137511475):ℝ):ℂ) + (((-0.8089236188915):ℝ):ℂ) * I)‖ ≤ 0.00000012247 := by
  have hl := lg_19
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.31431205652352466 71.31431209285359732 (-2.1992737) 0.00000002246 (-0.5879137511475) (-0.8089236188915) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_20 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.955335113806):ℝ):ℂ) + ((0.2955246522897:ℝ):ℂ) * I)‖ ≤ 0.00000014588 := by
  have hl := lg_20
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.55663564029414198 72.5566356887341662 2.841588 0.00000004587 (-0.955335113806) 0.2955246522897 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_21 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0889760529656):ℝ):ℂ) + ((0.996033765491:ℝ):ℂ) * I)‖ ≤ 0.0000001634 := by
  have hl := lg_21
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.73833342277365292 73.73833345910372558 1.6598902 0.00000006339 (-0.0889760529656) 0.996033765491 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_22 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8611974019043:ℝ):ℂ) + ((0.5082706316061:ℝ):ℂ) * I)‖ ≤ 0.00000015745 := by
  have hl := lg_22
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.86504819515486926 74.8650482435949177 0.5331755 0.00000005744 0.8611974019043 0.5082706316061 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_23 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8559317762211:ℝ):ℂ) + (((-0.5170887684479):ℝ):ℂ) * I)‖ ≤ 0.00000014692 := by
  have hl := lg_23
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.94166988462044452 75.94166993306051718 (-0.5434462) 0.00000004691 0.8559317762211 (-0.5170887684479) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_24 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0034437663982):ℝ):ℂ) + (((-0.9999940702188):ℝ):ℂ) * I)‖ ≤ 0.00000014033 := by
  have hl := lg_24
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.97246374584373208 76.9724637942837563 (-1.5742401) 0.00000004032 (-0.0034437663982) (-0.9999940702188) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_25 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8372050811834):ℝ):ℂ) + (((-0.5468890673384):ℝ):ℂ) * I)‖ ≤ 0.00000013305 := by
  have hl := lg_25
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.96117245312428396 77.9611725015643324 (-2.5629488) 0.00000003304 (-0.8372050811834) (-0.5468890673384) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_26 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9318630416633):ℝ):ℂ) + ((0.3628102416125:ℝ):ℂ) * I)‖ ≤ 0.00000016765 := by
  have hl := lg_26
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.911098125696774 78.91109817413682244 2.7703108 0.00000006764 (-0.9318630416633) 0.3628102416125 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_27 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.281583295724):ℝ):ℂ) + ((0.9595367880221:ℝ):ℂ) * I)‖ ≤ 0.00000011875 := by
  have hl := lg_27
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.82516887573719624 79.8251689120672689 1.8562401 0.00000001874 (-0.281583295724) 0.9595367880221 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_28 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5608238466041:ℝ):ℂ) + ((0.8279351502867:ℝ):ℂ) * I)‖ ≤ 0.00000016638 := by
  have hl := lg_28
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.70599321125992084 80.70599325969996928 0.9754158 0.00000006637 0.5608238466041 0.8279351502867 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_29 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9921347051493:ℝ):ℂ) + ((0.1251747851537:ℝ):ℂ) * I)‖ ≤ 0.00000013221 := by
  have hl := lg_29
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.55590497708888024 81.5559050255289529 0.125504 0.0000000322 0.9921347051493 0.1251747851537 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p22_30 : ‖exp (-((((((24220:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7676747153824:ℝ):ℂ) + (((-0.6408397080102):ℝ):ℂ) * I)‖ ≤ 0.00000013468 := by
  have hl := lg_30
  refine (ecis_approx ((((24220:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.37700055867387406 82.3770006071139225 (-0.6955916) 0.00000003467 0.7676747153824 (-0.6408397080102) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_2 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4096891475017):ℝ):ℂ) + ((0.9122251928202:ℝ):ℂ) * I)‖ ≤ 0.00000014384 := by
  have hl := lg_2
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.8566462777157 16.8566462898752 1.9929096 0.00000004383 (-0.4096891475017) 0.9122251928202 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_3 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0136142526079):ℝ):ℂ) + (((-0.9999073217682):ℝ):ℂ) * I)‖ ≤ 0.00000012525 := by
  have hl := lg_3
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.717152241798140316 26.717152253957664635 (-1.584411) 0.00000002524 (-0.0136142526079) (-0.9999073217682) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_4 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6643095247246):ℝ):ℂ) + (((-0.7474575943434):ℝ):ℂ) * I)‖ ≤ 0.00000014387 := by
  have hl := lg_4
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.7132925554314 33.7132925797504 (-2.297366) 0.00000004386 (-0.6643095247246) (-0.7474575943434) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_5 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1296218738111:ℝ):ℂ) + (((-0.9915634976287):ℝ):ℂ) * I)‖ ≤ 0.0000001611 := by
  have hl := lg_5
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.139920579841648671 39.13992060416067299 (-1.4408087) 0.00000006109 0.1296218738111 (-0.9915634976287) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_6 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9177182609492:ℝ):ℂ) + ((0.3972319140255:ℝ):ℂ) * I)‖ ≤ 0.00000013076 := by
  have hl := lg_6
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.573798519513840316 43.573798543832864635 0.4084986 0.00000003075 0.9177182609492 0.3972319140255 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_7 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9803241866853):ℝ):ℂ) + ((0.1973942468095:ℝ):ℂ) * I)‖ ≤ 0.00000015522 := by
  have hl := lg_7
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.322588902232927618 47.322588926551976256 2.9428935 0.00000005521 (-0.9803241866853) 0.1973942468095 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_8 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9540100509984:ℝ):ℂ) + (((-0.2997746196629):ℝ):ℂ) * I)‖ ≤ 0.0000001243 := by
  have hl := lg_8
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.5699388331471 50.5699388696256 (-0.3044564) 0.00000002429 0.9540100509984 (-0.2997746196629) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_9 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996293037525):ℝ):ℂ) + ((0.0272259886222:ℝ):ℂ) * I)‖ ≤ 0.00000014331 := by
  have hl := lg_9
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.434304483596280632 53.43430450791532927 3.1143633 0.0000000433 (-0.9996293037525) 0.0272259886222 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_10 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8514245278406:ℝ):ℂ) + ((0.5244771428685:ℝ):ℂ) * I)‖ ≤ 0.00000012943 := by
  have hl := lg_10
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.996566857557348671 55.99656689403587299 0.5521009 0.00000002942 0.8514245278406 0.5244771428685 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_11 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1937185352125):ℝ):ℂ) + (((-0.9810571487504):ℝ):ℂ) * I)‖ ≤ 0.00000014441 := by
  have hl := lg_11
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.314415120218704027 58.314415156697252665 (-1.7657474) 0.0000000444 (-0.1937185352125) (-0.9810571487504) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_12 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7383442387794):ℝ):ℂ) + ((0.6744240394813:ℝ):ℂ) * I)‖ ≤ 0.00000016193 := by
  have hl := lg_12
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.430444797229540316 60.430444833708064635 2.4014083 0.00000006192 (-0.7383442387794) 0.6744240394813 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_13 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8983271131509:ℝ):ℂ) + ((0.4393272103774:ℝ):ℂ) * I)‖ ≤ 0.00000016667 := by
  have hl := lg_13
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.3770034051422623 62.377003441620810938 0.4548496 0.00000006666 0.8983271131509 0.4393272103774 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_14 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.221560279884:ℝ):ℂ) + (((-0.9751466773659):ℝ):ℂ) * I)‖ ≤ 0.00000014465 := by
  have hl := lg_14
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.179235179948627618 64.179235216427176256 (-1.3473821) 0.00000004464 0.221560279884 (-0.9751466773659) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_15 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9932363176214):ℝ):ℂ) + (((-0.1161103652155):ℝ):ℂ) * I)‖ ≤ 0.00000015017 := by
  have hl := lg_15
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.857072821639788987 65.857072858118337625 (-3.0252198) 0.00000005016 (-0.9932363176214) (-0.1161103652155) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_16 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1173856042763):ℝ):ℂ) + ((0.9930864110983:ℝ):ℂ) * I)‖ ≤ 0.00000016813 := by
  have hl := lg_16
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.4265851108628 67.4265851595008 1.6884532 0.00000006812 (-0.1173856042763) 0.9930864110983 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_17 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.977163102918:ℝ):ℂ) + ((0.2124906357834:ℝ):ℂ) * I)‖ ≤ 0.00000015849 := by
  have hl := lg_17
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.900915288816658446 68.900915337454682765 0.2141231 0.00000005848 0.977163102918 0.2124906357834 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_18 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3847010510467:ℝ):ℂ) + (((-0.9230412240651):ℝ):ℂ) * I)‖ ≤ 0.00000011883 := by
  have hl := lg_18
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.290950761311980632 70.29095079779052927 (-1.1759124) 0.00000001882 0.3847010510467 (-0.9230412240651) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_19 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7955876091355):ℝ):ℂ) + (((-0.6058385561703):ℝ):ℂ) * I)‖ ≤ 0.00000016361 := by
  have hl := lg_19
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.605811515383798357 71.605811551862371314 (-2.4907732) 0.0000000636 (-0.7955876091355) (-0.6058385561703) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_20 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8272606517431):ℝ):ℂ) + ((0.561818310503:ℝ):ℂ) * I)‖ ≤ 0.0000001509 := by
  have hl := lg_20
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.853213135273048671 72.85321318391107299 2.5450105 0.00000005089 (-0.8272606517431) 0.561818310503 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_21 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2107223339381:ℝ):ℂ) + ((0.9775459569655:ℝ):ℂ) * I)‖ ≤ 0.00000014214 := by
  have hl := lg_21
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.039741144031067934 74.039741180509640891 1.3584825 0.00000004213 0.2107223339381 0.9775459569655 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_22 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9743094057139:ℝ):ℂ) + ((0.2252136362156:ℝ):ℂ) * I)‖ ≤ 0.00000016043 := by
  have hl := lg_22
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.171061397934404027 75.171061446572452665 0.2271623 0.00000006042 0.9743094057139 0.2252136362156 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_23 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6570781432216:ℝ):ℂ) + (((-0.753822468291):ℝ):ℂ) * I)‖ ≤ 0.00000017428 := by
  have hl := lg_23
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.252083811894491754 76.252083860532564711 (-0.8538602) 0.00000007427 0.6570781432216 (-0.753822468291) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_24 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3127349709062):ℝ):ℂ) + (((-0.9498404276353):ℝ):ℂ) * I)‖ ≤ 0.00000013744 := by
  have hl := lg_24
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.287091074945240316 77.287091123583264635 (-1.8888674) 0.00000003743 (-0.3127349709062) (-0.9498404276353) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_25 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.966396365267):ℝ):ℂ) + (((-0.2570565403608):ℝ):ℂ) * I)‖ ≤ 0.00000012649 := by
  have hl := lg_25
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.279841159683297342 78.27984120832134598 (-2.8816175) 0.00000002648 (-0.966396365267) (-0.2570565403608) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_26 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7688002823047):ℝ):ℂ) + ((0.6394889568158:ℝ):ℂ) * I)‖ ≤ 0.00000013818 := by
  have hl := lg_26
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.2336496828579623 79.233649731496010938 2.4477593 0.00000003817 (-0.7688002823047) 0.6394889568158 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_27 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0408327714227:ℝ):ℂ) + ((0.9991659946064:ℝ):ℂ) * I)‖ ≤ 0.00000016796 := by
  have hl := lg_27
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.151456725394420948 80.151456761872993905 1.5299522 0.00000006795 0.0408327714227 0.9991659946064 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_28 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7987825236041:ℝ):ℂ) + ((0.6016198799779:ℝ):ℂ) * I)‖ ≤ 0.00000013569 := by
  have hl := lg_28
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.035881457664327618 81.035881506302376256 0.6455275 0.00000003568 0.7987825236041 0.6016198799779 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_29 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9784751298965:ℝ):ℂ) + (((-0.2063647745474):ℝ):ℂ) * I)‖ ≤ 0.0000001292 := by
  have hl := lg_29
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.889267264154602748 81.889267312792675705 (-0.2078583) 0.00000002919 0.9784751298965 (-0.2063647745474) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p319_30 : ‖exp (-((((((24319:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5128370266558:ℝ):ℂ) + (((-0.858485983631):ℝ):ℂ) * I)‖ ≤ 0.00000015467 := by
  have hl := lg_30
  refine (ecis_approx ((((24319:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.713719099355488987 82.713719147993537625 (-1.0323101) 0.00000005466 0.5128370266558 (-0.858485983631) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_2 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3461757868733):ℝ):ℂ) + ((0.9381696672672:ℝ):ℂ) * I)‖ ≤ 0.00000013925 := by
  have hl := lg_2
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.9252678485654 16.9252678607744 1.9242881 0.00000003924 (-0.3461757868733) 0.9381696672672 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_3 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1220720441614):ℝ):ℂ) + (((-0.9925212421071):ℝ):ℂ) * I)‖ ≤ 0.00000014186 := by
  have hl := lg_3
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.825914858350548552 26.82591487055957297 (-1.6931736) 0.00000004185 (-0.1220720441614) (-0.9925212421071) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_4 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7603247094499):ℝ):ℂ) + (((-0.6495431749802):ℝ):ℂ) * I)‖ ≤ 0.00000013878 := by
  have hl := lg_4
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.8505356971308 33.8505357215488 (-2.4346092) 0.00000003877 (-0.7603247094499) (-0.6495431749802) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_5 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0293425609845):ℝ):ℂ) + (((-0.9995694143553):ℝ):ℂ) * I)‖ ≤ 0.00000011448 := by
  have hl := lg_5
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.299254933121155362 39.29925495753917978 (-1.6001431) 0.00000001447 (-0.0293425609845) (-0.9995694143553) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_6 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9734117323138:ℝ):ℂ) + ((0.22906243558:ℝ):ℂ) * I)‖ ≤ 0.00000014336 := by
  have hl := lg_6
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.751182706915948552 43.75118273133397297 0.2311144 0.00000004335 0.9734117323138 0.22906243558 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_7 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9243971546578):ℝ):ℂ) + ((0.3814313834895:ℝ):ℂ) * I)‖ ≤ 0.00000015051 := by
  have hl := lg_7
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.515234006937934396 47.515234031355983232 2.7502484 0.0000000505 (-0.9243971546578) 0.3814313834895 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_8 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8725877089422:ℝ):ℂ) + (((-0.4884574599727):ℝ):ℂ) * I)‖ ≤ 0.0000001249 := by
  have hl := lg_8
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.7758035456962 50.7758035823232 (-0.5103211) 0.00000002489 0.8725877089422 (-0.4884574599727) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_9 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9701968059909):ℝ):ℂ) + ((0.2423182976432:ℝ):ℂ) * I)‖ ≤ 0.00000014793 := by
  have hl := lg_9
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.651829716701097104 53.65182974111914594 2.896838 0.00000004792 (-0.9701968059909) 0.2423182976432 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_10 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9479233890153:ℝ):ℂ) + ((0.3184984278733:ℝ):ℂ) * I)‖ ≤ 0.00000015371 := by
  have hl := lg_10
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.224522781686555362 56.22452281831357978 0.324145 0.0000000537 0.9479233890153 0.3184984278733 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_11 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4189990662702):ℝ):ℂ) + (((-0.9079866642529):ℝ):ℂ) * I)‖ ≤ 0.00000012417 := by
  have hl := lg_11
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.551806752148538794 58.55180678877558763 (-2.003139) 0.00000002416 (-0.4189990662702) (-0.9079866642529) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_12 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5518710013567):ℝ):ℂ) + ((0.8339294921351:ℝ):ℂ) * I)‖ ≤ 0.00000012033 := by
  have hl := lg_12
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.676450555481348552 60.67645059210837297 2.1554025 0.00000002032 (-0.5518710013567) 0.8339294921351 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_13 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9798834471898:ℝ):ℂ) + ((0.1995706138776:ℝ):ℂ) * I)‖ ≤ 0.0000001563 := by
  have hl := lg_13
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.6309333914537506 62.630933428080799436 0.2009197 0.00000005629 0.9798834471898 0.1995706138776 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_14 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0378434346207):ℝ):ℂ) + (((-0.9992836806712):ℝ):ℂ) * I)‖ ≤ 0.00000012035 := by
  have hl := lg_14
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.440501855503334396 64.440501892130383232 (-1.6086488) 0.00000002034 (-0.0378434346207) (-0.9992836806712) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_15 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9885119690541):ℝ):ℂ) + ((0.1511426036744:ℝ):ℂ) * I)‖ ≤ 0.00000014914 := by
  have hl := lg_15
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.125169791471703914 66.12516982809875275 2.9898686 0.00000004913 (-0.9885119690541) 0.1511426036744 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_16 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1561872359385:ℝ):ℂ) + ((0.987727466121:ℝ):ℂ) * I)‖ ≤ 0.00000016414 := by
  have hl := lg_16
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.7010713942616 67.7010714430976 1.413967 0.00000006413 0.1561872359385 0.987727466121 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_17 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9977986448862:ℝ):ℂ) + (((-0.0663163951321):ℝ):ℂ) * I)‖ ≤ 0.00000016922 := by
  have hl := lg_17
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.181403409775285412 69.18140345861130983 (-0.0663651) 0.00000006921 0.9977986448862 (-0.0663163951321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_18 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1085229731078:ℝ):ℂ) + (((-0.9940939413897):ℝ):ℂ) * I)‖ ≤ 0.00000012293 := by
  have hl := lg_18
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.577097565266497104 70.57709760189354594 (-1.4620592) 0.00000002292 0.1085229731078 (-0.9940939413897) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_19 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9361361348569):ℝ):ℂ) + (((-0.3516377921155):ℝ):ℂ) * I)‖ ≤ 0.00000013191 := by
  have hl := lg_19
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.897310974244072054 71.897311010871145308 (-2.7822726) 0.0000000319 (-0.9361361348569) (-0.3516377921155) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_20 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6269536112843):ℝ):ℂ) + ((0.7790565892688:ℝ):ℂ) * I)‖ ≤ 0.00000015592 := by
  have hl := lg_20
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.149790630251955362 73.14979067908797978 2.248433 0.00000005591 (-0.6269536112843) 0.7790565892688 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_21 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4914218008906:ℝ):ℂ) + ((0.8709217034897:ℝ):ℂ) * I)‖ ≤ 0.00000012088 := by
  have hl := lg_21
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.341148865288482948 74.341148901915556202 1.0570748 0.00000002087 0.4914218008906 0.8709217034897 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_22 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9968928781535:ℝ):ℂ) + (((-0.0787692166196):ℝ):ℂ) * I)‖ ≤ 0.00000016341 := by
  have hl := lg_22
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.477074600713938794 75.47707464954998763 (-0.0788509) 0.0000000634 0.9968928781535 (-0.0787692166196) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_23 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3954173856217:ℝ):ℂ) + (((-0.9185015466226):ℝ):ℂ) * I)‖ ≤ 0.000000147 := by
  have hl := lg_23
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.562497739168538988 76.562497788004612242 (-1.1642741) 0.00000004699 0.3954173856217 (-0.9185015466226) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_24 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5913229702285):ℝ):ℂ) + (((-0.8064348360957):ℝ):ℂ) * I)‖ ≤ 0.00000016674 := by
  have hl := lg_24
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.601718404046748552 77.60171845288277297 (-2.2034947) 0.00000006673 (-0.5913229702285) (-0.8064348360957) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_25 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9982780275457):ℝ):ℂ) + ((0.05865985991:ℝ):ℂ) * I)‖ ≤ 0.00000012711 := by
  have hl := lg_25
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.598509866242310724 78.59850991507835956 3.0828991 0.0000000271 (-0.9982780275457) 0.05865985991 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_26 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5264429347717):ℝ):ℂ) + ((0.8502104659562:ℝ):ℂ) * I)‖ ≤ 0.00000015333 := by
  have hl := lg_26
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.5562012400191506 79.556201288855199436 2.1252077 0.00000005332 (-0.5264429347717) 0.8502104659562 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_27 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3589399652576:ℝ):ℂ) + ((0.9333606491281:ℝ):ℂ) * I)‖ ≤ 0.00000011836 := by
  have hl := lg_27
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.477744575051645656 80.47774461167871891 1.2036644 0.00000001835 0.3589399652576 0.9333606491281 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_28 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9505981189601:ℝ):ℂ) + ((0.3104242519995:ℝ):ℂ) * I)‖ ≤ 0.00000015959 := by
  have hl := lg_28
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.365769704068734396 81.365769752904783232 0.3156393 0.00000005958 0.9505981189601 0.3104242519995 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_29 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8570804881935:ℝ):ℂ) + (((-0.5151825276132):ℝ):ℂ) * I)‖ ≤ 0.00000014213 := by
  have hl := lg_29
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.222629551220325256 82.22262960005639851 (-0.5412206) 0.00000004212 0.8570804881935 (-0.5151825276132) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p418_30 : ‖exp (-((((((24418:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2004014114652:ℝ):ℂ) + (((-0.9797138736808):ℝ):ℂ) * I)‖ ≤ 0.00000015331 := by
  have hl := lg_30
  refine (ecis_approx ((((24418:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.050437640037103914 83.05043768887315275 (-1.3690287) 0.0000000533 0.2004014114652 (-0.9797138736808) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_2 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2976201543502):ℝ):ℂ) + ((0.9546843686386:ℝ):ℂ) * I)‖ ≤ 0.00000013063 := by
  have hl := lg_2
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.9765607399076 16.9765607521536 1.8729952 0.00000003062 (-0.2976201543502) 0.9546843686386 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_3 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2022693078132):ℝ):ℂ) + (((-0.9793299378227):ℝ):ℂ) * I)‖ ≤ 0.00000015124 := by
  have hl := lg_3
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.907212167692752688 26.90721217993877718 (-1.7744709) 0.00000005123 (-0.2022693078132) (-0.9793299378227) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_4 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8228445401828):ℝ):ℂ) + (((-0.5682665418906):ℝ):ℂ) * I)‖ ≤ 0.0000001561 := by
  have hl := lg_4
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.9531214798152 33.9531215043072 (-2.537195) 0.00000005609 (-0.8228445401828) (-0.5682665418906) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_5 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1479005846948):ℝ):ℂ) + (((-0.9890022330846):ℝ):ℂ) * I)‖ ≤ 0.00000012003 := by
  have hl := lg_5
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.418353338602806828 39.41835336309483132 (-1.7192415) 0.00000002002 (-0.1479005846948) (-0.9890022330846) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_6 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9951504158286:ℝ):ℂ) + ((0.0983648813149:ℝ):ℂ) * I)‖ ≤ 0.00000014267 := by
  have hl := lg_6
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.883772907600352688 43.88377293209237718 0.0985242 0.00000004266 0.9951504158286 0.0983648813149 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_7 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8600944410414):ℝ):ℂ) + ((0.5101348374785:ℝ):ℂ) * I)‖ ≤ 0.000000125 := by
  have hl := lg_7
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.659231357929555624 47.659231382421604608 2.6062511 0.00000002499 (-0.8600944410414) 0.5101348374785 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_8 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7874103038545:ℝ):ℂ) + (((-0.6164292444262):ℝ):ℂ) * I)‖ ≤ 0.00000013773 := by
  have hl := lg_8
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.9296822197228 50.9296822564608 (-0.6641998) 0.00000003772 0.7874103038545 (-0.6164292444262) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p492_9 : ‖exp (-((((((24492:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9181742117275):ℝ):ℂ) + ((0.396176875623:ℝ):ℂ) * I)‖ ≤ 0.00000012925 := by
  have hl := lg_9
  refine (ecis_approx ((((24492:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.814424335385505376 53.81442435987755436 2.7342434 0.00000002924 (-0.9181742117275) 0.396176875623 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
