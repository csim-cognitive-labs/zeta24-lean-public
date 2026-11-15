/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 4

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

lemma cs_b1left_v14p705_12 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4006596778823:ℝ):ℂ) + ((0.9162269492431:ℝ):ℂ) * I)‖ ≤ 0.00000015266 := by
  have hl := lg_12
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.54055227366505162 36.540552295722566325 1.1585596 0.00000005265 0.4006596778823 0.9162269492431 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_13 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9998294621013:ℝ):ℂ) + (((-0.0184674501283):ℝ):ℂ) * I)‖ ≤ 0.00000015309 := by
  have hl := lg_13
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.7175802900043985 37.71758031206192791 (-0.0184685) 0.00000005308 0.9998294621013 (-0.0184674501283) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_14 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4462496067034:ℝ):ℂ) + (((-0.8949085363975):ℝ):ℂ) * I)‖ ≤ 0.00000012257 := by
  have hl := lg_14
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.80733802052488051 38.80733804258240992 (-1.1082262) 0.00000002256 0.4462496067034 (-0.8949085363975) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_15 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5243657492381):ℝ):ℂ) + (((-0.8514931362135):ℝ):ℂ) * I)‖ ≤ 0.00000014735 := by
  have hl := lg_15
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.821878195740494965 39.821878217798024375 (-2.1227664) 0.00000004734 (-0.5243657492381) (-0.8514931362135) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_16 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.997565850545):ℝ):ℂ) + (((-0.0697307198722):ℝ):ℂ) * I)‖ ≤ 0.00000013159 := by
  have hl := lg_16
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.770917145246 40.770917174656 (-3.0718053) 0.00000003158 (-0.997565850545) (-0.0697307198722) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_17 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6809789192185):ℝ):ℂ) + ((0.7323030189472:ℝ):ℂ) * I)‖ ≤ 0.00000014122 := by
  have hl := lg_17
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.66240220905666197 41.662402238466676675 2.3198949 0.00000004121 (-0.6809789192185) 0.7323030189472 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_18 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.091288555209:ℝ):ℂ) + ((0.9958244823701:ℝ):ℂ) * I)‖ ≤ 0.00000016021 := by
  have hl := lg_18
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.50291668839560324 42.50291671045313265 1.4793805 0.0000000602 0.091288555209 0.9958244823701 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_19 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7748478213669:ℝ):ℂ) + ((0.6321478100279:ℝ):ℂ) * I)‖ ≤ 0.00000014899 := by
  have hl := lg_19
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.297975177174997115 43.29797519923254123 0.684322 0.00000004898 0.7748478213669 0.6321478100279 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_20 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9975547827015:ℝ):ℂ) + (((-0.0698888797261):ℝ):ℂ) * I)‖ ≤ 0.00000014649 := by
  have hl := lg_20
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.052243067321443345 44.05224309673145805 (-0.0699459) 0.00000004648 0.9975547827015 (-0.0698888797261) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_21 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7056860979133:ℝ):ℂ) + (((-0.7085246158123):ℝ):ℂ) * I)‖ ≤ 0.00000011502 := by
  have hl := lg_21
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.76970243525543213 44.769702457312976245 (-0.7874053) 0.00000001501 0.7056860979133 (-0.7085246158123) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_22 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0991510460297:ℝ):ℂ) + (((-0.995072394387):ℝ):ℂ) * I)‖ ≤ 0.00000014051 := by
  have hl := lg_22
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.453779261344027765 45.453779290754057175 (-1.4714821) 0.0000000405 0.0991510460297 (-0.995072394387) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_23 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5263898806138):ℝ):ℂ) + (((-0.8502433143401):ℝ):ℂ) * I)‖ ≤ 0.00000012032 := by
  have hl := lg_23
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.10744242994812703 46.107442459358171145 (-2.1251453) 0.00000002031 (-0.5263898806138) (-0.8502433143401) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_24 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9246776377594):ℝ):ℂ) + (((-0.3807509239349):ℝ):ℂ) * I)‖ ≤ 0.00000013914 := by
  have hl := lg_24
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.73328155997655162 46.733281589386566325 (-2.7509844) 0.00000003913 (-0.9246776377594) (-0.3807509239349) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_25 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9780977478663):ℝ):ℂ) + ((0.2081460912584:ℝ):ℂ) * I)‖ ≤ 0.00000016139 := by
  have hl := lg_25
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.33356898939688669 47.3335690188069161 2.9319135 0.00000006138 (-0.9780977478663) 0.2081460912584 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_26 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7063840389714):ℝ):ℂ) + ((0.7078287854147:ℝ):ℂ) * I)‖ ≤ 0.0000001483 := by
  have hl := lg_26
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.9103095763158985 47.91030960572592791 2.3551729 0.00000004829 (-0.7063840389714) 0.7078287854147 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_27 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2273981256167):ℝ):ℂ) + ((0.9738018753653:ℝ):ℂ) * I)‖ ≤ 0.00000015433 := by
  have hl := lg_27
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.46528110312615486 48.465281125183698975 1.8002013 0.00000005432 (-0.2273981256167) 0.9738018753653 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_28 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3006567853956:ℝ):ℂ) + ((0.9537324034526:ℝ):ℂ) * I)‖ ≤ 0.00000015062 := by
  have hl := lg_28
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.00006730683638051 49.00006733624640992 1.2654151 0.00000005061 0.3006567853956 0.9537324034526 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_29 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7320995596376:ℝ):ℂ) + ((0.681197647367:ℝ):ℂ) * I)‖ ≤ 0.00000013665 := by
  have hl := lg_29
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.51608516466110586 49.516085194071149975 0.7493973 0.00000003664 0.7320995596376 0.681197647367 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_30 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9686955723622:ℝ):ℂ) + ((0.248251662806:ℝ):ℂ) * I)‖ ≤ 0.00000015404 := by
  have hl := lg_30
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.014607482051994965 50.014607511462024375 0.250875 0.00000005403 0.9686955723622 0.248251662806 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_2 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6700109020563):ℝ):ℂ) + ((0.742351258574:ℝ):ℂ) * I)‖ ≤ 0.00000015022 := by
  have hl := lg_2
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.2613508571612 10.2613508645632 2.3050198 0.00000005021 (-0.6700109020563) 0.742351258574 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_3 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8494295127917):ℝ):ℂ) + ((0.5277020965706:ℝ):ℂ) * I)‖ ≤ 0.00000010396 := by
  have hl := lg_3
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.263856317594459856 16.26385632499647466 2.5856996 0.00000000395 (-0.8494295127917) 0.5277020965706 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_4 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1021708745801):ℝ):ℂ) + (((-0.9947668633339):ℝ):ℂ) * I)‖ ≤ 0.0000001076 := by
  have hl := lg_4
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.5227017143224 20.5227017291264 (-1.6731458) 0.00000000759 (-0.1021708745801) (-0.9947668633339) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_5 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2611119418217:ℝ):ℂ) + ((0.9653085277972:ℝ):ℂ) * I)‖ ≤ 0.00000013408 := by
  have hl := lg_5
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.826118847977950036 23.82611886278196484 1.3066224 0.00000003407 0.2611119418217 0.9653085277972 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_6 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1773866271872:ℝ):ℂ) + (((-0.9841412421472):ℝ):ℂ) * I)‖ ≤ 0.00000015398 := by
  have hl := lg_6
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.525207174755659856 26.52520718955967466 (-1.392466) 0.00000005397 0.1773866271872 (-0.9841412421472) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_7 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8613272604976):ℝ):ℂ) + ((0.5080505390632:ℝ):ℂ) * I)‖ ≤ 0.00000011784 := by
  have hl := lg_7
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.807253838918387288 28.807253853722416896 2.6086727 0.00000001783 (-0.8613272604976) 0.5080505390632 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_8 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8069220328362:ℝ):ℂ) + ((0.5906579661052:ℝ):ℂ) * I)‖ ≤ 0.00000015781 := by
  have hl := lg_8
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.7840525714836 30.7840525936896 0.631874 0.0000000578 0.8069220328362 0.5906579661052 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_9 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4430610009008:ℝ):ℂ) + (((-0.8964914664852):ℝ):ℂ) * I)‖ ≤ 0.00000011411 := by
  have hl := lg_9
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.527712635188919712 32.52771264999294932 (-1.1117861) 0.0000000141 0.4430610009008 (-0.8964914664852) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_10 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8915458902219):ℝ):ℂ) + (((-0.4529303760195):ℝ):ℂ) * I)‖ ≤ 0.00000013077 := by
  have hl := lg_10
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.087469705139150036 34.08746972734516484 (-2.6715432) 0.00000003076 (-0.8915458902219) (-0.4529303760195) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_11 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5890428393359):ℝ):ℂ) + ((0.8081018088186:ℝ):ℂ) * I)‖ ≤ 0.00000013613 := by
  have hl := lg_11
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.498441606962362532 35.49844162916839214 2.2006702 0.00000003612 (-0.5890428393359) 0.8081018088186 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_12 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6117275156386:ℝ):ℂ) + ((0.7910685473527:ℝ):ℂ) * I)‖ ≤ 0.00000011118 := by
  have hl := lg_12
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.786558031916859856 36.78655805412287466 0.9125538 0.00000001117 0.6117275156386 0.7910685473527 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_13 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9631283963423:ℝ):ℂ) + (((-0.2690421754283):ℝ):ℂ) * I)‖ ≤ 0.00000015546 := by
  have hl := lg_13
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.9715102763158868 37.971510298521916408 (-0.2723984) 0.00000005545 0.9631283963423 (-0.2690421754283) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_14 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1999466067099:ℝ):ℂ) + (((-0.9798067944575):ℝ):ℂ) * I)‖ ≤ 0.00000014701 := by
  have hl := lg_14
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.068604696079587288 39.068604718285616896 (-1.3694929) 0.000000047 0.1999466067099 (-0.9798067944575) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_15 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7311915186234):ℝ):ℂ) + (((-0.6821722385613):ℝ):ℂ) * I)‖ ≤ 0.00000014472 := by
  have hl := lg_15
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.089975165572409892 40.0899751877784395 (-2.3908633) 0.00000004471 (-0.7311915186234) (-0.6821722385613) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_16 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9791222231857):ℝ):ℂ) + ((0.2032724077319:ℝ):ℂ) * I)‖ ≤ 0.00000012163 := by
  have hl := lg_16
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.0454034286448 41.0454034582528 2.9368937 0.00000002162 (-0.9791222231857) 0.2032724077319 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_17 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4516469905389):ℝ):ℂ) + ((0.8921967249058:ℝ):ℂ) * I)‖ ≤ 0.00000012026 := by
  have hl := lg_17
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.942890330015288936 41.94289035962330374 2.0394068 0.00000002025 (-0.4516469905389) 0.8921967249058 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_18 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.368655960532:ℝ):ℂ) + ((0.9295659109306:ℝ):ℂ) * I)‖ ≤ 0.00000015792 := by
  have hl := lg_18
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.789063492350119712 42.78906351455614932 1.1932336 0.00000005791 0.368655960532 0.9295659109306 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_19 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.923832295336:ℝ):ℂ) + ((0.3827974530928:ℝ):ℂ) * I)‖ ≤ 0.00000011424 := by
  have hl := lg_19
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.589474636035270812 43.589474658241315224 0.3928225 0.00000001423 0.923832295336 0.3827974530928 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_20 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9335789008873:ℝ):ℂ) + (((-0.3583719238697):ℝ):ℂ) * I)‖ ≤ 0.00000014167 := by
  have hl := lg_20
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.348820562300350036 44.34882059190836484 (-0.3665234) 0.00000004166 0.9335789008873 (-0.3583719238697) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_21 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4635374669619:ℝ):ℂ) + (((-0.8860773198331):ℝ):ℂ) * I)‖ ≤ 0.00000012848 := by
  have hl := lg_21
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.071110156512847144 45.071110178718891556 (-1.088813) 0.00000002847 0.4635374669619 (-0.8860773198331) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_22 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2052302636843):ℝ):ℂ) + (((-0.978713716501):ℝ):ℂ) * I)‖ ≤ 0.00000014349 := by
  have hl := lg_22
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.759792464123562532 45.75979249373159214 (-1.7774953) 0.00000004348 (-0.2052302636843) (-0.978713716501) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_23 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7609414322768):ℝ):ℂ) + (((-0.6488205735085):ℝ):ℂ) * I)‖ ≤ 0.00000013659 := by
  have hl := lg_23
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.417856357222174264 46.417856386830218676 (-2.4355592) 0.00000003658 (-0.7609414322768) (-0.6488205735085) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_24 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9971148431245):ℝ):ℂ) + (((-0.0759077670622):ℝ):ℂ) * I)‖ ≤ 0.00000016119 := by
  have hl := lg_24
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.047908889078059856 47.04790891868607466 (-3.0656118) 0.00000006118 (-0.9971148431245) (-0.0759077670622) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_25 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.863641057244):ℝ):ℂ) + ((0.5041072546189:ℝ):ℂ) * I)‖ ≤ 0.0000001615 := by
  have hl := lg_25
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.652237695955900072 47.65223772556392968 2.6132447 0.00000006149 (-0.863641057244) 0.5041072546189 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_26 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4455826385658):ℝ):ℂ) + ((0.8952408124099:ℝ):ℂ) * I)‖ ≤ 0.00000012397 := by
  have hl := lg_26
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.2328611334770868 48.232861163085116408 2.0326213 0.00000002396 (-0.4455826385658) 0.8952408124099 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_27 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.096731336318:ℝ):ℂ) + ((0.9953105287166:ℝ):ℂ) * I)‖ ≤ 0.00000011757 := by
  have hl := lg_27
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.791568952783379568 48.79156897498942398 1.4739135 0.00000001756 0.096731336318 0.9953105287166 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_28 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5933944007104:ℝ):ℂ) + ((0.8049118493385:ℝ):ℂ) * I)‖ ≤ 0.00000012543 := by
  have hl := lg_28
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.329955553240787288 49.329955582848816896 0.9355269 0.00000002542 0.5933944007104 0.8049118493385 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_29 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9146985288435:ℝ):ℂ) + ((0.4041368596547:ℝ):ℂ) * I)‖ ≤ 0.00000012391 := by
  have hl := lg_29
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.849447451726828368 49.84944748133487278 0.416035 0.0000000239 0.9146985288435 0.4041368596547 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p804_30 : ‖exp (-((((((14804:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9963177002798:ℝ):ℂ) + (((-0.0857382068229):ℝ):ℂ) * I)‖ ≤ 0.00000013472 := by
  have hl := lg_30
  refine (ecis_approx ((((14804:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.351326022733609892 50.3513260523416395 (-0.0858436) 0.00000003471 0.9963177002798 (-0.0857382068229) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_2 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6175326450607):ℝ):ℂ) + ((0.7865452512544:ℝ):ℂ) * I)‖ ≤ 0.00000012112 := by
  have hl := lg_2
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.3299724280109 10.3299724354624 2.2363982 0.00000002111 (-0.6175326450607) 0.7865452512544 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_3 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7871292205587):ℝ):ℂ) + ((0.6167881241546:ℝ):ℂ) * I)‖ ≤ 0.00000012007 := by
  have hl := lg_3
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.372618934146868092 16.372618941598382995 2.476937 0.00000002006 (-0.7871292205587) 0.6167881241546 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_4 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2373068575914):ℝ):ℂ) + (((-0.9714347406486):ℝ):ℂ) * I)‖ ≤ 0.0000001494 := by
  have hl := lg_4
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.6599448560218 20.6599448709248 (-1.8103889) 0.00000004939 (-0.2373068575914) (-0.9714347406486) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_5 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4109613514555:ℝ):ℂ) + ((0.9116527670171:ℝ):ℂ) * I)‖ ≤ 0.00000012748 := by
  have hl := lg_5
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.985453201257456727 23.98545321616047163 1.147288 0.00000002747 0.4109613514555 0.9116527670171 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_6 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0009462266537:ℝ):ℂ) + (((-0.9999995523274):ℝ):ℂ) * I)‖ ≤ 0.00000014836 := by
  have hl := lg_6
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.702591362157768092 26.702591377060782995 (-1.5698501) 0.00000004835 0.0009462266537 (-0.9999995523274) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_7 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7481245954256):ℝ):ℂ) + ((0.6635582790425:ℝ):ℂ) * I)‖ ≤ 0.00000012264 := by
  have hl := lg_7
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.999898943623394066 28.999898958526423872 2.4160276 0.00000002263 (-0.7481245954256) 0.6635582790425 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_8 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9106221549523:ℝ):ℂ) + ((0.4132399919055:ℝ):ℂ) * I)‖ ≤ 0.00000015188 := by
  have hl := lg_8
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.9899172840327 30.9899173063872 0.4260092 0.00000005187 0.9106221549523 0.4132399919055 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_9 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2391448267132:ℝ):ℂ) + (((-0.9709839091645):ℝ):ℂ) * I)‖ ≤ 0.00000014731 := by
  have hl := lg_9
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.745237868293736184 32.74523788319676599 (-1.3293113) 0.0000000473 0.2391448267132 (-0.9709839091645) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_10 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.970838203251):ℝ):ℂ) + (((-0.2397356519859):ℝ):ℂ) * I)‖ ≤ 0.00000011574 := by
  have hl := lg_10
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.315425629268356727 34.31542565162287163 (-2.8994991) 0.00000001573 (-0.970838203251) (-0.2397356519859) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_11 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3824831184428):ℝ):ℂ) + ((0.9239624798136:ℝ):ℂ) * I)‖ ≤ 0.00000011818 := by
  have hl := lg_11
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.735833238892197299 35.735833261246727105 1.9632786 0.00000001817 (-0.3824831184428) 0.9239624798136 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_12 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7859606351267:ℝ):ℂ) + ((0.6182765400945:ℝ):ℂ) * I)‖ ≤ 0.00000015292 := by
  have hl := lg_12
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.032563790168668092 37.032563812523182995 0.666548 0.00000005291 0.7859606351267 0.6182765400945 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_13 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.864657366968:ℝ):ℂ) + (((-0.5023620584279):ℝ):ℂ) * I)‖ ≤ 0.00000014192 := by
  have hl := lg_13
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.2254402626273751 38.225440284981904906 (-0.5263284) 0.00000004191 0.864657366968 (-0.5023620584279) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_14 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0599272459123):ℝ):ℂ) + (((-0.9982027475403):ℝ):ℂ) * I)‖ ≤ 0.00000015093 := by
  have hl := lg_14
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.329871371634294066 39.329871393988823872 (-1.6307595) 0.00000005092 (-0.0599272459123) (-0.9982027475403) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p903_15 : ‖exp (-((((((14903:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8857762849656):ℝ):ℂ) + (((-0.4641124571599):ℝ):ℂ) * I)‖ ≤ 0.0000001147 := by
  have hl := lg_15
  refine (ecis_approx ((((14903:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.358072135404324819 40.358072157758854625 (-2.6589603) 0.00000001469 (-0.8857762849656) (-0.4641124571599) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_2 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5430847328786):ℝ):ℂ) + ((0.8396778983074:ℝ):ℂ) * I)‖ ≤ 0.00000014898 := by
  have hl := lg_2
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.4214678558105 10.421467863328 2.1449028 0.00000004897 (-0.5430847328786) 0.8396778983074 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_3 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6897356336216):ℝ):ℂ) + ((0.7240612927719:ℝ):ℂ) * I)‖ ≤ 0.00000014221 := by
  have hl := lg_3
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.51763575621674574 16.517635763734260775 2.3319202 0.0000000422 (-0.6897356336216) 0.7240612927719 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_4 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4101180304828):ℝ):ℂ) + (((-0.9120324561491):ℝ):ℂ) * I)‖ ≤ 0.00000010993 := by
  have hl := lg_4
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.842935711621 20.842935726656 (-1.9933798) 0.00000000992 (-0.4101180304828) (-0.9120324561491) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_5 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5939453847148:ℝ):ℂ) + ((0.8045053635471:ℝ):ℂ) * I)‖ ≤ 0.0000001231 := by
  have hl := lg_5
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.197899005630132315 24.19789902066514735 0.9348422 0.00000002309 0.5939453847148 0.8045053635471 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_6 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2333934624874):ℝ):ℂ) + (((-0.9723823793483):ℝ):ℂ) * I)‖ ≤ 0.00000011671 := by
  have hl := lg_6
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.93910361202724574 26.939103627062260775 (-1.8063624) 0.0000000167 (-0.2333934624874) (-0.9723823793483) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_7 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.555006743849):ℝ):ℂ) + ((0.8318458476624:ℝ):ℂ) * I)‖ ≤ 0.00000015268 := by
  have hl := lg_7
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.25675908323006977 29.25675909826509984 2.1591674 0.00000005267 (-0.555006743849) 0.8318458476624 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_8 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9885423370069:ℝ):ℂ) + ((0.1509438569301:ℝ):ℂ) * I)‖ ≤ 0.0000001541 := by
  have hl := lg_8
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.2644035674315 31.264403589984 0.151523 0.00000005409 0.9885423370069 0.1509438569301 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_9 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0485296041285):ℝ):ℂ) + (((-0.9988217446185):ℝ):ℂ) * I)‖ ≤ 0.00000012348 := by
  have hl := lg_9
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.03527151243349148 33.03527152746852155 (-1.619345) 0.00000002347 (-0.0485296041285) (-0.9988217446185) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_10 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9980880431874):ℝ):ℂ) + ((0.0618082316352:ℝ):ℂ) * I)‖ ≤ 0.00000014093 := by
  have hl := lg_10
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.619366861440632315 34.61936688399314735 3.079745 0.00000004092 (-0.9980880431874) 0.0618082316352 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_11 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0758870468576):ℝ):ℂ) + ((0.9971164205442:ℝ):ℂ) * I)‖ ≤ 0.00000012829 := by
  have hl := lg_11
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.052355414798643655 36.052355437351173725 1.6467564 0.00000002828 (-0.0758870468576) 0.9971164205442 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_12 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9432404188779:ℝ):ℂ) + ((0.3321106926839:ℝ):ℂ) * I)‖ ≤ 0.00000014733 := by
  have hl := lg_12
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.36057146783774574 37.360571490390260775 0.3385404 0.00000004732 0.9432404188779 0.3321106926839 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_13 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.648714928217:ℝ):ℂ) + (((-0.7610314986309):ℝ):ℂ) * I)‖ ≤ 0.0000001572 := by
  have hl := lg_13
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.5640135777093595 38.56401360026188957 (-0.8649017) 0.00000005719 0.648714928217 (-0.7610314986309) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_14 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3970668772702):ℝ):ℂ) + (((-0.9177896790505):ℝ):ℂ) * I)‖ ≤ 0.00000011853 := by
  have hl := lg_14
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.67822693904056977 39.67822696159309984 (-1.9791151) 0.00000001852 (-0.3970668772702) (-0.9177896790505) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p035_15 : ‖exp (-((((((15035:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.992176488758):ℝ):ℂ) + (((-0.1248431604974):ℝ):ℂ) * I)‖ ≤ 0.00000014134 := by
  have hl := lg_15
  refine (ecis_approx ((((15035:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.715534761846878055 40.715534784399408125 (-3.0164229) 0.00000004133 (-0.992176488758) (-0.1248431604974) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_2 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4640935188713):ℝ):ℂ) + ((0.8857862076916:ℝ):ℂ) * I)‖ ≤ 0.00000013076 := by
  have hl := lg_2
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.5129632836101 10.5129632911936 2.0534073 0.00000003075 (-0.4640935188713) 0.8857862076916 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_3 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.577862314921):ℝ):ℂ) + ((0.8161342689679:ℝ):ℂ) * I)‖ ≤ 0.00000014327 := by
  have hl := lg_3
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.662652578286623388 16.662652585870138555 2.1869033 0.00000004326 (-0.577862314921) 0.8161342689679 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_4 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5692344055798):ℝ):ℂ) + (((-0.8221752802745):ℝ):ℂ) * I)‖ ≤ 0.00000015433 := by
  have hl := lg_4
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.0259265672202 21.0259265823872 (-2.1763707) 0.00000005432 (-0.5692344055798) (-0.8221752802745) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_5 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7502234225166:ℝ):ℂ) + ((0.6611844041623:ℝ):ℂ) * I)‖ ≤ 0.00000011873 := by
  have hl := lg_5
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.410344810002807903 24.41034482516982307 0.7223964 0.00000001872 0.7502234225166 0.6611844041623 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_6 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4547382284718):ℝ):ℂ) + (((-0.8906251419995):ℝ):ℂ) * I)‖ ≤ 0.00000014836 := by
  have hl := lg_6
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.175615861896723388 27.175615877063738555 (-2.0428746) 0.00000004835 (-0.4547382284718) (-0.8906251419995) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_7 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3254721025815):ℝ):ℂ) + ((0.9455516434543:ℝ):ℂ) * I)‖ ≤ 0.00000011308 := by
  have hl := lg_7
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.513619222836745474 29.513619238003775808 1.9023073 0.00000001307 (-0.3254721025815) 0.9455516434543 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_8 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9924495341931:ℝ):ℂ) + (((-0.122653667209):ℝ):ℂ) * I)‖ ≤ 0.0000001377 := by
  have hl := lg_8
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.5388898508303 31.5388898735808 (-0.1229633) 0.00000003769 0.9924495341931 (-0.122653667209) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_9 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3321501888923):ℝ):ℂ) + (((-0.9432265115107):ℝ):ℂ) * I)‖ ≤ 0.00000013586 := by
  have hl := lg_9
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.325305156573246776 33.32530517174027711 (-1.9093786) 0.00000003585 (-0.3321501888923) (-0.9432265115107) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_10 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9338418539894):ℝ):ℂ) + ((0.3576861635161:ℝ):ℂ) * I)‖ ≤ 0.00000014948 := by
  have hl := lg_10
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.923308093612907903 34.92330811636342307 2.7758037 0.00000004947 (-0.9338418539894) 0.3576861635161 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_11 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2382486039455:ℝ):ℂ) + ((0.9712042023787:ℝ):ℂ) * I)‖ ≤ 0.00000015239 := by
  have hl := lg_11
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.368877590705090011 36.368877613455620345 1.3302342 0.00000005238 0.2382486039455 0.9712042023787 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_12 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999445316282:ℝ):ℂ) + ((0.0105325052554:ℝ):ℂ) * I)‖ ≤ 0.00000012519 := by
  have hl := lg_12
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.688579145506823388 37.688579168257338555 0.0105327 0.00000002518 0.9999445316282 0.0105325052554 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_13 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3591166439962:ℝ):ℂ) + (((-0.9332926850699):ℝ):ℂ) * I)‖ ≤ 0.0000001503 := by
  have hl := lg_13
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.9025868927913439 38.902586915541874234 (-1.2034751) 0.00000005029 0.3591166439962 (-0.9332926850699) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_14 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6865071058309):ℝ):ℂ) + (((-0.7271230938583):ℝ):ℂ) * I)‖ ≤ 0.00000013665 := by
  have hl := lg_14
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.026582506446845474 40.026582529197375808 (-2.3274707) 0.00000003664 (-0.6865071058309) (-0.7271230938583) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p167_15 : ‖exp (-((((((15167:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9731411168996):ℝ):ℂ) + ((0.2302093966657:ℝ):ℂ) * I)‖ ≤ 0.0000001608 := by
  have hl := lg_15
  refine (ecis_approx ((((15167:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.072997388289431291 41.072997411039961625 2.9092998 0.00000006079 (-0.9731411168996) 0.2302093966657 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_2 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3522030790213):ℝ):ℂ) + ((0.9359236032527:ℝ):ℂ) * I)‖ ≤ 0.00000012785 := by
  have hl := lg_2
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.6356503345232 10.6356503421952 1.9307203 0.00000002784 (-0.3522030790213) 0.9359236032527 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_3 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4092689331344):ℝ):ℂ) + ((0.9124137988695:ℝ):ℂ) * I)‖ ≤ 0.00000013948 := by
  have hl := lg_3
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.857106953334868416 16.85710696100688376 1.992449 0.00000003947 (-0.4092689331344) 0.9124137988695 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_4 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7519060434439):ℝ):ℂ) + (((-0.6592702797778):ℝ):ℂ) * I)‖ ≤ 0.00000015251 := by
  have hl := lg_4
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.2713006690464 21.2713006843904 (-2.4217448) 0.0000000525 (-0.7519060434439) (-0.6592702797778) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_5 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9058027099071:ℝ):ℂ) + ((0.4236997176362:ℝ):ℂ) * I)‖ ≤ 0.00000010832 := by
  have hl := lg_5
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.695215320411622896 24.69521533575563824 0.4375259 0.00000000831 0.9058027099071 0.4236997176362 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_6 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7098038972799):ℝ):ℂ) + (((-0.7043993380043):ℝ):ℂ) * I)‖ ≤ 0.00000014088 := by
  have hl := lg_6
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.492757287858068416 27.49275730320208376 (-2.3600161) 0.00000004087 (-0.7098038972799) (-0.7043993380043) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_7 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0129147677563:ℝ):ℂ) + ((0.9999166009091:ℝ):ℂ) * I)‖ ≤ 0.00000011679 := by
  have hl := lg_7
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.858045319127515168 29.858045334471545856 1.5578812 0.00000001678 0.0129147677563 0.9999166009091 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_8 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8818502394237:ℝ):ℂ) + (((-0.4715295910422):ℝ):ℂ) * I)‖ ≤ 0.00000013234 := by
  have hl := lg_8
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.9069510035696 31.9069510265856 (-0.4910245) 0.00000003233 0.8818502394237 (-0.4715295910422) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_9 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6649979500625):ℝ):ℂ) + (((-0.7468451823464):ℝ):ℂ) * I)‖ ≤ 0.00000012924 := by
  have hl := lg_9
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.714213906669736832 33.71421392201376752 (-2.2982874) 0.00000002923 (-0.6649979500625) (-0.7468451823464) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_10 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.715577069839):ℝ):ℂ) + ((0.6985337909466:ℝ):ℂ) * I)‖ ≤ 0.00000013489 := by
  have hl := lg_10
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.330865654934822896 35.33086567795083824 2.3682462 0.00000003488 (-0.715577069839) 0.6985337909466 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_11 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6170508911534:ℝ):ℂ) + ((0.7869232476721:ℝ):ℂ) * I)‖ ≤ 0.00000013381 := by
  have hl := lg_11
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.793305053852370352 36.79330507686840104 0.9058068 0.0000000338 0.6170508911534 0.7869232476721 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_12 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9092590846927:ℝ):ℂ) + (((-0.4162306054386):ℝ):ℂ) * I)‖ ≤ 0.00000012071 := by
  have hl := lg_12
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.128407622381268416 38.12840764539728376 (-0.4292958) 0.0000000207 0.9092590846927 (-0.4162306054386) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_13 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0865662896878):ℝ):ℂ) + (((-0.9962460928351):ℝ):ℂ) * I)‖ ≤ 0.00000011417 := by
  have hl := lg_13
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.3565829289240048 39.356582951940035488 (-1.6574711) 0.00000001416 (-0.0865662896878) (-0.9962460928351) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_14 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9403941665417):ℝ):ℂ) + (((-0.3400864762882):ℝ):ℂ) * I)‖ ≤ 0.0000001336 := by
  have hl := lg_14
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.493695653650715168 40.493695676666745856 (-2.7945838) 0.00000003359 (-0.9403941665417) (-0.3400864762882) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p344_15 : ‖exp (-((((((15344:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7573063776569):ℝ):ℂ) + ((0.6530597601479:ℝ):ℂ) * I)‖ ≤ 0.00000014652 := by
  have hl := lg_15
  refine (ecis_approx ((((15344:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.552322273746491312 41.552322296762522 2.4299749 0.00000004651 (-0.7573063776569) 0.6530597601479 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_2 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2350177924436):ℝ):ℂ) + ((0.9719910684949:ℝ):ℂ) * I)‖ ≤ 0.00000012894 := by
  have hl := lg_2
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.7583373854363 10.7583373931968 1.8080332 0.00000002893 (-0.2350177924436) 0.9719910684949 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_3 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2252486851021):ℝ):ℂ) + ((0.9743013034266:ℝ):ℂ) * I)‖ ≤ 0.00000011462 := by
  have hl := lg_3
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.051561328383113444 17.051561336143628965 1.7979946 0.00000001461 (-0.2252486851021) 0.9743013034266 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_4 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8895332711601):ℝ):ℂ) + (((-0.4568703967145):ℝ):ℂ) * I)‖ ≤ 0.00000015068 := by
  have hl := lg_4
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.5166747708726 21.5166747863936 (-2.6671189) 0.00000005067 (-0.8895332711601) (-0.4568703967145) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_5 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9883707744013:ℝ):ℂ) + ((0.1520631852534:ℝ):ℂ) * I)‖ ≤ 0.00000011764 := by
  have hl := lg_5
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.980085830820437889 24.98008584634145341 0.1526554 0.00000001763 0.9883707744013 0.1520631852534 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_6 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8940747129837):ℝ):ℂ) + (((-0.4479178579753):ℝ):ℂ) * I)‖ ≤ 0.00000011491 := by
  have hl := lg_6
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.809898713819413444 27.809898729340428965 (-2.6771575) 0.0000000149 (-0.8940747129837) (-0.4479178579753) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_7 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3497846536835:ℝ):ℂ) + ((0.9368301319063:ℝ):ℂ) * I)‖ ≤ 0.00000012049 := by
  have hl := lg_7
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.202471415418284862 30.202471430939315904 1.2134551 0.00000002048 0.3497846536835 0.9368301319063 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_8 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6531301665466:ℝ):ℂ) + (((-0.7572456573311):ℝ):ℂ) * I)‖ ≤ 0.00000014371 := by
  have hl := lg_8
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.2750121563089 32.2750121795904 (-0.8590856) 0.0000000437 0.6531301665466 (-0.7572456573311) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_9 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8985260565348):ℝ):ℂ) + (((-0.4389201813693):ℝ):ℂ) * I)‖ ≤ 0.0000001364 := by
  have hl := lg_9
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.103122656766226888 34.10312267228725793 (-2.6871961) 0.00000003639 (-0.8985260565348) (-0.4389201813693) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_10 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3800887754288):ℝ):ℂ) + ((0.9249500109682:ℝ):ℂ) * I)‖ ≤ 0.00000012684 := by
  have hl := lg_10
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.738423216256737889 35.73842323953825341 1.9606886 0.00000002683 (-0.3800887754288) 0.9249500109682 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_11 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8863571472246:ℝ):ℂ) + ((0.4630021679905:ℝ):ℂ) * I)‖ ≤ 0.00000012609 := by
  have hl := lg_11
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.217732516999650693 37.217732540281181735 0.4813793 0.00000002608 0.8863571472246 0.4630021679905 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_12 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6454956227618:ℝ):ℂ) + (((-0.7637639694273):ℝ):ℂ) * I)‖ ≤ 0.00000014384 := by
  have hl := lg_12
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.568236099255713444 38.568236122537228965 (-0.8691243) 0.00000004383 0.6454956227618 (-0.7637639694273) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_13 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5147112039467):ℝ):ℂ) + (((-0.8573636197815):ℝ):ℂ) * I)‖ ≤ 0.00000014528 := by
  have hl := lg_13
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.8105789650566657 39.810578988338196742 (-2.1114671) 0.00000004527 (-0.5147112039467) (-0.8573636197815) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_14 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9927961378528):ℝ):ℂ) + ((0.1198158095722:ℝ):ℂ) * I)‖ ≤ 0.00000014942 := by
  have hl := lg_14
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.960808800854584862 40.960808824136115904 3.0214883 0.00000004941 (-0.9927961378528) 0.1198158095722 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p521_15 : ‖exp (-((((((15521:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3707845769229):ℝ):ℂ) + ((0.9287189012362:ℝ):ℂ) * I)‖ ≤ 0.00000013224 := by
  have hl := lg_15
  refine (ecis_approx ((((15521:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.031647159203551333 42.031647182485082375 1.95065 0.00000003223 (-0.3707845769229) 0.9287189012362 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_2 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0735875963887):ℝ):ℂ) + ((0.9972887574105:ℝ):ℂ) * I)‖ ≤ 0.00000011352 := by
  have hl := lg_2
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.9219201199871 10.9219201278656 1.6444505 0.00000001351 (-0.0735875963887) 0.9972887574105 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_3 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0320687276521:ℝ):ℂ) + ((0.9994856660836:ℝ):ℂ) * I)‖ ≤ 0.0000001148 := by
  have hl := lg_3
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.310833828447440148 17.310833836325955905 1.5387221 0.00000001479 0.0320687276521 0.9994856660836 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_4 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.989169730089):ℝ):ℂ) + (((-0.1467761720365):ℝ):ℂ) * I)‖ ≤ 0.00000013421 := by
  have hl := lg_4
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.8438402399742 21.8438402557312 (-2.9942843) 0.0000000342 (-0.989169730089) (-0.1467761720365) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_5 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9743072210958:ℝ):ℂ) + (((-0.2252230870063):ℝ):ℂ) * I)‖ ≤ 0.0000001507 := by
  have hl := lg_5
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.359913178032191213 25.35991319378920697 (-0.227172) 0.00000005069 0.9743072210958 (-0.2252230870063) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_6 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9991356779826):ℝ):ℂ) + (((-0.0415679731447):ℝ):ℂ) * I)‖ ≤ 0.00000013549 := by
  have hl := lg_6
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.232753948434540148 28.232753964191555905 (-3.1000127) 0.00000003548 (-0.9991356779826) (-0.0415679731447) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_7 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7288056413337:ℝ):ℂ) + ((0.6847206270883:ℝ):ℂ) * I)‖ ≤ 0.00000012544 := by
  have hl := lg_7
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.661706210472644454 30.661706226229675968 0.7542203 0.00000002543 0.7288056413337 0.6847206270883 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_8 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2191688492896:ℝ):ℂ) + (((-0.9756869454395):ℝ):ℂ) * I)‖ ≤ 0.00000014771 := by
  have hl := lg_8
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.7657603599613 32.7657603835968 (-1.3498338) 0.0000000477 0.2191688492896 (-0.9756869454395) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_9 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9979431931572):ℝ):ℂ) + ((0.0641044669848:ℝ):ℂ) * I)‖ ≤ 0.00000012959 := by
  have hl := lg_9
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.621667656894880296 34.62166767265191181 3.0774442 0.00000002958 (-0.9979431931572) 0.0641044669848 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_10 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1529155260361:ℝ):ℂ) + ((0.9882392634869:ℝ):ℂ) * I)‖ ≤ 0.00000014507 := by
  have hl := lg_10
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.281833298019291213 36.28183332165480697 1.4172785 0.00000004506 0.1529155260361 0.9882392634869 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_11 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9964299729188:ℝ):ℂ) + (((-0.0844233917174):ℝ):ℂ) * I)‖ ≤ 0.0000001419 := by
  have hl := lg_11
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.783635801196024481 37.783635824831555995 (-0.084524) 0.00000004189 0.9964299729188 (-0.0844233917174) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_12 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1149792655835:ℝ):ℂ) + (((-0.9933678918134):ℝ):ℂ) * I)‖ ≤ 0.00000014899 := by
  have hl := lg_12
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.154674068421640148 39.154674092057155905 (-1.4555622) 0.00000004898 0.1149792655835 (-0.9933678918134) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_13 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9111222283201):ℝ):ℂ) + (((-0.4121362455922):ℝ):ℂ) * I)‖ ≤ 0.00000012986 := by
  have hl := lg_13
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.4159070132335469 40.415907036869078414 (-2.7167952) 0.00000002985 (-0.9111222283201) (-0.4121362455922) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_14 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7364952387377):ℝ):ℂ) + ((0.676442727277:ℝ):ℂ) * I)‖ ≤ 0.00000011981 := by
  have hl := lg_14
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.583626330459744454 41.583626354095275968 2.3986708 0.0000000198 (-0.7364952387377) 0.676442727277 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p757_15 : ‖exp (-((((((15757:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2563520400567:ℝ):ℂ) + ((0.9665834840089:ℝ):ℂ) * I)‖ ≤ 0.00000014379 := by
  have hl := lg_15
  refine (ecis_approx ((((15757:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.670747006479631361 42.670747030115162875 1.3115501 0.00000004378 0.2563520400567 0.9665834840089 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p993_2 : ‖exp (-((((((15993:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0898073650345:ℝ):ℂ) + ((0.995959154376:ℝ):ℂ) * I)‖ ≤ 0.00000014819 := by
  have hl := lg_2
  refine (ecis_approx ((((15993:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.0855028545379 11.0855028625344 1.4808678 0.00000004818 0.0898073650345 0.995959154376 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p993_3 : ‖exp (-((((((15993:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2872424581061:ℝ):ℂ) + ((0.9578579071351:ℝ):ℂ) * I)‖ ≤ 0.00000011498 := by
  have hl := lg_3
  refine (ecis_approx ((((15993:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.570106328511766852 17.570106336508282845 1.2794496 0.00000001497 0.2872424581061 0.9578579071351 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p993_4 : ‖exp (-((((((15993:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.983869256335):ℝ):ℂ) + ((0.1788890328879:ℝ):ℂ) * I)‖ ≤ 0.00000011966 := by
  have hl := lg_4
  refine (ecis_approx ((((15993:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.1710057090758 22.1710057250688 2.9617355 0.00000001965 (-0.983869256335) 0.1788890328879 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p993_5 : ‖exp (-((((((15993:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8213633285185:ℝ):ℂ) + (((-0.5704053668795):ℝ):ℂ) * I)‖ ≤ 0.00000011253 := by
  have hl := lg_5
  refine (ecis_approx ((((15993:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.739740525243944537 25.73974054123696053 (-0.6069993) 0.00000001252 0.8213633285185 (-0.5704053668795) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p993_6 : ‖exp (-((((((15993:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9281908256527):ℝ):ℂ) + ((0.3721045431298:ℝ):ℂ) * I)‖ ≤ 0.00000015286 := by
  have hl := lg_6
  refine (ecis_approx ((((15993:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.655609183049666852 28.655609199042682845 2.7603173 0.00000005285 (-0.9281908256527) 0.3721045431298 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p993_7 : ‖exp (-((((((15993:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9568063579483:ℝ):ℂ) + ((0.290725976462:ℝ):ℂ) * I)‖ ≤ 0.00000013039 := by
  have hl := lg_7
  refine (ecis_approx ((((15993:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.120941005527004046 31.120941021520036032 0.2949855 0.00000003038 0.9568063579483 0.290725976462 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p993_8 : ‖exp (-((((((15993:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.266524868637):ℝ):ℂ) + (((-0.9638280419228):ℝ):ℂ) * I)‖ ≤ 0.00000015172 := by
  have hl := lg_8
  refine (ecis_approx ((((15993:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.2565085636137 33.2565085876032 (-1.840582) 0.00000005171 (-0.266524868637) (-0.9638280419228) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p993_9 : ‖exp (-((((((15993:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8349835405072):ℝ):ℂ) + ((0.5502749194875:ℝ):ℂ) * I)‖ ≤ 0.00000012995 := by
  have hl := lg_9
  refine (ecis_approx ((((15993:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.140212657023533704 35.14021267301656569 2.5588992 0.00000002994 (-0.8349835405072) 0.5502749194875 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v15p993_10 : ‖exp (-((((((15993:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6418649231192:ℝ):ℂ) + ((0.7668177231058:ℝ):ℂ) * I)‖ ≤ 0.00000016071 := by
  have hl := lg_10
  refine (ecis_approx ((((15993:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.825243379781844537 36.82524340377136053 0.8738685 0.0000000607 0.6418649231192 0.7668177231058 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_2 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2508045952401:ℝ):ℂ) + ((0.9680377342885:ℝ):ℂ) * I)‖ ≤ 0.00000012529 := by
  have hl := lg_2
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.2490855890887 11.2490855972032 1.317285 0.00000002528 0.2508045952401 0.9680377342885 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_3 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5232150347142:ℝ):ℂ) + ((0.8522006966959:ℝ):ℂ) * I)‖ ≤ 0.00000011517 := by
  have hl := lg_3
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.829378828576093556 17.829378836690609785 1.0201771 0.00000001516 0.5232150347142 0.8522006966959 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_4 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8741941099884):ℝ):ℂ) + ((0.4855766242008:ℝ):ℂ) * I)‖ ≤ 0.00000015056 := by
  have hl := lg_4
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.4981711781774 22.4981711944064 2.63457 0.00000005055 (-0.8741941099884) 0.4855766242008 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_5 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5513400547617:ℝ):ℂ) + (((-0.8342806146707):ℝ):ℂ) * I)‖ ≤ 0.00000015628 := by
  have hl := lg_5
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.119567872455697861 26.11956788868471409 (-0.9868267) 0.00000005627 0.5513400547617 (-0.8342806146707) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_6 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6937376965806):ℝ):ℂ) + ((0.7202277475357:ℝ):ℂ) * I)‖ ≤ 0.00000011825 := by
  have hl := lg_6
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.078464417664793556 29.078464433893809785 2.3374621 0.00000001824 (-0.6937376965806) 0.7202277475357 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_7 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9865413816114:ℝ):ℂ) + (((-0.1635117805184):ℝ):ℂ) * I)‖ ≤ 0.00000013533 := by
  have hl := lg_7
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.580175800581363638 31.580175816810396096 (-0.1642493) 0.00000003532 0.9865413816114 (-0.1635117805184) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_8 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6893083174352):ℝ):ℂ) + (((-0.7244681107493):ℝ):ℂ) * I)‖ ≤ 0.00000015573 := by
  have hl := lg_8
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.7472567672661 33.7472567916096 (-2.3313302) 0.00000005572 (-0.6893083174352) (-0.7244681107493) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_9 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.452492054898):ℝ):ℂ) + ((0.8917684342079:ℝ):ℂ) * I)‖ ≤ 0.00000013032 := by
  have hl := lg_9
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.658757657152187112 35.65875767338121957 2.0403542 0.00000003031 (-0.452492054898) 0.8917684342079 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_10 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9458937028132:ℝ):ℂ) + ((0.3244766601443:ℝ):ℂ) * I)‖ ≤ 0.00000014283 := by
  have hl := lg_10
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.368653461544397861 37.36865348588791409 0.3304584 0.00000004282 0.9458937028132 0.3244766601443 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_11 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3470894500385:ℝ):ℂ) + (((-0.9378320284955):ℝ):ℂ) * I)‖ ≤ 0.00000015087 := by
  have hl := lg_11
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.915442369588772057 38.915442393932304515 (-1.2163305) 0.00000005086 0.3470894500385 (-0.9378320284955) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_12 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8712002355549):ℝ):ℂ) + (((-0.4909278454929):ℝ):ℂ) * I)‖ ≤ 0.00000013634 := by
  have hl := lg_12
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.327550006753493556 40.327550031097009785 (-2.6284382) 0.00000003633 (-0.8712002355549) (-0.4909278454929) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_13 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7067810904855):ℝ):ℂ) + ((0.7074323219272:ℝ):ℂ) * I)‖ ≤ 0.00000014068 := by
  have hl := lg_13
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.6265631095873093 41.626563133930841758 2.355734 0.00000004067 (-0.7067810904855) 0.7074323219272 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_14 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4057146854452:ℝ):ℂ) + ((0.913999777907:ℝ):ℂ) * I)‖ ≤ 0.0000001606 := by
  have hl := lg_14
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.829261389670063638 42.829261414013596096 1.1530357 0.00000006059 0.4057146854452 0.913999777907 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p229_15 : ‖exp (-((((((16229:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9994439269538:ℝ):ℂ) + ((0.033344218018:ℝ):ℂ) * I)‖ ≤ 0.00000014924 := by
  have hl := lg_15
  refine (ecis_approx ((((16229:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.948946701031791417 43.948946725375323875 0.0333504 0.00000004923 0.9994439269538 0.033344218018 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_2 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4051053230976:ℝ):ℂ) + ((0.9142700242259:ℝ):ℂ) * I)‖ ≤ 0.00000011753 := by
  have hl := lg_2
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.4126683236395 11.412668331872 1.1537023 0.00000001752 0.4051053230976 0.9142700242259 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_3 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7242125159196:ℝ):ℂ) + ((0.6895768498039:ℝ):ℂ) * I)‖ ≤ 0.00000011535 := by
  have hl := lg_3
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.08865132864042026 18.088651336872936725 0.7609046 0.00000001534 0.7242125159196 0.6895768498039 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_4 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6717793543937):ℝ):ℂ) + ((0.7407513071138:ℝ):ℂ) * I)‖ ≤ 0.00000013504 := by
  have hl := lg_4
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.825336647279 22.825336663744 2.3074046 0.00000003503 (-0.6717793543937) 0.7407513071138 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_5 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2027273707628:ℝ):ℂ) + (((-0.9792352184963):ℝ):ℂ) * I)‖ ≤ 0.00000010907 := by
  have hl := lg_5
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.499395219667451185 26.49939523613246765 (-1.366654) 0.00000000906 0.2027273707628 (-0.9792352184963) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_6 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.337077097923):ℝ):ℂ) + ((0.9414770470137:ℝ):ℂ) * I)‖ ≤ 0.00000013286 := by
  have hl := lg_6
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.50131965227992026 29.501319668744936725 1.9146069 0.00000003285 (-0.337077097923) 0.9414770470137 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_7 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8118491363443:ℝ):ℂ) + (((-0.5838672621556):ℝ):ℂ) * I)‖ ≤ 0.00000014028 := by
  have hl := lg_7
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.03941059563572323 32.03941061210075616 (-0.6234841) 0.00000004027 0.8118491363443 (-0.5838672621556) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_8 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9493881055966):ℝ):ℂ) + (((-0.3141054357219):ℝ):ℂ) * I)‖ ≤ 0.00000015973 := by
  have hl := lg_8
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.2380049709185 34.238004995616 (-2.8220784) 0.00000005972 (-0.9493881055966) (-0.3141054357219) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_9 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0489675364292:ℝ):ℂ) + ((0.9988003706326:ℝ):ℂ) * I)‖ ≤ 0.00000013068 := by
  have hl := lg_9
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.17730265728084052 36.17730267374587345 1.5218092 0.00000003067 0.0489675364292 0.9988003706326 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_10 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9774113439711:ℝ):ℂ) + (((-0.2113458413989):ℝ):ℂ) * I)‖ ≤ 0.00000012494 := by
  have hl := lg_10
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.912063543306951185 37.91206356800446765 (-0.2129517) 0.00000002493 0.9774113439711 (-0.2113458413989) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_11 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2098655772224):ℝ):ℂ) + (((-0.9777302488397):ℝ):ℂ) * I)‖ ≤ 0.00000013542 := by
  have hl := lg_11
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.481345653785145845 39.481345678482678775 (-1.7822338) 0.00000003541 (-0.2098655772224) (-0.9777302488397) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_12 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9973159689996):ℝ):ℂ) + ((0.0732178765923:ℝ):ℂ) * I)‖ ≤ 0.00000015037 := by
  have hl := lg_12
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.91398797591942026 40.913988000616936725 3.0683092 0.00000005036 (-0.9973159689996) 0.0732178765923 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_13 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1786455392424):ℝ):ℂ) + ((0.9839134978788:ℝ):ℂ) * I)‖ ≤ 0.00000013222 := by
  have hl := lg_13
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.2318911577641905 42.23189118246172343 1.750406 0.00000003221 (-0.1786455392424) 0.9839134978788 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_14 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8626967426009:ℝ):ℂ) + ((0.5057215936716:ℝ):ℂ) * I)‖ ≤ 0.000000131 := by
  have hl := lg_14
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.45207891927522323 43.45207894397275616 0.5302182 0.00000003099 0.8626967426009 0.5057215936716 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p465_15 : ‖exp (-((((((16465:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8220756364136:ℝ):ℂ) + (((-0.5693782995647):ℝ):ℂ) * I)‖ ≤ 0.00000012276 := by
  have hl := lg_15
  refine (ecis_approx ((((16465:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.588046548307871445 44.588046573005404375 (-0.6057494) 0.00000002275 0.8220756364136 (-0.5693782995647) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p701_2 : ‖exp (-((((((16701:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5485898679505:ℝ):ℂ) + ((0.8360915959284:ℝ):ℂ) * I)‖ ≤ 0.0000001522 := by
  have hl := lg_2
  refine (ecis_approx ((((16701:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.5762510581903 11.5762510665408 0.9901196 0.00000005219 0.5485898679505 0.8360915959284 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p701_3 : ‖exp (-((((((16701:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.876798922986:ℝ):ℂ) + ((0.4808572019327:ℝ):ℂ) * I)‖ ≤ 0.00000011553 := by
  have hl := lg_3
  refine (ecis_approx ((((16701:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.347923828704746964 18.347923837055263665 0.5016321 0.00000001552 0.876798922986 0.4808572019327 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p701_4 : ‖exp (-((((((16701:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3980982218299):ℝ):ℂ) + ((0.9173427962178:ℝ):ℂ) * I)‖ ≤ 0.00000011235 := by
  have hl := lg_4
  refine (ecis_approx ((((16701:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.1525021163806 23.1525021330816 1.9802391 0.00000001234 (-0.3980982218299) 0.9173427962178 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p701_5 : ‖exp (-((((((16701:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1747826079897):ℝ):ℂ) + (((-0.9846070484938):ℝ):ℂ) * I)‖ ≤ 0.00000015488 := by
  have hl := lg_5
  refine (ecis_approx ((((16701:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.879222566879204509 26.87922258358022121 (-1.7464813) 0.00000005487 (-0.1747826079897) (-0.9846070484938) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p701_6 : ‖exp (-((((((16701:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0789624396902:ℝ):ℂ) + ((0.9968775918427:ℝ):ℂ) * I)‖ ≤ 0.00000014902 := by
  have hl := lg_6
  refine (ecis_approx ((((16701:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.924174886895046964 29.924174903596063665 1.4917516 0.00000004901 0.0789624396902 0.9968775918427 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p701_7 : ‖exp (-((((((16701:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4689286699202:ℝ):ℂ) + (((-0.8832360400974):ℝ):ℂ) * I)‖ ≤ 0.00000014522 := by
  have hl := lg_7
  refine (ecis_approx ((((16701:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.498645390690082822 32.498645407391116224 (-1.0827189) 0.00000004521 0.4689286699202 (-0.8832360400974) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p701_8 : ‖exp (-((((((16701:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.985375253296):ℝ):ℂ) + ((0.1703983856403:ℝ):ℂ) * I)‖ ≤ 0.00000015656 := by
  have hl := lg_8
  refine (ecis_approx ((((16701:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.7287531745709 34.7287531996224 2.9703587 0.00000005655 (-0.985375253296) 0.1703983856403 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p701_9 : ‖exp (-((((((16701:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5375527026988:ℝ):ℂ) + ((0.8432301535294:ℝ):ℂ) * I)‖ ≤ 0.00000013105 := by
  have hl := lg_9
  refine (ecis_approx ((((16701:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.695847657409493928 36.69584767411052733 1.0032642 0.00000003104 0.5375527026988 0.8432301535294 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p701_10 : ‖exp (-((((((16701:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7273376420727:ℝ):ℂ) + (((-0.6862797931049):ℝ):ℂ) * I)‖ ≤ 0.00000011802 := by
  have hl := lg_10
  refine (ecis_approx ((((16701:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.455473625069504509 38.45547365012102121 (-0.7563618) 0.00000001801 0.7273376420727 (-0.6862797931049) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p937_2 : ‖exp (-((((((16937:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6774273117442:ℝ):ℂ) + ((0.7355897207704:ℝ):ℂ) * I)‖ ≤ 0.00000012163 := by
  have hl := lg_2
  refine (ecis_approx ((((16937:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.7398337927411 11.7398338012096 0.8265368 0.00000002162 0.6774273117442 0.7355897207704 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p937_3 : ‖exp (-((((((16937:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9707743881913:ℝ):ℂ) + ((0.2399939316562:ℝ):ℂ) * I)‖ ≤ 0.00000011571 := by
  have hl := lg_3
  refine (ecis_approx ((((16937:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.607196328769073668 18.607196337237590605 0.2423596 0.0000000157 0.9707743881913 0.2399939316562 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p937_4 : ‖exp (-((((((16937:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0821844746061):ℝ):ℂ) + ((0.9966171341761:ℝ):ℂ) * I)‖ ≤ 0.00000014325 := by
  have hl := lg_4
  refine (ecis_approx ((((16937:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.4796675854822 23.4796676024192 1.6530736 0.00000004324 (-0.0821844746061) 0.9966171341761 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p937_5 : ‖exp (-((((((16937:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5273786972283):ℝ):ℂ) + (((-0.8496303370892):ℝ):ℂ) * I)‖ ≤ 0.00000011464 := by
  have hl := lg_5
  refine (ecis_approx ((((16937:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.259049914090957833 27.25904993102797477 (-2.1263087) 0.00000001463 (-0.5273786972283) (-0.8496303370892) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p937_6 : ‖exp (-((((((16937:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.481092014929:ℝ):ℂ) + ((0.8766701050974:ℝ):ℂ) * I)‖ ≤ 0.0000001144 := by
  have hl := lg_6
  refine (ecis_approx ((((16937:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.347030121510173668 30.347030138447190605 1.0688964 0.00000001439 0.481092014929 0.8766701050974 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p937_7 : ‖exp (-((((((16937:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0288386279448:ℝ):ℂ) + (((-0.9995840802744):ℝ):ℂ) * I)‖ ≤ 0.00000015017 := by
  have hl := lg_7
  refine (ecis_approx ((((16937:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.957880185744442414 32.957880202681476288 (-1.5419537) 0.00000005016 0.0288386279448 (-0.9995840802744) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p937_8 : ‖exp (-((((((16937:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7887753886025):ℝ):ℂ) + ((0.6146815324132:ℝ):ℂ) * I)‖ ≤ 0.00000016057 := by
  have hl := lg_8
  refine (ecis_approx ((((16937:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.2195013782233 35.2195014036288 2.4796105 0.00000006056 (-0.7887753886025) 0.6146815324132 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p937_9 : ‖exp (-((((((16937:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8848058255364:ℝ):ℂ) + ((0.4659599243463:ℝ):ℂ) * I)‖ ≤ 0.00000013141 := by
  have hl := lg_9
  refine (ecis_approx ((((16937:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.214392657538147336 37.21439267447518121 0.4847192 0.0000000314 0.8848058255364 0.4659599243463 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v16p937_10 : ‖exp (-((((((16937:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2677186092858:ℝ):ℂ) + (((-0.9634971438681):ℝ):ℂ) * I)‖ ≤ 0.00000013626 := by
  have hl := lg_10
  refine (ecis_approx ((((16937:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.998883706832057833 38.99888373223757477 (-1.2997719) 0.00000003625 0.2677186092858 (-0.9634971438681) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p252_2 : ‖exp (-((((((17252:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8206804221393:ℝ):ℂ) + ((0.5713874733639:ℝ):ℂ) * I)‖ ≤ 0.00000014882 := by
  have hl := lg_2
  refine (ecis_approx ((((17252:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.9581751545356 11.9581751631616 0.6081955 0.00000004881 0.8206804221393 0.5713874733639 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p252_3 : ‖exp (-((((((17252:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9946276300811:ℝ):ℂ) + (((-0.1035175225712):ℝ):ℂ) * I)‖ ≤ 0.00000012194 := by
  have hl := lg_3
  refine (ecis_approx ((((17252:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.953259199617645328 18.95325920824366258 (-0.1037033) 0.00000002193 0.9946276300811 (-0.1035175225712) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p252_4 : ‖exp (-((((((17252:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3470328043509:ℝ):ℂ) + ((0.9378529909876:ℝ):ℂ) * I)‖ ≤ 0.00000011966 := by
  have hl := lg_4
  refine (ecis_approx ((((17252:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.9163503090712 23.9163503263232 1.2163909 0.00000001965 0.3470328043509 0.9378529909876 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p252_5 : ‖exp (-((((((17252:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8735677676691):ℝ):ℂ) + (((-0.4867025325584):ℝ):ℂ) * I)‖ ≤ 0.00000014489 := by
  have hl := lg_5
  refine (ecis_approx ((((17252:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.766022856343933668 27.76602287359595092 (-2.6332816) 0.00000004488 (-0.8735677676691) (-0.4867025325584) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p252_6 : ‖exp (-((((((17252:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8754200389972:ℝ):ℂ) + ((0.4833629643675:ℝ):ℂ) * I)‖ ≤ 0.00000013552 := by
  have hl := lg_6
  refine (ecis_approx ((((17252:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.911434354153245328 30.91143437140526258 0.5044922 0.00000003551 0.8754200389972 0.4833629643675 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p252_7 : ‖exp (-((((((17252:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5514647288469):ℝ):ℂ) + (((-0.8341982095576):ℝ):ℂ) * I)‖ ≤ 0.00000015338 := by
  have hl := lg_7
  refine (ecis_approx ((((17252:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.570841882533100344 33.570841899785134848 (-2.1549154) 0.00000005337 (-0.5514647288469) (-0.8341982095576) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p252_8 : ‖exp (-((((((17252:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2510744225364):ℝ):ℂ) + ((0.9679677858001:ℝ):ℂ) * I)‖ ≤ 0.00000014642 := by
  have hl := lg_8
  refine (ecis_approx ((((17252:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.8745254636068 35.8745254894848 1.8245864 0.00000004641 (-0.2510744225364) 0.9679677858001 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p252_9 : ‖exp (-((((((17252:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9785682450415:ℝ):ℂ) + (((-0.2059227762936):ℝ):ℂ) * I)‖ ≤ 0.00000014386 := by
  have hl := lg_9
  refine (ecis_approx ((((17252:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.906518399235290656 37.90651841648732516 (-0.2074066) 0.00000004385 0.9785682450415 (-0.2059227762936) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p252_10 : ‖exp (-((((((17252:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4388243238285):ℝ):ℂ) + (((-0.8985728756268):ℝ):ℂ) * I)‖ ≤ 0.00000013221 := by
  have hl := lg_10
  refine (ecis_approx ((((17252:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.724198010879533668 39.72419803675755092 (-2.0250862) 0.0000000322 (-0.4388243238285) (-0.8985728756268) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p673_2 : ‖exp (-((((((17673:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.950367771407:ℝ):ℂ) + ((0.3111287499908:ℝ):ℂ) * I)‖ ≤ 0.00000011193 := by
  have hl := lg_2
  refine (ecis_approx ((((17673:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.2499901174419 12.2499901262784 0.3163805 0.00000001192 0.950367771407 0.3111287499908 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p673_3 : ‖exp (-((((((17673:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.843935247548:ℝ):ℂ) + (((-0.5364450558502):ℝ):ℂ) * I)‖ ≤ 0.00000014852 := by
  have hl := lg_3
  refine (ecis_approx ((((17673:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.415774973037482372 19.415774981874000045 (-0.5662191) 0.00000004851 0.843935247548 (-0.5364450558502) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p673_4 : ‖exp (-((((((17673:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8063978018584:ℝ):ℂ) + ((0.5913734734988:ℝ):ℂ) * I)‖ ≤ 0.00000012385 := by
  have hl := lg_4
  refine (ecis_approx ((((17673:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.4999802348838 24.4999802525568 0.632761 0.00000002384 0.8063978018584 0.5913734734988 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p673_5 : ‖exp (-((((((17673:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9857092953564):ℝ):ℂ) + ((0.1684552898613:ℝ):ℂ) * I)‖ ≤ 0.00000011865 := by
  have hl := lg_5
  refine (ecis_approx ((((17673:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.443596217259815657 28.44359623493283333 2.9723303 0.00000001864 (-0.9857092953564) 0.1684552898613 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p673_6 : ‖exp (-((((((17673:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9689523400894:ℝ):ℂ) + (((-0.2472475735679):ℝ):ℂ) * I)‖ ≤ 0.00000014543 := by
  have hl := lg_6
  refine (ecis_approx ((((17673:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.665765090479382372 31.665765108152400045 (-0.2498386) 0.00000004542 0.9689523400894 (-0.2472475735679) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p673_7 : ‖exp (-((((((17673:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9860131179646):ℝ):ℂ) + (((-0.1666677258303):ℝ):ℂ) * I)‖ ≤ 0.00000013686 := by
  have hl := lg_7
  refine (ecis_approx ((((17673:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.390070055066513006 34.390070072739548352 (-2.9741435) 0.00000003685 (-0.9860131179646) (-0.1666677258303) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p673_8 : ‖exp (-((((((17673:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5823811922323:ℝ):ℂ) + ((0.8129158301658:ℝ):ℂ) * I)‖ ≤ 0.00000013577 := by
  have hl := lg_8
  refine (ecis_approx ((((17673:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.7499703523257 36.7499703788352 0.9491415 0.00000003576 0.5823811922323 0.8129158301658 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p673_9 : ‖exp (-((((((17673:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4244534946528:ℝ):ℂ) + (((-0.9054497395643):ℝ):ℂ) * I)‖ ≤ 0.00000012069 := by
  have hl := lg_9
  refine (ecis_approx ((((17673:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.831549946074964744 38.83154996374800009 (-1.1324381) 0.00000002068 0.4244534946528 (-0.9054497395643) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v17p673_10 : ‖exp (-((((((17673:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9891976290245):ℝ):ℂ) + (((-0.1465880292999):ℝ):ℂ) * I)‖ ≤ 0.00000011815 := by
  have hl := lg_10
  refine (ecis_approx ((((17673:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.693586334701715657 40.69358636121123333 (-2.9944745) 0.00000001814 (-0.9891976290245) (-0.1465880292999) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p094_2 : ‖exp (-((((((18094:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9996982832783:ℝ):ℂ) + ((0.0245630293429:ℝ):ℂ) * I)‖ ≤ 0.00000013403 := by
  have hl := lg_2
  refine (ecis_approx ((((18094:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.5418050803482 12.5418050893952 0.0245655 0.00000003402 0.9996982832783 0.0245630293429 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p094_3 : ‖exp (-((((((18094:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5159030873185:ℝ):ℂ) + (((-0.8566469544073):ℝ):ℂ) * I)‖ ≤ 0.00000013398 := by
  have hl := lg_3
  refine (ecis_approx ((((18094:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.878290746457319416 19.87829075550433751 (-1.0287348) 0.00000003397 0.5159030873185 (-0.8566469544073) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p094_4 : ‖exp (-((((((18094:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9987933102679:ℝ):ℂ) + ((0.0491113364118:ℝ):ℂ) * I)‖ ≤ 0.00000015009 := by
  have hl := lg_4
  refine (ecis_approx ((((18094:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.0836101606964 25.0836101787904 0.0491311 0.00000005008 0.9987933102679 0.0491113364118 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p094_5 : ‖exp (-((((((18094:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6623570742178):ℝ):ℂ) + ((0.749188298237:ℝ):ℂ) * I)‖ ≤ 0.00000015774 := by
  have hl := lg_5
  refine (ecis_approx ((((18094:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.121169578175697646 29.12116959626971574 2.2947569 0.00000005773 (-0.6623570742178) 0.749188298237 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p094_6 : ‖exp (-((((((18094:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5367892750079:ℝ):ℂ) + (((-0.8437163470246):ℝ):ℂ) * I)‖ ≤ 0.00000010911 := by
  have hl := lg_6
  refine (ecis_approx ((((18094:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.420095826805519416 32.42009584489953751 (-1.0041693) 0.0000000091 0.5367892750079 (-0.8437163470246) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p094_7 : ‖exp (-((((((18094:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.795005880245):ℝ):ℂ) + ((0.6066017229851:ℝ):ℂ) * I)‖ ≤ 0.00000011549 := by
  have hl := lg_7
  refine (ecis_approx ((((18094:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.209298227599925668 35.209298245693961856 2.4898136 0.00000001548 (-0.795005880245) 0.6066017229851 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p094_8 : ‖exp (-((((((18094:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9972856344272:ℝ):ℂ) + ((0.073629908088:ℝ):ℂ) * I)‖ ≤ 0.00000012512 := by
  have hl := lg_8
  refine (ecis_approx ((((18094:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.6254152410446 37.6254152681856 0.0736966 0.00000002511 0.9972856344272 0.073629908088 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p094_9 : ‖exp (-((((((18094:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4676880973798):ℝ):ℂ) + (((-0.8838935702697):ℝ):ℂ) * I)‖ ≤ 0.00000015018 := by
  have hl := lg_9
  refine (ecis_approx ((((18094:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.756581492914638832 39.75658151100867502 (-2.0574697) 0.00000005017 (-0.4676880973798) (-0.8838935702697) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p094_10 : ‖exp (-((((((18094:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6805596374348):ℝ):ℂ) + ((0.7326926912928:ℝ):ℂ) * I)‖ ≤ 0.00000013542 := by
  have hl := lg_10
  refine (ecis_approx ((((18094:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.662974658523897646 41.66297468566491574 2.3193225 0.00000003541 (-0.6805596374348) 0.7326926912928 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p515_2 : ‖exp (-((((((18515:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9645009210837:ℝ):ℂ) + (((-0.2640794827863):ℝ):ℂ) * I)‖ ≤ 0.00000013817 := by
  have hl := lg_2
  refine (ecis_approx ((((18515:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.8336200432545 12.833620052512 (-0.2672494) 0.00000003816 0.9645009210837 (-0.2640794827863) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p515_3 : ‖exp (-((((((18515:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.079461865433:ℝ):ℂ) + (((-0.9968379065534):ℝ):ℂ) * I)‖ ≤ 0.00000010761 := by
  have hl := lg_3
  refine (ecis_approx ((((18515:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.34080651987715646 20.340806529134674975 (-1.4912506) 0.0000000076 0.079461865433 (-0.9968379065534) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p515_4 : ‖exp (-((((((18515:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8605240026017:ℝ):ℂ) + (((-0.5094098948258):ℝ):ℂ) * I)‖ ≤ 0.00000014222 := by
  have hl := lg_4
  refine (ecis_approx ((((18515:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.667240086509 25.667240105024 (-0.5344989) 0.00000004221 0.8605240026017 (-0.5094098948258) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p515_5 : ‖exp (-((((((18515:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0463706391339):ℝ):ℂ) + ((0.9989243033514:ℝ):ℂ) * I)‖ ≤ 0.00000012172 := by
  have hl := lg_5
  refine (ecis_approx ((((18515:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.798742939091579635 29.79874295760659815 1.6171836 0.00000002171 (-0.0463706391339) 0.9989243033514 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p515_6 : ‖exp (-((((((18515:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1866033963833):ℝ):ℂ) + (((-0.9824353273663):ℝ):ℂ) * I)‖ ≤ 0.00000014576 := by
  have hl := lg_6
  refine (ecis_approx ((((18515:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.17442656313165646 33.174426581646674975 (-1.7585) 0.00000004575 (-0.1866033963833) (-0.9824353273663) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p515_7 : ‖exp (-((((((18515:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0996235413882):ℝ):ℂ) + ((0.9950252006863:ℝ):ℂ) * I)‖ ≤ 0.00000014296 := by
  have hl := lg_7
  refine (ecis_approx ((((18515:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.02852640013333833 36.02852641864837536 1.6705854 0.00000004295 (-0.0996235413882) 0.9950252006863 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p515_8 : ‖exp (-((((((18515:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6954514915722:ℝ):ℂ) + (((-0.7185730463008):ℝ):ℂ) * I)‖ ≤ 0.00000011447 := by
  have hl := lg_8
  refine (ecis_approx ((((18515:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.5008601297635 38.500860157536 (-0.8017483) 0.00000001446 0.6954514915722 (-0.7185730463008) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p515_9 : ‖exp (-((((((18515:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9873716237208):ℝ):ℂ) + (((-0.1584211989936):ℝ):ℂ) * I)‖ ≤ 0.00000011521 := by
  have hl := lg_9
  refine (ecis_approx ((((18515:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.68161303975431292 40.68161305826934995 (-2.9825012) 0.0000000152 (-0.9873716237208) (-0.1584211989936) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p515_10 : ‖exp (-((((((18515:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2190708892158:ℝ):ℂ) + ((0.9757089450744:ℝ):ℂ) * I)‖ ≤ 0.00000015988 := by
  have hl := lg_10
  refine (ecis_approx ((((18515:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.632362982346079635 42.63236301011859815 1.3499342 0.00000005987 0.2190708892158 0.9757089450744 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_2 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8843993588303:ℝ):ℂ) + (((-0.4667309440144):ℝ):ℂ) * I)‖ ≤ 0.00000010933 := by
  have hl := lg_2
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.051961405049 13.051961414464 (-0.4855908) 0.00000000932 0.8843993588303 (-0.4667309440144) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_3 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2633731786375):ℝ):ℂ) + (((-0.9646940285775):ℝ):ℂ) * I)‖ ≤ 0.00000013083 := by
  have hl := lg_3
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.68686939072572812 20.68686940014074695 (-1.8373135) 0.00000003082 (-0.2633731786375) (-0.9646940285775) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_4 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5643244517988:ℝ):ℂ) + (((-0.8255530952652):ℝ):ℂ) * I)‖ ≤ 0.00000011864 := by
  have hl := lg_4
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.103922810098 26.103922828928 (-0.9711816) 0.00000001863 0.5643244517988 (-0.8255530952652) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_5 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.444472872739:ℝ):ℂ) + ((0.8957923115316:ℝ):ℂ) * I)‖ ≤ 0.00000015457 := by
  have hl := lg_5
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.30571588134455547 30.3057159001745743 1.1102106 0.00000005456 0.444472872739 0.8957923115316 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_6 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6831796249607):ℝ):ℂ) + (((-0.7302503680365):ℝ):ℂ) * I)‖ ≤ 0.00000014014 := by
  have hl := lg_6
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.73883079577472812 33.73883081460474695 (-2.3229043) 0.00000004013 (-0.6831796249607) (-0.7302503680365) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_7 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4909436779611:ℝ):ℂ) + ((0.8711913137021:ℝ):ℂ) * I)‖ ≤ 0.00000014617 := by
  have hl := lg_7
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.64148809692199626 36.64148811575203392 1.0576237 0.00000004616 0.4909436779611 0.8711913137021 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_8 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1137770078559:ℝ):ℂ) + (((-0.9935063122513):ℝ):ℂ) * I)‖ ≤ 0.00000012795 := by
  have hl := lg_8
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.155884215147 39.155884243392 (-1.4567724) 0.00000002794 0.1137770078559 (-0.9935063122513) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_9 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8612691846947):ℝ):ℂ) + ((0.5081489854501:ℝ):ℂ) * I)‖ ≤ 0.00000015004 := by
  have hl := lg_9
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.37373878145145624 41.3737388002814939 2.6085584 0.00000005003 (-0.8612691846947) 0.5081489854501 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_10 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8111855148698:ℝ):ℂ) + ((0.5847889024814:ℝ):ℂ) * I)‖ ≤ 0.00000016388 := by
  have hl := lg_10
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.35767728639355547 43.3576773146385743 0.6246198 0.00000006387 0.8111855148698 0.5847889024814 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_11 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3900864941881:ℝ):ℂ) + (((-0.9207782181677):ℝ):ℂ) * I)‖ ≤ 0.00000015011 := by
  have hl := lg_11
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.15236797210897639 45.15236800035401405 (-1.1700708) 0.0000000501 0.3900864941881 (-0.9207782181677) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_12 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9450340658631):ℝ):ℂ) + (((-0.3269718858975):ℝ):ℂ) * I)‖ ≤ 0.00000014945 := by
  have hl := lg_12
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.79079220082372812 46.79079222906874695 (-2.8084951) 0.00000004944 (-0.9450340658631) (-0.3269718858975) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_13 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3863672935513):ℝ):ℂ) + ((0.9223450083732:ℝ):ℂ) * I)‖ ≤ 0.00000015714 := by
  have hl := lg_13
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.297996386316411 48.29799641456144866 1.9674861 0.00000005713 (-0.3863672935513) 0.9223450083732 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_14 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8408022182719:ℝ):ℂ) + ((0.541342432984:ℝ):ℂ) * I)‖ ≤ 0.00000015548 := by
  have hl := lg_14
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.69344950197099626 49.69344953021603392 0.5720329 0.00000005547 0.8408022182719 0.541342432984 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v18p83_15 : ‖exp (-((((((18830:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7471033269403:ℝ):ℂ) + (((-0.664707919973):ℝ):ℂ) * I)‖ ≤ 0.00000014289 := by
  have hl := lg_15
  refine (ecis_approx ((((18830:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.99258527207028359 50.99258530031532125 (-0.7271028) 0.00000004288 0.7471033269403 (-0.664707919973) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_2 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7965837131531:ℝ):ℂ) + (((-0.6045282358494):ℝ):ℂ) * I)‖ ≤ 0.00000013479 := by
  have hl := lg_2
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.2155441395998 13.2155441491328 (-0.6491735) 0.00000003478 0.7965837131531 (-0.6045282358494) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_3 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5018961714589):ℝ):ℂ) + (((-0.8649278773797):ℝ):ℂ) * I)‖ ≤ 0.00000013076 := by
  have hl := lg_3
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.946141890790054824 20.94614190032307389 (-2.096586) 0.00000003075 (-0.5018961714589) (-0.8649278773797) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_4 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2690911278102:ℝ):ℂ) + (((-0.9631147205467):ℝ):ℂ) * I)‖ ≤ 0.00000014953 := by
  have hl := lg_4
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.4310882791996 26.4310882982656 (-1.2983471) 0.00000004952 0.2690911278102 (-0.9631147205467) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_5 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7449187364799:ℝ):ℂ) + ((0.6671552113573:ℝ):ℂ) * I)‖ ≤ 0.00000011174 := by
  have hl := lg_5
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.685543228556308794 30.68554324762232786 0.7303833 0.00000001173 0.7449187364799 0.6671552113573 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_6 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9226756396826):ℝ):ℂ) + (((-0.3855770529857):ℝ):ℂ) * I)‖ ≤ 0.00000011357 := by
  have hl := lg_6
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.161686030389854824 34.16168604945587389 (-2.7457595) 0.00000001356 (-0.9226756396826) (-0.3855770529857) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_7 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8262442388669:ℝ):ℂ) + ((0.563312042956:ℝ):ℂ) * I)‖ ≤ 0.00000015112 := by
  have hl := lg_7
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.100722891976355852 37.100722911042393984 0.5983889 0.00000005111 0.8262442388669 0.563312042956 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_8 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3678764331651):ℝ):ℂ) + (((-0.9298746850619):ℝ):ℂ) * I)‖ ≤ 0.00000012429 := by
  have hl := lg_8
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.6466324187994 39.6466324473984 (-1.9475206) 0.00000002428 (-0.3678764331651) (-0.9298746850619) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_9 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4962005467367):ℝ):ℂ) + ((0.8682079344328:ℝ):ℂ) * I)‖ ≤ 0.0000001504 := by
  have hl := lg_9
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.892283781580109648 41.89228380064614778 2.0900134 0.00000005039 (-0.4962005467367) 0.8682079344328 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_10 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.996704296062:ℝ):ℂ) + ((0.0811205658971:ℝ):ℂ) * I)‖ ≤ 0.00000014651 := by
  have hl := lg_10
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.901087368156108794 43.90108739675512786 0.0812098 0.0000000465 0.996704296062 0.0811205658971 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_11 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1644276871468):ℝ):ℂ) + (((-0.9863891400958):ℝ):ℂ) * I)‖ ≤ 0.00000013466 := by
  have hl := lg_11
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.718271256305350178 45.71827128490438831 (-1.7359741) 0.00000003465 (-0.1644276871468) (-0.9863891400958) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_12 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9680806009036):ℝ):ℂ) + ((0.2506390829278:ℝ):ℂ) * I)‖ ≤ 0.00000014117 := by
  have hl := lg_12
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.377230169989654824 47.37723019858867389 2.8882523 0.00000004116 (-0.9680806009036) 0.2506390829278 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_13 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.207127948509:ℝ):ℂ) + ((0.9783138621866:ℝ):ℂ) * I)‖ ≤ 0.00000012296 := by
  have hl := lg_13
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.9033244344932922 48.903324463092330332 1.362158 0.00000002295 0.207127948509 0.9783138621866 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_14 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9987107393289:ℝ):ℂ) + (((-0.0507627732611):ℝ):ℂ) * I)‖ ≤ 0.00000012588 := by
  have hl := lg_14
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.316267031576155852 50.316267060175193984 (-0.0507846) 0.00000002587 0.9987107393289 (-0.0507627732611) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p066_15 : ‖exp (-((((((19066:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.203169278957:ℝ):ℂ) + (((-0.9791436279158):ℝ):ℂ) * I)‖ ≤ 0.00000013811 := by
  have hl := lg_15
  refine (ecis_approx ((((19066:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.631685119346363618 51.63168514794540175 (-1.3662027) 0.0000000381 0.203169278957 (-0.9791436279158) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_2 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7166141984904:ℝ):ℂ) + (((-0.6974697774971):ℝ):ℂ) * I)‖ ≤ 0.00000012386 := by
  have hl := lg_2
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.3382311905129 13.3382312001344 (-0.7718606) 0.00000002385 0.7166141984904 (-0.6974697774971) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_3 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6595680727968):ℝ):ℂ) + (((-0.7516448345656):ℝ):ℂ) * I)‖ ≤ 0.00000015394 := by
  have hl := lg_3
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.140596265838299852 21.140596275459819095 (-2.2910403) 0.00000005393 (-0.6595680727968) (-0.7516448345656) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_4 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0270718189561:ℝ):ℂ) + (((-0.9996334911447):ℝ):ℂ) * I)‖ ≤ 0.00000014771 := by
  have hl := lg_4
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.6764623810258 26.6764624002688 (-1.5437212) 0.0000000477 0.0270718189561 (-0.9996334911447) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_5 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9023898079278:ℝ):ℂ) + ((0.4309206824324:ℝ):ℂ) * I)‖ ≤ 0.00000012233 := by
  have hl := lg_5
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.970413738965123787 30.97041375820814303 0.4455128 0.00000002232 0.9023898079278 0.4309206824324 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_6 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9969054011275):ℝ):ℂ) + (((-0.0786105634603):ℝ):ℂ) * I)‖ ≤ 0.00000013971 := by
  have hl := lg_6
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.478827456351199852 34.478827475594219095 (-3.0629009) 0.0000000397 (-0.9969054011275) (-0.0786105634603) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_7 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9679244040813:ℝ):ℂ) + ((0.2512416127633:ℝ):ℂ) * I)‖ ≤ 0.00000015483 := by
  have hl := lg_7
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.445148988267125546 37.445149007510164032 0.2539628 0.00000005482 0.9679244040813 0.2512416127633 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_8 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6778140252787):ℝ):ℂ) + (((-0.7352333963546):ℝ):ℂ) * I)‖ ≤ 0.00000015734 := by
  have hl := lg_8
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.0146935715387 40.0146936004032 (-2.3155817) 0.00000005733 (-0.6778140252787) (-0.7352333963546) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_9 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1299398084182):ℝ):ℂ) + ((0.9915218838673:ℝ):ℂ) * I)‖ ≤ 0.0000001186 := by
  have hl := lg_9
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.281192531676599704 42.28119255091963819 1.7011046 0.00000001859 (-0.1299398084182) 0.9915218838673 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_10 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9472195014292:ℝ):ℂ) + (((-0.3205857390969):ℝ):ℂ) * I)‖ ≤ 0.00000012079 := by
  have hl := lg_10
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.308644929478023787 44.30864495834254303 (-0.3263478) 0.00000002078 0.9472195014292 (-0.3205857390969) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_11 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5560329850267):ℝ):ℂ) + (((-0.8311602249586):ℝ):ℂ) * I)‖ ≤ 0.00000013082 := by
  have hl := lg_11
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.142698719452630519 46.142698748317169005 (-2.1604016) 0.00000003081 (-0.5560329850267) (-0.8311602249586) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_12 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7692250529494):ℝ):ℂ) + ((0.6389779478793:ℝ):ℂ) * I)‖ ≤ 0.00000011831 := by
  have hl := lg_12
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.817058646864099852 47.817058675728619095 2.4484238 0.0000000183 (-0.7692250529494) 0.6389779478793 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_13 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6151958198542:ℝ):ℂ) + ((0.7883743420698:ℝ):ℂ) * I)‖ ≤ 0.00000014207 := by
  have hl := lg_13
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.3573204706259531 49.357320499490491586 0.908162 0.00000004206 0.6151958198542 0.7883743420698 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_14 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8688618522875:ℝ):ℂ) + (((-0.4950546249046):ℝ):ℂ) * I)‖ ≤ 0.00000015022 := by
  have hl := lg_14
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.783380178780025546 50.783380207644564032 (-0.5178977) 0.00000005021 0.8688618522875 (-0.4950546249046) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p243_15 : ‖exp (-((((((19243:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2712882977159):ℝ):ℂ) + (((-0.9624981348143):ℝ):ℂ) * I)‖ ≤ 0.00000015265 := by
  have hl := lg_15
  refine (ecis_approx ((((19243:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.111010004803423639 52.111010033667962125 (-1.8455276) 0.00000005264 (-0.2712882977159) (-0.9624981348143) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_2 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5934616892673:ℝ):ℂ) + (((-0.8048622387539):ℝ):ℂ) * I)‖ ≤ 0.00000012046 := by
  have hl := lg_2
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.5018139250637 13.5018139348032 (-0.9354433) 0.00000002045 0.5934616892673 (-0.8048622387539) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_3 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.830227938077):ℝ):ℂ) + (((-0.5574240493321):ℝ):ℂ) * I)‖ ≤ 0.00000015412 := by
  have hl := lg_3
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.399868765902626556 21.399868775642146035 (-2.5503128) 0.00000005411 (-0.830227938077) (-0.5574240493321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_4 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.295606446744):ℝ):ℂ) + (((-0.9553098076759):ℝ):ℂ) * I)‖ ≤ 0.0000001409 := by
  have hl := lg_4
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.0036278501274 27.0036278696064 (-1.8708866) 0.00000004089 (-0.295606446744) (-0.9553098076759) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_5 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9978434896489:ℝ):ℂ) + ((0.0656381761266:ℝ):ℂ) * I)‖ ≤ 0.00000014974 := by
  have hl := lg_5
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.350241086176877111 31.35024110565589659 0.0656854 0.00000004973 0.9978434896489 0.0656381761266 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_6 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9413580066993):ℝ):ℂ) + ((0.3374093997517:ℝ):ℂ) * I)‖ ≤ 0.00000015213 := by
  have hl := lg_6
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.901682690966326556 34.901682710445346035 2.7974291 0.00000005212 (-0.9413580066993) 0.3374093997517 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_7 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9790055984186:ℝ):ℂ) + (((-0.2038333590584):ℝ):ℂ) * I)‖ ≤ 0.00000015974 := by
  have hl := lg_7
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.904383783321485138 37.904383802800524096 (-0.2052719) 0.00000005973 0.9790055984186 (-0.2038333590584) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_8 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9443238916875):ℝ):ℂ) + (((-0.3290173056224):ℝ):ℂ) * I)‖ ≤ 0.00000016135 := by
  have hl := lg_8
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.5054417751911 40.5054418044096 (-2.8063299) 0.00000006134 (-0.9443238916875) (-0.3290173056224) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_9 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3785569575779:ℝ):ℂ) + ((0.9255779977232:ℝ):ℂ) * I)‖ ≤ 0.00000011847 := by
  have hl := lg_9
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.799737531805253112 42.79973755128429207 1.1825596 0.00000001846 0.3785569575779 0.9255779977232 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_10 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6450115723764:ℝ):ℂ) + (((-0.7641728021204):ℝ):ℂ) * I)‖ ≤ 0.00000013903 := by
  have hl := lg_10
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.852055011240577111 44.85205504045909659 (-0.8697579) 0.00000003902 0.6450115723764 (-0.7641728021204) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_11 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9150002632175):ℝ):ℂ) + (((-0.4034532416233):ℝ):ℂ) * I)‖ ≤ 0.00000014662 := by
  have hl := lg_11
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.708602003649004307 46.708602032867543265 (-2.7263049) 0.00000004661 (-0.9150002632175) (-0.4034532416233) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_12 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2870918279608):ℝ):ℂ) + ((0.9579030651984:ℝ):ℂ) * I)‖ ≤ 0.00000014142 := by
  have hl := lg_12
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.403496616030026556 48.403496645248546035 1.8619858 0.00000004141 (-0.2870918279608) 0.9579030651984 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_13 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.954495179387:ℝ):ℂ) + ((0.2982263444551:ℝ):ℂ) * I)‖ ≤ 0.00000013865 := by
  have hl := lg_13
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.9626485188028343 49.962648548021373258 0.3028339 0.00000003864 0.954495179387 0.2982263444551 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_14 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.416944451642:ℝ):ℂ) + (((-0.9089319689861):ℝ):ℂ) * I)‖ ≤ 0.00000014907 := by
  have hl := lg_14
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.406197708385185138 51.406197737603724096 (-1.1407153) 0.00000004906 0.416944451642 (-0.9089319689861) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p479_15 : ‖exp (-((((((19479:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7918492450104):ℝ):ℂ) + (((-0.6107166062342):ℝ):ℂ) * I)‖ ≤ 0.00000012388 := by
  have hl := lg_15
  refine (ecis_approx ((((19479:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.750109852079503667 52.750109881298042625 (-2.4846274) 0.00000002387 (-0.7918492450104) (-0.6107166062342) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_2 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4544638530227:ℝ):ℂ) + (((-0.8907651802219):ℝ):ℂ) * I)‖ ≤ 0.00000015476 := by
  have hl := lg_2
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.6653966596145 13.665396669472 (-1.0990261) 0.00000005475 0.4544638530227 (-0.8907651802219) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_3 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9453899689387):ℝ):ℂ) + (((-0.3259414156536):ℝ):ℂ) * I)‖ ≤ 0.0000001543 := by
  have hl := lg_3
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.65914126596695326 21.659141275824472975 (-2.8095853) 0.00000005429 (-0.9453899689387) (-0.3259414156536) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_4 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5869251316267):ℝ):ℂ) + (((-0.8096412105704):ℝ):ℂ) * I)‖ ≤ 0.00000011024 := by
  have hl := lg_4
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.330793319229 27.330793338944 (-2.1980521) 0.00000001023 (-0.5869251316267) (-0.8096412105704) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_5 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9510618823428:ℝ):ℂ) + (((-0.3090004788905):ℝ):ℂ) * I)‖ ≤ 0.00000011722 := by
  have hl := lg_5
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.730068433388630435 31.73006845310365015 (-0.3141419) 0.00000001721 0.9510618823428 (-0.3090004788905) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_6 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7199828268822):ℝ):ℂ) + ((0.6939918796121:ℝ):ℂ) * I)‖ ≤ 0.00000011751 := by
  have hl := lg_6
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.32453792558145326 35.324537945296472975 2.3745739 0.0000000175 (-0.7199828268822) 0.6939918796121 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_7 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7872210846402:ℝ):ℂ) + (((-0.6166708716146):ℝ):ℂ) * I)‖ ≤ 0.00000015503 := by
  have hl := lg_7
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.36361857837584473 38.36361859809088416 (-0.6645067) 0.00000005502 0.7872210846402 (-0.6166708716146) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_8 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9879364698179):ℝ):ℂ) + ((0.1548597146389:ℝ):ℂ) * I)‖ ≤ 0.00000015817 := by
  have hl := lg_8
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.9961899788435 40.996190008416 2.9861072 0.00000005816 (-0.9879364698179) 0.1548597146389 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_9 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7875244530462:ℝ):ℂ) + ((0.6162834054673:ℝ):ℂ) * I)‖ ≤ 0.00000011834 := by
  have hl := lg_9
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.31828253193390652 43.31828255164894595 0.6640146 0.00000001833 0.7875244530462 0.6162834054673 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_10 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1569763802449:ℝ):ℂ) + (((-0.9876023572497):ℝ):ℂ) * I)‖ ≤ 0.00000015727 := by
  have hl := lg_10
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.395465093003130435 45.39546512257565015 (-1.413168) 0.00000005726 0.1569763802449 (-0.9876023572497) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_11 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.988678918272):ℝ):ℂ) + ((0.1500466466524:ℝ):ℂ) * I)‖ ≤ 0.00000016 := by
  have hl := lg_11
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.274505287845378095 47.274505317417917525 2.9909772 0.00000005999 (-0.988678918272) 0.1500466466524 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_12 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2909775364391:ℝ):ℂ) + ((0.9567298852277:ℝ):ℂ) * I)‖ ≤ 0.00000015735 := by
  have hl := lg_12
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.98993458519595326 48.989934614768472975 1.2755479 0.00000005734 0.2909775364391 0.9567298852277 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_13 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9545964615919:ℝ):ℂ) + (((-0.2979019897822):ℝ):ℂ) * I)‖ ≤ 0.00000013913 := by
  have hl := lg_13
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.5679765669797155 50.56797659655225493 (-0.3024941) 0.00000003912 0.9545964615919 (-0.2979019897822) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_14 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1915454127853):ℝ):ℂ) + (((-0.9814837516944):ℝ):ℂ) * I)‖ ≤ 0.00000011946 := by
  have hl := lg_14
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.02901523799034473 52.02901526756288416 (-1.7635328) 0.00000001945 (-0.1915454127853) (-0.9814837516944) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p715_15 : ‖exp (-((((((19715:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.999840418498):ℝ):ℂ) + (((-0.0178644029661):ℝ):ℂ) * I)‖ ≤ 0.0000001581 := by
  have hl := lg_15
  refine (ecis_approx ((((19715:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.389209699355583695 53.389209728928123125 (-3.1237273) 0.00000005809 (-0.999840418498) (-0.0178644029661) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_2 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3420364717452:ℝ):ℂ) + (((-0.9396866775666):ℝ):ℂ) * I)‖ ≤ 0.00000010613 := by
  have hl := lg_2
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.7880837105276 13.7880837204736 (-1.2217131) 0.00000000612 0.3420364717452 (-0.9396866775666) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_3 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9905544994455):ℝ):ℂ) + (((-0.137119594571):ℝ):ℂ) * I)‖ ≤ 0.00000012944 := by
  have hl := lg_3
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.853595641015198288 21.85359565096121818 (-3.0040397) 0.00000002943 (-0.9905544994455) (-0.137119594571) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_4 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7660221039854):ℝ):ℂ) + (((-0.6428142314602):ℝ):ℂ) * I)‖ ≤ 0.00000011224 := by
  have hl := lg_4
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.5761674210552 27.5761674409472 (-2.4434262) 0.00000001223 (-0.7660221039854) (-0.6428142314602) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_5 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8258928532287:ℝ):ℂ) + (((-0.5638270967112):ℝ):ℂ) * I)‖ ≤ 0.00000012781 := by
  have hl := lg_5
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.014938943797445428 32.01493896368946532 (-0.5990124) 0.0000000278 0.8258928532287 (-0.5638270967112) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_6 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4676552162154):ℝ):ℂ) + ((0.8839109676554:ℝ):ℂ) * I)‖ ≤ 0.00000012837 := by
  have hl := lg_6
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.641679351542798288 35.64167937143481818 2.0574325 0.00000002836 (-0.4676552162154) 0.8839109676554 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_7 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5327641572751:ℝ):ℂ) + (((-0.8462637607289):ℝ):ℂ) * I)‖ ≤ 0.0000001515 := by
  have hl := lg_7
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.708044674666614424 38.708044694558654208 (-1.0089328) 0.00000005149 0.5327641572751 (-0.8462637607289) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_8 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8660514635902):ℝ):ℂ) + ((0.4999548602908:ℝ):ℂ) * I)‖ ≤ 0.00000011869 := by
  have hl := lg_8
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.3642511315828 41.3642511614208 2.618046 0.00000001868 (-0.8660514635902) 0.4999548602908 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
