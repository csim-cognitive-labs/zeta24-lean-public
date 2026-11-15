/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Base
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
namespace H22

open Complex Set

lemma cs_b1left_v21p013_28 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6180197548295:ℝ):ℂ) + (((-0.7861625675651):ℝ):ℂ) * I)‖ ≤ 0.00000012853 := by
  have hl := lg_28
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.019613350462622486 70.019613392488664512 (-0.904575) 0.00000002852 0.6180197548295 (-0.7861625675651) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_29 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0710925511797):ℝ):ℂ) + (((-0.9974697234334):ℝ):ℂ) * I)‖ ≤ 0.00000012533 := by
  have hl := lg_29
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.756987253656838996 70.756987295682902035 (-1.6419489) 0.00000002532 (-0.0710925511797) (-0.9974697234334) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_30 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7057816334946):ℝ):ℂ) + (((-0.7084294501198):ℝ):ℂ) * I)‖ ≤ 0.00000012208 := by
  have hl := lg_30
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.469360559017923849 71.469360601043965875 (-2.3543222) 0.00000002207 (-0.7057816334946) (-0.7084294501198) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_31 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9951765696347):ℝ):ℂ) + (((-0.0980999223806):ℝ):ℂ) * I)‖ ≤ 0.00000016906 := by
  have hl := lg_31
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.158373105997412719 72.158373148023475758 (-3.0433347) 0.00000006905 (-0.9951765696347) (-0.0980999223806) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_32 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8425062065935):ℝ):ℂ) + ((0.5386866359787:ℝ):ℂ) * I)‖ ≤ 0.00000016461 := by
  have hl := lg_32
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.8255084982195 72.825508550752 2.5727152 0.0000000646 (-0.8425062065935) 0.5386866359787 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_33 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3478847439718):ℝ):ℂ) + ((0.9375373085426:ℝ):ℂ) * I)‖ ≤ 0.00000012313 := by
  have hl := lg_33
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.472113367246184061 73.4721134092722471 1.9261103 0.00000002312 (-0.3478847439718) 0.9375373085426 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_34 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2686452731921:ℝ):ℂ) + ((0.963239179639:ℝ):ℂ) * I)‖ ≤ 0.00000014284 := by
  have hl := lg_34
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.099413676448227642 74.099413728980748655 1.29881 0.00000004283 0.2686452731921 0.963239179639 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_35 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7714401865923:ℝ):ℂ) + ((0.6363018454401:ℝ):ℂ) * I)‖ ≤ 0.00000015011 := by
  have hl := lg_35
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.708528794228096203 74.708528836254159242 0.6896949 0.0000000501 0.7714401865923 0.6363018454401 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_36 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9952272280501:ℝ):ℂ) + ((0.0975846532385:ℝ):ℂ) * I)‖ ≤ 0.00000015424 := by
  have hl := lg_36
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.300483431929300264 75.30048347395534229 0.0977402 0.00000005423 0.9952272280501 0.0975846532385 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_37 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8879192825354:ℝ):ℂ) + (((-0.4599992909798):ℝ):ℂ) * I)‖ ≤ 0.00000013243 := by
  have hl := lg_37
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.876218076544139746 75.876218118570202785 (-0.4779944) 0.00000003242 0.8879192825354 (-0.4599992909798) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_38 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5076215982227:ℝ):ℂ) + (((-0.8615801257096):ℝ):ℂ) * I)‖ ≤ 0.00000013369 := by
  have hl := lg_38
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.436597952481588839 76.436597994507651878 (-1.0383743) 0.00000003368 0.5076215982227 (-0.8615801257096) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_39 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.013400472113):ℝ):ℂ) + (((-0.9999102096423):ℝ):ℂ) * I)‖ ≤ 0.0000001379 := by
  have hl := lg_39
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.982420848273312232 76.982420890299375271 (-1.5841972) 0.00000003789 (-0.013400472113) (-0.9999102096423) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_40 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5187634967059):ℝ):ℂ) + (((-0.8549177939886):ℝ):ℂ) * I)‖ ≤ 0.00000014419 := by
  have hl := lg_40
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.514423941984973717 77.51442399451749473 (-2.1162003) 0.00000004418 (-0.5187634967059) (-0.8549177939886) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_41 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8744349454798):ℝ):ℂ) + (((-0.4851427893231):ℝ):ℂ) * I)‖ ≤ 0.00000017582 := by
  have hl := lg_41
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.03328981034643954 78.033289862878981566 (-2.6350662) 0.00000007581 (-0.8744349454798) (-0.4851427893231) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_42 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999999861011):ℝ):ℂ) + (((-0.0001646532846):ℝ):ℂ) * I)‖ ≤ 0.00000012303 := by
  have hl := lg_42
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.539651667139472618 78.539651709165535657 (-3.141428) 0.00000002302 (-0.9999999861011) (-0.0001646532846) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_43 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8803097200204):ℝ):ℂ) + ((0.4743994063456:ℝ):ℂ) * I)‖ ≤ 0.00000015793 := by
  have hl := lg_43
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.03409800921987914 79.034098051245963192 2.647311 0.00000005792 (-0.8803097200204) 0.4743994063456 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_44 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5592127401291):ℝ):ℂ) + ((0.8290241922092:ℝ):ℂ) * I)‖ ≤ 0.00000014314 := by
  have hl := lg_44
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.517176750213233929 79.517176802745775955 2.1642322 0.00000004313 (-0.5592127401291) 0.8290241922092 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_45 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1209171633304):ℝ):ℂ) + ((0.9926626010945:ℝ):ℂ) * I)‖ ≤ 0.0000001244 := by
  have hl := lg_45
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.989398875694773981 79.98939891772083702 1.6920101 0.00000002439 (-0.1209171633304) 0.9926626010945 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_46 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3340800440711:ℝ):ℂ) + ((0.9425447067134:ℝ):ℂ) * I)‖ ≤ 0.00000015624 := by
  have hl := lg_46
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.451241637114147758 80.451241689646710797 1.2301673 0.00000005623 0.3340800440711 0.9425447067134 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_47 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7121379927087:ℝ):ℂ) + ((0.7020395140879:ℝ):ℂ) * I)‖ ≤ 0.00000016593 := by
  have hl := lg_47
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.903151527422243277 80.903151579954827329 0.7782574 0.00000006592 0.7121379927087 0.7020395140879 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_48 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9441264938575:ℝ):ℂ) + ((0.3295833181403:ℝ):ℂ) * I)‖ ≤ 0.00000017411 := by
  have hl := lg_48
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.345546814896350132 81.345546867428871145 0.3358622 0.0000000741 0.9441264938575 0.3295833181403 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_49 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9952593087154:ℝ):ℂ) + (((-0.0972569196273):ℝ):ℂ) * I)‖ ≤ 0.00000015106 := by
  have hl := lg_49
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.778819902349644972 81.778819944375729024 (-0.0974109) 0.00000005105 0.9952593087154 (-0.0972569196273) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p013_50 : ‖exp (-((((((21013:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8668583859159:ℝ):ℂ) + (((-0.49855444915):ℝ):ℂ) * I)‖ ≤ 0.00000014496 := by
  have hl := lg_50
  refine (ecis_approx ((((21013:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.203339385750447434 82.20333943828298946 (-0.5219304) 0.00000004495 0.8668583859159 (-0.49855444915) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
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

lemma cs_b1left_v21p155_2 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5023908280716):ℝ):ℂ) + (((-0.86464065129):ℝ):ℂ) * I)‖ ≤ 0.00000011513 := by
  have hl := lg_2
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.6635285992465 14.663528609824 (-2.097158) 0.00000001512 (-0.5023908280716) (-0.86464065129) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_3 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3153277207468):ℝ):ℂ) + ((0.9489828389:ℝ):ℂ) * I)‖ ≤ 0.00000014315 := by
  have hl := lg_3
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.24114296127470942 23.241142971852230575 1.8915983 0.00000004314 (-0.3153277207468) 0.9489828389 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_4 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4952069055012):ℝ):ℂ) + ((0.8687750691277:ℝ):ℂ) * I)‖ ≤ 0.00000013742 := by
  have hl := lg_4
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.327057198493 29.327057219648 2.0888693 0.00000003741 (-0.4952069055012) 0.8687750691277 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_5 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8728127689229):ℝ):ℂ) + (((-0.4880551918739):ℝ):ℂ) * I)‖ ≤ 0.00000011182 := by
  have hl := lg_5
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.047659026545091395 34.04765904770011255 (-2.6317325) 0.00000001181 (-0.8728127689229) (-0.4880551918739) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_6 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9789468946337:ℝ):ℂ) + (((-0.2041151084241):ℝ):ℂ) * I)‖ ≤ 0.00000013861 := by
  have hl := lg_6
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.90467156052120942 37.904671581676230575 (-0.2055597) 0.0000000386 0.9789468946337 (-0.2041151084241) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_7 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9476428220163):ℝ):ℂ) + ((0.319332243414:ℝ):ℂ) * I)‖ ≤ 0.00000015801 := by
  have hl := lg_7
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.16572919226685241 41.16572921342189472 2.8165679 0.000000058 (-0.9476428220163) 0.319332243414 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_8 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999656489228:ℝ):ℂ) + (((-0.0082886050912):ℝ):ℂ) * I)‖ ≤ 0.00000015253 := by
  have hl := lg_8
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.9905857977395 43.990585829472 (-0.0082887) 0.00000005252 0.9999656489228 (-0.0082886050912) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_9 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8011369125984):ℝ):ℂ) + (((-0.5984811168471):ℝ):ℂ) * I)‖ ≤ 0.00000012772 := by
  have hl := lg_9
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.48228592254941884 46.48228594370446115 (-2.4999888) 0.00000002771 (-0.8011369125984) (-0.5984811168471) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_10 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0165007779097:ℝ):ℂ) + ((0.9998638528961:ℝ):ℂ) * I)‖ ≤ 0.00000013166 := by
  have hl := lg_10
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.711187625791591395 48.71118765752411255 1.5542948 0.00000003165 0.0165007779097 0.9998638528961 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_11 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8951663756851:ℝ):ℂ) + (((-0.4457321615532):ℝ):ℂ) * I)‖ ≤ 0.00000015386 := by
  have hl := lg_11
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.727474479552065615 50.727474511284607925 (-0.461992) 0.00000005385 0.8951663756851 (-0.4457321615532) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_12 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6683001613178):ℝ):ℂ) + (((-0.743891722204):ℝ):ℂ) * I)‖ ≤ 0.00000013408 := by
  have hl := lg_12
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.56820015976770942 52.568200191500230575 (-2.3027177) 0.00000003407 (-0.6683001613178) (-0.743891722204) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_13 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6566495994103):ℝ):ℂ) + ((0.7541957992303:ℝ):ℂ) * I)‖ ≤ 0.00000012403 := by
  have hl := lg_13
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.2615036406013635 54.26150367233390581 2.2871641 0.00000002402 (-0.6566495994103) 0.7541957992303 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_14 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.752194635223:ℝ):ℂ) + ((0.6589409918511:ℝ):ℂ) * I)‖ ≤ 0.00000015864 := by
  have hl := lg_14
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.82925779151335241 55.82925782324589472 0.71941 0.00000005863 0.752194635223 0.6589409918511 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_15 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7383780626423:ℝ):ℂ) + (((-0.6743870080366):ℝ):ℂ) * I)‖ ≤ 0.00000015495 := by
  have hl := lg_15
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.288801987819800815 57.288802019552343125 (-0.7401342) 0.00000005494 0.7383780626423 (-0.6743870080366) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_16 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5095402353098):ℝ):ℂ) + (((-0.8604468307767):ℝ):ℂ) * I)‖ ≤ 0.00000016765 := by
  have hl := lg_16
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.654114396986 58.654114439296 (-2.1054467) 0.00000006764 (-0.5095402353098) (-0.8604468307767) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_17 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9698046358566):ℝ):ℂ) + ((0.2438831031465:ℝ):ℂ) * I)‖ ≤ 0.00000014204 := by
  have hl := lg_17
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.93662827151266127 59.936628313822682425 2.8952248 0.00000004203 (-0.9698046358566) 0.2438831031465 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_18 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1149872586254):ℝ):ℂ) + ((0.9933669666107:ℝ):ℂ) * I)‖ ≤ 0.00000015001 := by
  have hl := lg_18
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.14581452179591884 61.14581455352846115 1.6860385 0.00000005 (-0.1149872586254) 0.9933669666107 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_19 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8565515115051:ℝ):ℂ) + ((0.5160615352246:ℝ):ℂ) * I)‖ ≤ 0.00000014772 := by
  have hl := lg_19
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.289606587768586465 62.28960661950114993 0.5422465 0.00000004771 0.8565515115051 0.5160615352246 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_20 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8562330934951:ℝ):ℂ) + (((-0.5165896723743):ℝ):ℂ) * I)‖ ≤ 0.00000014677 := by
  have hl := lg_20
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.374716225038091395 63.37471626734811255 (-0.5428632) 0.00000004676 0.8562330934951 (-0.5165896723743) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_21 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0042227606552):ℝ):ℂ) + (((-0.9999910841064):ℝ):ℂ) * I)‖ ≤ 0.00000011827 := by
  have hl := lg_21
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.40687215354156183 64.406872185274125295 (-1.5750191) 0.00000001826 (-0.0042227606552) (-0.9999910841064) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_22 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.835121523195):ℝ):ℂ) + (((-0.5500654883113):ℝ):ℂ) * I)‖ ≤ 0.00000014933 := by
  have hl := lg_22
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.391003078798565615 65.391003121108607925 (-2.55915) 0.00000004932 (-0.835121523195) (-0.5500654883113) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_23 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9366224653876):ℝ):ℂ) + ((0.3503403447491:ℝ):ℂ) * I)‖ ≤ 0.00000016301 := by
  have hl := lg_23
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.33138011598453773 66.331380158294601195 2.7836582 0.000000063 (-0.9366224653876) 0.3503403447491 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_24 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.30745114491):ℝ):ℂ) + ((0.9515638672689:ℝ):ℂ) * I)‖ ≤ 0.00000012236 := by
  have hl := lg_24
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.23172875901420942 67.231728801324230575 1.8833096 0.00000002235 (-0.30745114491) 0.9515638672689 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_25 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5236042653903:ℝ):ℂ) + ((0.8519616031636:ℝ):ℂ) * I)‖ ≤ 0.0000001259 := by
  have hl := lg_25
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.09531805309018279 68.0953180954002251 1.0197203 0.00000002589 0.5236042653903 0.8519616031636 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_26 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9820030830597:ℝ):ℂ) + ((0.1888648851988:ℝ):ℂ) * I)‖ ≤ 0.00000013914 := by
  have hl := lg_26
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.9250322398478635 68.92503228215790581 0.1900061 0.00000003913 0.9820030830597 0.1888648851988 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_27 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8205689859796:ℝ):ℂ) + (((-0.5715474951817):ℝ):ℂ) * I)‖ ≤ 0.0000001366 := by
  have hl := lg_27
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.72342888382412826 69.723428915556691725 (-0.6083905) 0.00000003659 0.8205689859796 (-0.5715474951817) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_28 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1918514826973:ℝ):ℂ) + (((-0.9814239698452):ℝ):ℂ) * I)‖ ≤ 0.00000015411 := by
  have hl := lg_28
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.49278639075985241 70.49278643306989472 (-1.377748) 0.0000000541 0.1918514826973 (-0.9814239698452) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_29 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5220976457387):ℝ):ℂ) + (((-0.8528857181984):ℝ):ℂ) * I)‖ ≤ 0.00000012472 := by
  have hl := lg_29
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.23514326136726926 71.235143303677332725 (-2.1201049) 0.00000002471 (-0.5220976457387) (-0.8528857181984) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_30 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9540567880959):ℝ):ℂ) + (((-0.2996258414649):ℝ):ℂ) * I)‖ ≤ 0.00000015042 := by
  have hl := lg_30
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.952330587066300815 71.952330629376343125 (-2.8372922) 0.00000005041 (-0.9540567880959) (-0.2996258414649) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_31 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9251490578918):ℝ):ℂ) + ((0.3796040312362:ℝ):ℂ) * I)‖ ≤ 0.00000014506 := by
  have hl := lg_31
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.645999288886654265 72.64599933119671773 2.7522244 0.00000004505 (-0.9251490578918) 0.3796040312362 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_32 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4879890484344):ℝ):ℂ) + ((0.8728497514477:ℝ):ℂ) * I)‖ ≤ 0.00000016298 := by
  have hl := lg_32
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.3176429962325 73.31764304912 2.0805807 0.00000006297 (-0.4879890484344) 0.8728497514477 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_33 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1407214981313:ℝ):ℂ) + ((0.9900492209803:ℝ):ℂ) * I)‖ ≤ 0.00000014534 := by
  have hl := lg_33
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.968617440826775035 73.9686174831368385 1.4296062 0.00000004533 0.1407214981313 0.9900492209803 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_34 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6980921993909:ℝ):ℂ) + ((0.7160078778545:ℝ):ℂ) * I)‖ ≤ 0.00000013751 := by
  have hl := lg_34
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.60015687075916127 74.600156923646682425 0.7980668 0.0000000375 0.6980921993909 0.7160078778545 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_35 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9829665149141:ℝ):ℂ) + ((0.1837847397301:ℝ):ℂ) * I)‖ ≤ 0.00000016736 := by
  have hl := lg_35
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.213388218811943805 75.21338826112200727 0.1848354 0.00000006735 0.9829665149141 0.1837847397301 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_36 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9166740050625:ℝ):ℂ) + (((-0.3996357947465):ℝ):ℂ) * I)‖ ≤ 0.00000016513 := by
  have hl := lg_36
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.80934312104241884 75.80934316335246115 (-0.4111195) 0.00000006512 0.9166740050625 (-0.3996357947465) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_37 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5480670363038:ℝ):ℂ) + (((-0.8364344108878):ℝ):ℂ) * I)‖ ≤ 0.00000016618 := by
  have hl := lg_37
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.38896841999197051 76.388968462302033975 (-0.9907448) 0.00000006617 0.5480670363038 (-0.8364344108878) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_38 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0158841587729:ℝ):ℂ) + (((-0.9998738387916):ℝ):ℂ) * I)‖ ≤ 0.00000014319 := by
  have hl := lg_38
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.953135187015086465 76.95313522932514993 (-1.5549115) 0.00000004318 0.0158841587729 (-0.9998738387916) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_39 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5086590429569):ℝ):ℂ) + (((-0.8609680470328):ℝ):ℂ) * I)‖ ≤ 0.00000015805 := by
  have hl := lg_39
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.50264660187607292 77.502646644186136385 (-2.1044229) 0.00000005804 (-0.5086590429569) (-0.8609680470328) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_40 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8768280836114):ℝ):ℂ) + (((-0.4808040262903):ℝ):ℂ) * I)‖ ≤ 0.00000016189 := by
  have hl := lg_40
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.038244824284591395 78.03824487717211255 (-2.6400212) 0.00000006188 (-0.8768280836114) (-0.4808040262903) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_41 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997836718122):ℝ):ℂ) + ((0.0207992533542:ℝ):ℂ) * I)‖ ≤ 0.00000014972 := by
  have hl := lg_41
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.5606170436338899 78.56061709652143221 3.1207919 0.00000004971 (-0.9997836718122) 0.0207992533542 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_42 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.862511462373):ℝ):ℂ) + ((0.506037525479:ℝ):ℂ) * I)‖ ≤ 0.00000014056 := by
  have hl := lg_42
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.07040075278806183 79.070400795098125295 2.6110082 0.00000004055 (-0.862511462373) 0.506037525479 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_43 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5162137133305):ℝ):ℂ) + ((0.8564598076749:ℝ):ℂ) * I)‖ ≤ 0.00000016785 := by
  have hl := lg_43
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.5681884255007159 79.56818846781080052 2.1132205 0.00000006784 (-0.5162137133305) 0.8564598076749 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_44 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0560515813445):ℝ):ℂ) + ((0.9984278743247:ℝ):ℂ) * I)‖ ≤ 0.00000013761 := by
  have hl := lg_44
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.054531678045065615 80.054531730932607925 1.6268773 0.0000000376 (-0.0560515813445) 0.9984278743247 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_45 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4071507171983:ℝ):ℂ) + ((0.9133609874989:ℝ):ℂ) * I)‖ ≤ 0.00000014426 := by
  have hl := lg_45
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.529944949094510235 80.5299449914045737 1.151464 0.00000004425 0.4071507171983 0.9133609874989 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_46 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7734689765591:ℝ):ℂ) + ((0.6338341599351:ℝ):ℂ) * I)‖ ≤ 0.0000001748 := by
  have hl := lg_46
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.99490871523103773 80.994908768118601195 0.6865003 0.00000007479 0.7734689765591 0.6338341599351 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_47 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.973314958347:ℝ):ℂ) + ((0.2294732922542:ℝ):ℂ) * I)‖ ≤ 0.00000014625 := by
  have hl := lg_47
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.449872486680509995 81.449872539568094615 0.2315365 0.00000004624 0.973314958347 0.2294732922542 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_48 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9772214372265:ℝ):ℂ) + (((-0.2122222010651):ℝ):ℂ) * I)‖ ≤ 0.00000013509 := by
  have hl := lg_48
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.89525735826070942 81.895257411148230575 (-0.2138484) 0.00000003508 0.9772214372265 (-0.2122222010651) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_49 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7960539013693:ℝ):ℂ) + (((-0.6052257315372):ℝ):ℂ) * I)‖ ≤ 0.00000013352 := by
  have hl := lg_49
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.33145838453370482 82.33145842684378944 (-0.6500494) 0.00000003351 0.7960539013693 (-0.6052257315372) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p155_50 : ‖exp (-((((((21155:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4735866549652:ℝ):ℂ) + (((-0.8807472283459):ℝ):ℂ) * I)‖ ≤ 0.00000014101 := by
  have hl := lg_50
  refine (ecis_approx ((((21155:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.75884665233668279 82.7588467052242251 (-1.0774377) 0.000000041 0.4735866549652 (-0.8807472283459) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_2 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5119488603176):ℝ):ℂ) + (((-0.8590159279156):ℝ):ℂ) * I)‖ ≤ 0.00000015037 := by
  have hl := lg_2
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.6746189541313 14.6746189647168 (-2.1082483) 0.00000005036 (-0.5119488603176) (-0.8590159279156) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_3 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2985988356268):ℝ):ℂ) + ((0.9543787169466:ℝ):ℂ) * I)‖ ≤ 0.00000013977 := by
  have hl := lg_3
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.258720757889240044 23.258720768474761215 1.8740205 0.00000003976 (-0.2985988356268) 0.9543787169466 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_4 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4758166345693):ℝ):ℂ) + ((0.8795445015813:ℝ):ℂ) * I)‖ ≤ 0.00000012765 := by
  have hl := lg_4
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.3492379082626 29.3492379294336 2.0666886 0.00000002764 (-0.4758166345693) 0.8795445015813 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_5 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8850899180267):ℝ):ℂ) + (((-0.4654200650022):ℝ):ℂ) * I)‖ ≤ 0.00000011842 := by
  have hl := lg_5
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.073410033135718739 34.07341005430673991 (-2.6574835) 0.00000001841 (-0.8850899180267) (-0.4654200650022) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_6 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9726938295073:ℝ):ℂ) + (((-0.2320920378608):ℝ):ℂ) * I)‖ ≤ 0.00000013107 := by
  have hl := lg_6
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.933339712020540044 37.933339733191561215 (-0.2342279) 0.00000003106 0.9726938295073 (-0.2320920378608) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_7 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9372429134353):ℝ):ℂ) + ((0.3486771014013:ℝ):ℂ) * I)‖ ≤ 0.00000012557 := by
  have hl := lg_7
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.196863754643419162 41.196863775814461504 2.7854334 0.00000002556 (-0.9372429134353) 0.3486771014013 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_8 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9991365199629:ℝ):ℂ) + (((-0.0415477373208):ℝ):ℂ) * I)‖ ≤ 0.00000014391 := by
  have hl := lg_8
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.0238568623939 44.0238568941504 (-0.0415597) 0.0000000439 0.9991365199629 (-0.0415477373208) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_9 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8216775236151):ℝ):ℂ) + (((-0.5699526709538):ℝ):ℂ) * I)‖ ≤ 0.00000013449 := by
  have hl := lg_9
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.517441515778480088 46.51744153694952243 (-2.5351444) 0.00000003448 (-0.8216775236151) (-0.5699526709538) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_10 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0533175329389:ℝ):ℂ) + ((0.9985776087421:ℝ):ℂ) * I)‖ ≤ 0.0000001616 := by
  have hl := lg_10
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.748028987267018739 48.74802901902353991 1.5174535 0.00000006159 0.0533175329389 0.9985776087421 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_11 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.877410679418:ℝ):ℂ) + (((-0.4797400333964):ℝ):ℂ) * I)‖ ≤ 0.00000015355 := by
  have hl := lg_11
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.765840803904362143 50.765840835660904485 (-0.5003584) 0.00000005354 0.877410679418 (-0.4797400333964) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_12 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.697340254717):ℝ):ℂ) + (((-0.7167402382509):ℝ):ℂ) * I)‖ ≤ 0.00000014049 := by
  have hl := lg_12
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.607958666151840044 52.607958697908361215 (-2.3424762) 0.00000004048 (-0.697340254717) (-0.7167402382509) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_13 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6251538023749):ℝ):ℂ) + ((0.7805015844711:ℝ):ℂ) * I)‖ ≤ 0.00000013432 := by
  have hl := lg_13
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.3025428303082707 54.302542862064813042 2.2461249 0.00000003431 (-0.6251538023749) 0.7805015844711 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_14 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7793396879473:ℝ):ℂ) + ((0.626601668359:ℝ):ℂ) * I)‖ ≤ 0.00000015586 := by
  have hl := lg_14
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.871482708774719162 55.871482740531261504 0.677185 0.00000005585 0.7793396879473 0.626601668359 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_15 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7084738234869:ℝ):ℂ) + (((-0.705737090873):ℝ):ℂ) * I)‖ ≤ 0.00000015818 := by
  have hl := lg_15
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.332130791024958783 57.332130822781501125 (-0.783463) 0.00000005817 0.7084738234869 (-0.705737090873) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_16 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5471970545245):ℝ):ℂ) + (((-0.8370038133194):ℝ):ℂ) * I)‖ ≤ 0.00000014811 := by
  have hl := lg_16
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.6984758165252 58.6984758588672 (-2.1498081) 0.0000000481 (-0.5471970545245) (-0.8370038133194) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_17 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.957756586872):ℝ):ℂ) + ((0.2875801107125:ℝ):ℂ) * I)‖ ≤ 0.00000015556 := by
  have hl := lg_17
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.981959685000924214 59.981959727342945385 2.8498934 0.00000005555 (-0.957756586872) 0.2875801107125 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_18 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0689415436049):ℝ):ℂ) + ((0.9976207012512:ℝ):ℂ) * I)‖ ≤ 0.00000012989 := by
  have hl := lg_18
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.192060469909780088 61.19206050166632243 1.6397926 0.00000002988 (-0.0689415436049) 0.9976207012512 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_19 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8799043824845:ℝ):ℂ) + ((0.4751507946795:ℝ):ℂ) * I)‖ ≤ 0.00000016039 := by
  have hl := lg_19
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.336717611422772113 62.336717643179335626 0.4951354 0.00000006038 0.8799043824845 0.4751507946795 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_20 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8304981652481:ℝ):ℂ) + (((-0.5570213618162):ℝ):ℂ) * I)‖ ≤ 0.00000013041 := by
  have hl := lg_20
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.422647941398318739 63.42264798374033991 (-0.5907949) 0.0000000304 0.8304981652481 (-0.5570213618162) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_21 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0529104547732):ℝ):ℂ) + (((-0.9985992608526):ℝ):ℂ) * I)‖ ≤ 0.00000015928 := by
  have hl := lg_21
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.455584512532659206 64.455584544289222719 (-1.6237315) 0.00000005927 (-0.0529104547732) (-0.9985992608526) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_22 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.861293727286):ℝ):ℂ) + (((-0.5081073855558):ℝ):ℂ) * I)‖ ≤ 0.0000001286 := by
  have hl := lg_22
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.440459758035662143 65.440459800377704485 (-2.6086067) 0.00000002859 (-0.861293727286) (-0.5081073855558) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_23 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9178755905751):ℝ):ℂ) + ((0.396868240209:ℝ):ℂ) * I)‖ ≤ 0.00000015557 := by
  have hl := lg_23
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.381548023422767586 66.381548065764831099 2.7334903 0.00000005556 (-0.9178755905751) 0.396868240209 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_24 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2586886286607):ℝ):ℂ) + ((0.9659607618327:ℝ):ℂ) * I)‖ ≤ 0.00000015871 := by
  have hl := lg_24
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.282577620283140044 67.282577662625161215 1.8324607 0.0000000587 (-0.2586886286607) 0.9659607618327 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_25 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5667683319995:ℝ):ℂ) + ((0.8238772104158:ℝ):ℂ) * I)‖ ≤ 0.00000012965 := by
  have hl := lg_25
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.146820066271437478 68.14682010861347982 0.9682183 0.00000002964 0.5667683319995 0.8238772104158 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_26 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9905100694839:ℝ):ℂ) + ((0.1374401769901:ℝ):ℂ) * I)‖ ≤ 0.00000014782 := by
  have hl := lg_26
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.9771617844395707 68.977161826781613042 0.1378766 0.00000004781 0.9905100694839 0.1374401769901 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_27 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7893026506727:ℝ):ℂ) + (((-0.6140043368259):ℝ):ℂ) * I)‖ ≤ 0.00000012646 := by
  have hl := lg_27
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.776162273667720132 69.776162305424283645 (-0.6611239) 0.00000002645 0.7893026506727 (-0.6140043368259) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_28 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1392787485362:ℝ):ℂ) + (((-0.9902532151961):ℝ):ℂ) * I)‖ ≤ 0.00000012629 := by
  have hl := lg_28
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.546101662906019162 70.546101705248061504 (-1.4310633) 0.00000002628 0.1392787485362 (-0.9902532151961) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_29 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5672685239493):ℝ):ℂ) + (((-0.8235328904948):ℝ):ℂ) * I)‖ ≤ 0.00000015801 := by
  have hl := lg_29
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.289019994630416332 71.289020036972479845 (-2.1739816) 0.000000058 (-0.5672685239493) (-0.8235328904948) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_30 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9689417931081):ℝ):ℂ) + (((-0.2472889025037):ℝ):ℂ) * I)‖ ≤ 0.00000013383 := by
  have hl := lg_30
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.006749745156258783 72.006749787498301125 (-2.8917114) 0.00000003382 (-0.9689417931081) (-0.2472889025037) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_31 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9029065837013):ℝ):ℂ) + ((0.4298368306568:ℝ):ℂ) * I)‖ ≤ 0.00000014034 := by
  have hl := lg_31
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.700943084141780073 72.700943126483843586 2.6972806 0.00000004033 (-0.9029065837013) 0.4298368306568 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_32 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4388626924903):ℝ):ℂ) + ((0.898554137009:ℝ):ℂ) * I)‖ ≤ 0.00000013744 := by
  have hl := lg_32
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.3730947706565 73.373094823584 2.0251289 0.00000003743 (-0.4388626924903) 0.898554137009 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p171_33 : ‖exp (-((((((21171:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1958598703006:ℝ):ℂ) + ((0.9806318938347:ℝ):ℂ) * I)‖ ≤ 0.00000012438 := by
  have hl := lg_33
  refine (ecis_approx ((((21171:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.024561561793602187 74.0245616041356657 1.3736621 0.00000002437 0.1958598703006 0.9806318938347 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
