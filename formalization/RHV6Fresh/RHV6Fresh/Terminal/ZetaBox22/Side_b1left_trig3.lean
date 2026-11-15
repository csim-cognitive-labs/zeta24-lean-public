/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Base
/-!
# Certificat (V2), côté b1left (b1), angles 3

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

lemma cs_b1left_v14p279_18 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9085844112586):ℝ):ℂ) + ((0.4177012897885:ℝ):ℂ) * I)‖ ≤ 0.00000013041 := by
  have hl := lg_18
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.271618319864047512 41.27161834128257607 2.7106788 0.0000000304 (-0.9085844112586) 0.4177012897885 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_19 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3596163207104):ℝ):ℂ) + ((0.9331002635709:ℝ):ℂ) * I)‖ ≤ 0.00000014356 := by
  have hl := lg_19
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.043644172382304237 42.043644193800847074 1.938653 0.00000004355 (-0.3596163207104) 0.9331002635709 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_20 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3565385508007:ℝ):ℂ) + ((0.9342806119111:ℝ):ℂ) * I)‖ ≤ 0.00000013104 := by
  have hl := lg_20
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.776061119230390311 42.77606114778840459 1.206236 0.00000003103 0.3565385508007 0.9342806119111 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_21 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8729585870139:ℝ):ℂ) + ((0.487794326903:ℝ):ℂ) * I)‖ ≤ 0.00000014829 := by
  have hl := lg_21
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.472735877117464494 43.472735898536007331 0.5095613 0.00000004828 0.8729585870139 0.487794326903 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_22 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9880581085082:ℝ):ℂ) + (((-0.1540817127733):ℝ):ℂ) * I)‖ ≤ 0.00000015497 := by
  have hl := lg_22
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.136995176656332707 44.136995205214361265 (-0.154698) 0.00000005496 0.9880581085082 (-0.1540817127733) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_23 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7042537943966:ℝ):ℂ) + (((-0.7099483031024):ℝ):ℂ) * I)‖ ≤ 0.00000015587 := by
  have hl := lg_23
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.771721894405257114 44.771721922963299951 (-0.7894248) 0.00000005586 0.7042537943966 (-0.7099483031024) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_24 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1727912323884:ℝ):ℂ) + (((-0.9849584712107):ℝ):ℂ) * I)‖ ≤ 0.00000012158 := by
  have hl := lg_24
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.379430628691273756 45.379430657249288035 (-1.3971335) 0.00000002157 0.1727912323884 (-0.9849584712107) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_25 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3979071306903):ℝ):ℂ) + (((-0.9174257001755):ℝ):ℂ) * I)‖ ≤ 0.00000016183 := by
  have hl := lg_25
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.962327888445980622 45.96232791700400918 (-1.9800308) 0.00000006182 (-0.3979071306903) (-0.9174257001755) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_26 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8244711120415):ℝ):ℂ) + (((-0.5659040425278):ℝ):ℂ) * I)‖ ≤ 0.00000012988 := by
  have hl := lg_26
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.5223604515616943 46.522360480119722858 (-2.5400633) 0.00000002987 (-0.8244711120415) (-0.5659040425278) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_27 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9980390597255):ℝ):ℂ) + (((-0.0625942067234):ℝ):ℂ) * I)‖ ≤ 0.00000015173 := by
  have hl := lg_27
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.061254598540521268 47.061254619959064105 (-3.0789575) 0.00000005172 (-0.9980390597255) (-0.0625942067234) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_28 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8975310094038):ℝ):ℂ) + ((0.4409513431717:ℝ):ℂ) * I)‖ ≤ 0.00000015708 := by
  have hl := lg_28
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.580548185944690738 47.580548214502719296 2.6849343 0.00000005707 (-0.8975310094038) 0.4409513431717 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_29 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5753802361539):ℝ):ℂ) + ((0.8178860457504:ℝ):ℂ) * I)‖ ≤ 0.00000011592 := by
  have hl := lg_29
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.081617141529815068 48.081617170087857905 2.1838653 0.00000001591 (-0.5753802361539) 0.8178860457504 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_30 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1286312833851):ℝ):ℂ) + ((0.9916924890984:ℝ):ℂ) * I)‖ ≤ 0.00000015954 := by
  have hl := lg_30
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.565697397906864067 48.565697426464892625 1.699785 0.00000005953 (-0.1286312833851) 0.9916924890984 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_31 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3327489326541:ℝ):ℂ) + ((0.9430154547077:ℝ):ℂ) * I)‖ ≤ 0.00000014913 := by
  have hl := lg_31
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.033903277996338277 49.033903306554381114 1.2315792 0.00000004912 0.3327489326541 0.9430154547077 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_32 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7121505591019:ℝ):ℂ) + ((0.7020267667054:ℝ):ℂ) * I)‖ ≤ 0.00000011993 := by
  have hl := lg_32
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.4872429375185 49.487242973216 0.7782395 0.00000001992 0.7121505591019 0.7020267667054 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_33 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9431372198001:ℝ):ℂ) + ((0.3324036471335:ℝ):ℂ) * I)‖ ≤ 0.00000012647 := by
  have hl := lg_33
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.926631455332806463 49.9266314838908493 0.338851 0.00000002646 0.9431372198001 0.3324036471335 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_34 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9961813483378:ℝ):ℂ) + (((-0.0873081967732):ℝ):ℂ) * I)‖ ≤ 0.00000014502 := by
  have hl := lg_34
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.352901912435361086 50.352901948132875365 (-0.0874195) 0.00000004501 0.9961813483378 (-0.0873081967732) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_35 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8769429484507:ℝ):ℂ) + (((-0.4805944913984):ℝ):ℂ) * I)‖ ≤ 0.0000001263 := by
  have hl := lg_35
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.766814955160281049 50.766814983718323886 (-0.5013325) 0.00000002629 0.8769429484507 (-0.4805944913984) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_36 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6187981455588:ℝ):ℂ) + (((-0.7855500334498):ℝ):ℂ) * I)‖ ≤ 0.00000015008 := by
  have hl := lg_36
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.169066907367747512 51.16906693592577607 (-0.9035845) 0.00000005007 0.6187981455588 (-0.7855500334498) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_37 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2724918369838:ℝ):ℂ) + (((-0.962158094482):ℝ):ℂ) * I)‖ ≤ 0.00000013094 := by
  have hl := lg_37
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.560296859799827318 51.560296888357870155 (-1.2948144) 0.00000003093 0.2724918369838 (-0.962158094482) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_38 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1046221647525):ℝ):ℂ) + (((-0.9945120424822):ℝ):ℂ) * I)‖ ≤ 0.00000013102 := by
  have hl := lg_38
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.941092759886004237 51.941092788444047074 (-1.6756103) 0.00000003101 (-0.1046221647525) (-0.9945120424822) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_39 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.457976817594):ℝ):ℂ) + (((-0.8889641356892):ℝ):ℂ) * I)‖ ≤ 0.00000012721 := by
  have hl := lg_39
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.311996730238168056 52.311996758796210893 (-2.0465143) 0.0000000272 (-0.457976817594) (-0.8889641356892) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p279_40 : ‖exp (-((((((14279:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7427920451009):ℝ):ℂ) + (((-0.6695222010529):ℝ):ℂ) * I)‖ ≤ 0.00000015072 := by
  have hl := lg_40
  refine (ecis_approx ((((14279:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.673509706734090311 52.67350974243160459 (-2.4080273) 0.00000005071 (-0.7427920451009) (-0.6695222010529) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_2 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8770596332126):ℝ):ℂ) + ((0.480381514731:ℝ):ℂ) * I)‖ ≤ 0.00000011471 := by
  have hl := lg_2
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.925867621896 9.925867629056 2.640503 0.0000000147 (-0.8770596332126) 0.480381514731 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_3 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.999708046241):ℝ):ℂ) + ((0.0241624015995:ℝ):ℂ) * I)‖ ≤ 0.00000015155 := by
  have hl := lg_3
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.73212797000490848 15.7321279771649228 3.1174279 0.00000005154 (-0.999708046241) 0.0241624015995 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_4 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5384672065611:ℝ):ℂ) + (((-0.8426464664723):ℝ):ℂ) * I)‖ ≤ 0.00000013659 := by
  have hl := lg_4
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.851735243792 19.851735258112 (-1.0021793) 0.00000003658 0.5384672065611 (-0.8426464664723) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_5 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4923555349637):ℝ):ℂ) + ((0.8703941791996:ℝ):ℂ) * I)‖ ≤ 0.00000013012 := by
  have hl := lg_5
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.04715089861147288 23.0471509129314872 2.0855903 0.00000003011 (-0.4923555349637) 0.8703941791996 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_6 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8651964050343:ℝ):ℂ) + (((-0.5014331268631):ℝ):ℂ) * I)‖ ≤ 0.00000013683 := by
  have hl := lg_6
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.65799559190090848 25.6579956062209228 (-0.5252544) 0.00000003682 0.8651964050343 (-0.5014331268631) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_7 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9175585179797):ℝ):ℂ) + (((-0.3976007620009):ℝ):ℂ) * I)‖ ≤ 0.00000011264 := by
  have hl := lg_7
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.86543332702724304 27.86543334134727168 (-2.7326921) 0.00000001263 (-0.9175585179797) (-0.3976007620009) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_8 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0674760647074):ℝ):ℂ) + ((0.9977208931817:ℝ):ℂ) * I)‖ ≤ 0.00000015129 := by
  have hl := lg_8
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.777602865688 29.777602887168 1.6383237 0.00000005128 (-0.0674760647074) 0.9977208931817 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_9 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9988323618484:ℝ):ℂ) + (((-0.0483105881182):ℝ):ℂ) * I)‖ ≤ 0.00000011845 := by
  have hl := lg_9
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.46425594000981696 31.4642559543298456 (-0.0483294) 0.00000001844 0.9988323618484 (-0.0483105881182) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_10 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0137038978339:ℝ):ℂ) + (((-0.9999060971831):ℝ):ℂ) * I)‖ ≤ 0.00000011541 := by
  have hl := lg_10
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.97301852050747288 32.9730185419874872 (-1.557092) 0.0000000154 0.0137038978339 (-0.9999060971831) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_11 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9759718406732):ℝ):ℂ) + (((-0.2178966863268):ℝ):ℂ) * I)‖ ≤ 0.00000014061 := by
  have hl := lg_11
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.33786029530539256 34.3378603167854212 (-2.9219338) 0.0000000406 (-0.9759718406732) (-0.2178966863268) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_12 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5179496366336):ℝ):ℂ) + ((0.8554111139704:ℝ):ℂ) * I)‖ ≤ 0.0000001293 := by
  have hl := lg_12
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.58386321379690848 35.5838632352769228 2.1152486 0.00000002929 (-0.5179496366336) 0.8554111139704 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_13 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5660936338589:ℝ):ℂ) + ((0.8243409474874:ℝ):ℂ) * I)‖ ≤ 0.00000015541 := by
  have hl := lg_13
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.730074787681944 36.73007480916197264 0.969037 0.0000000554 0.5660936338589 0.8243409474874 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_14 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9957535936562:ℝ):ℂ) + (((-0.0920585722285):ℝ):ℂ) * I)‖ ≤ 0.00000012734 := by
  have hl := lg_14
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.79130094892324304 37.79130097040327168 (-0.0921891) 0.00000002733 0.9957535936562 (-0.0920585722285) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_15 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4711810706482:ℝ):ℂ) + (((-0.8820365064229):ℝ):ℂ) * I)‖ ≤ 0.00000014703 := by
  have hl := lg_15
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.77927886861638136 38.77927889009641 (-1.080167) 0.00000004702 0.4711810706482 (-0.8820365064229) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_16 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4201062256642):ℝ):ℂ) + (((-0.9074749358271):ℝ):ℂ) * I)‖ ≤ 0.00000015551 := by
  have hl := lg_16
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.703470487584 39.703470516224 (-2.0043587) 0.0000000555 (-0.4201062256642) (-0.9074749358271) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_17 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9640133680623):ℝ):ℂ) + (((-0.2658537679814):ℝ):ℂ) * I)‖ ≤ 0.00000015757 := by
  have hl := lg_17
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.57161507199533488 40.5716151006353492 (-2.8725032) 0.00000005756 (-0.9640133680623) (-0.2658537679814) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_18 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.85282803143):ℝ):ℂ) + ((0.522191869653:ℝ):ℂ) * I)‖ ≤ 0.00000013314 := by
  have hl := lg_18
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.39012356190581696 41.3901235833858456 2.5921736 0.00000003313 (-0.85282803143) 0.522191869653 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_19 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.244626696725):ℝ):ℂ) + ((0.9696173365035:ℝ):ℂ) * I)‖ ≤ 0.00000014173 := by
  have hl := lg_19
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.16436617049615496 42.16436619197619792 1.817931 0.00000004172 (-0.244626696725) 0.9696173365035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_20 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4683172699966:ℝ):ℂ) + ((0.8835603740678:ℝ):ℂ) * I)‖ ≤ 0.0000001208 := by
  have hl := lg_20
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.89888614240347288 42.8988861710434872 1.083411 0.00000002079 0.4683172699966 0.8835603740678 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_21 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9268976230499:ℝ):ℂ) + ((0.3753142634971:ℝ):ℂ) * I)‖ ≤ 0.00000015324 := by
  have hl := lg_21
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.59756129703215152 43.59756131851219448 0.3847358 0.00000005323 0.9268976230499 0.3753142634971 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_22 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.960659045053:ℝ):ℂ) + (((-0.2777304433401):ℝ):ℂ) * I)‖ ≤ 0.00000013307 := by
  have hl := lg_22
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.26372791720139256 44.2637279458414212 (-0.2814308) 0.00000003306 0.960659045053 (-0.2777304433401) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_23 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6074260348291:ℝ):ℂ) + (((-0.7943762409663):ℝ):ℂ) * I)‖ ≤ 0.00000013561 := by
  have hl := lg_23
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.90027715721572112 44.90027718585576408 (-0.91798) 0.0000000356 0.6074260348291 (-0.7943762409663) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_24 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0433490388221:ℝ):ℂ) + (((-0.9990599886058):ℝ):ℂ) * I)‖ ≤ 0.00000011458 := by
  have hl := lg_24
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.50973083569290848 45.5097308643329228 (-1.5274337) 0.00000001457 0.0433490388221 (-0.9990599886058) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_25 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5151720482272):ℝ):ℂ) + (((-0.8570867871566):ℝ):ℂ) * I)‖ ≤ 0.00000015305 := by
  have hl := lg_25
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.09430179722294576 46.0943018258629744 (-2.1120047) 0.00000005304 (-0.5151720482272) (-0.8570867871566) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_26 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8924960246723):ℝ):ℂ) + (((-0.4510552580738):ℝ):ℂ) * I)‖ ≤ 0.00000014069 := by
  have hl := lg_26
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.655942409577944 46.65594243821797264 (-2.6736453) 0.00000004068 (-0.8924960246723) (-0.4510552580738) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_27 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9973734492017):ℝ):ℂ) + ((0.0724306723717:ℝ):ℂ) * I)‖ ≤ 0.00000014744 := by
  have hl := lg_27
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.19638391001472544 47.1963839314947684 3.0690985 0.00000004743 (-0.9973734492017) 0.0724306723717 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_28 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8291120452576):ℝ):ℂ) + ((0.5590824772309:ℝ):ℂ) * I)‖ ≤ 0.00000014204 := by
  have hl := lg_28
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.71716857081924304 47.71716859945927168 2.5483139 0.00000004203 (-0.8291120452576) 0.5590824772309 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_29 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4573472273261):ℝ):ℂ) + ((0.8892882061809:ℝ):ℂ) * I)‖ ≤ 0.00000014173 := by
  have hl := lg_29
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.21967627051662944 48.2196762991566724 2.0458062 0.00000004172 (-0.4573472273261) 0.8892882061809 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_30 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0104601360371:ℝ):ℂ) + ((0.9999452912804:ℝ):ℂ) * I)‖ ≤ 0.00000016173 := by
  have hl := lg_30
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.70514649051238136 48.70514651915241 1.560336 0.00000006172 0.0104601360371 0.9999452912804 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_31 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4617886014285:ℝ):ℂ) + ((0.8869900154966:ℝ):ℂ) * I)‖ ≤ 0.00000012456 := by
  have hl := lg_31
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.17469675333759816 49.17469678197764112 1.0907857 0.00000002455 0.4617886014285 0.8869900154966 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_32 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8043923965025:ℝ):ℂ) + ((0.5940983693371:ℝ):ℂ) * I)‖ ≤ 0.00000014797 := by
  have hl := lg_32
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.62933810948 49.62933814528 0.6361443 0.00000004796 0.8043923965025 0.5940983693371 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_33 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9809517903295:ℝ):ℂ) + ((0.1942513450388:ℝ):ℂ) * I)‖ ≤ 0.00000013653 := by
  have hl := lg_33
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.06998826531030104 50.069988293950344 0.1954942 0.00000003652 0.9809517903295 0.1942513450388 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_34 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9732084239528:ℝ):ℂ) + (((-0.2299246910346):ℝ):ℂ) * I)‖ ≤ 0.00000016356 := by
  have hl := lg_34
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.49748269389133488 50.4974827296913492 (-0.2320003) 0.00000006355 0.9732084239528 (-0.2299246910346) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_35 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.797834403959:ℝ):ℂ) + (((-0.602876657252):ℝ):ℂ) * I)‖ ≤ 0.00000013181 := by
  have hl := lg_35
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.91258422563871592 50.91258425427875888 (-0.6471018) 0.0000000318 0.797834403959 (-0.602876657252) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_36 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4971297253363:ℝ):ℂ) + (((-0.8676762277411):ℝ):ℂ) * I)‖ ≤ 0.00000015502 := by
  have hl := lg_36
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.31599118380181696 51.3159912124418456 (-1.0505087) 0.00000005501 0.4971297253363 (-0.8676762277411) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_37 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1275855254838:ℝ):ℂ) + (((-0.9918275725583):ℝ):ℂ) * I)‖ ≤ 0.00000016328 := by
  have hl := lg_37
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.70834449417560944 51.7083445228156524 (-1.4428621) 0.00000006327 0.1275855254838 (-0.9918275725583) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_38 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2512340370099):ℝ):ℂ) + (((-0.9679263704675):ℝ):ℂ) * I)‖ ≤ 0.00000016361 := by
  have hl := lg_38
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.09023379239215496 52.09023382103219792 (-1.8247513) 0.0000000636 (-0.2512340370099) (-0.9679263704675) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_39 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5858463312693):ℝ):ℂ) + (((-0.810422159203):ℝ):ℂ) * I)‖ ≤ 0.00000012891 := by
  have hl := lg_39
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.46220275768685248 52.46220278632689544 (-2.1967203) 0.0000000289 (-0.5858463312693) (-0.810422159203) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p32_40 : ‖exp (-((((((14320:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8351882399947):ℝ):ℂ) + (((-0.5499641840241):ℝ):ℂ) * I)‖ ≤ 0.00000014268 := by
  have hl := lg_40
  refine (ecis_approx ((((14320:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.82475376429947288 52.8247538000994872 (-2.5592713) 0.00000004267 (-0.8351882399947) (-0.5499641840241) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_2 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8630553583259):ℝ):ℂ) + ((0.5051093429964:ℝ):ℂ) * I)‖ ≤ 0.00000014912 := by
  have hl := lg_2
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.9542866562883 9.9542866634688 2.612084 0.00000004911 (-0.8630553583259) 0.5051093429964 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_3 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9976060919929):ℝ):ℂ) + ((0.0691526187851:ℝ):ℂ) * I)‖ ≤ 0.00000014772 := by
  have hl := lg_3
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.777171073829643204 15.777171081010157565 3.0723848 0.00000004771 (-0.9976060919929) 0.0691526187851 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_4 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4897290222159:ℝ):ℂ) + (((-0.8718746955839):ℝ):ℂ) * I)‖ ≤ 0.00000010898 := by
  have hl := lg_4
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.9085733125766 19.9085733269376 (-1.0590174) 0.00000000897 0.4897290222159 (-0.8718746955839) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_5 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4338910573961):ℝ):ℂ) + ((0.9009653435663:ℝ):ℂ) * I)‖ ≤ 0.00000013866 := by
  have hl := lg_5
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.113137852999955449 23.11313786736096981 2.0196034 0.00000003865 (-0.4338910573961) 0.9009653435663 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_6 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8260596535079:ℝ):ℂ) + (((-0.563582690336):ℝ):ℂ) * I)‖ ≤ 0.00000011578 := by
  have hl := lg_6
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.731457730117943204 25.731457744478957565 (-0.5987165) 0.00000001577 0.8260596535079 (-0.563582690336) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_7 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9463276994375):ℝ):ℂ) + (((-0.3232087329937):ℝ):ℂ) * I)‖ ≤ 0.00000012877 := by
  have hl := lg_7
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.945215643117195342 27.945215657478224064 (-2.8124744) 0.00000002876 (-0.9463276994375) (-0.3232087329937) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_8 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0177287979396:ℝ):ℂ) + ((0.9998428325109:ℝ):ℂ) * I)‖ ≤ 0.00000015452 := by
  have hl := lg_8
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.8628599688649 29.8628599904064 1.5530666 0.00000005451 0.0177287979396 0.9998428325109 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_9 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9904358453501:ℝ):ℂ) + (((-0.1379740419271):ℝ):ℂ) * I)‖ ≤ 0.00000012614 := by
  have hl := lg_9
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.554342147659286408 31.55434216202031513 (-0.1384156) 0.00000002613 0.9904358453501 (-0.1379740419271) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_10 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0806141032871):ℝ):ℂ) + (((-0.9967453869223):ℝ):ℂ) * I)‖ ≤ 0.00000012662 := by
  have hl := lg_10
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.067424509288255449 33.06742453082976981 (-1.651498) 0.00000002661 (-0.0806141032871) (-0.9967453869223) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_11 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9926467061886):ℝ):ℂ) + (((-0.1210475784717):ℝ):ℂ) * I)‖ ≤ 0.00000013445 := by
  have hl := lg_11
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.436174001458152413 34.436174022999681135 (-3.0202475) 0.00000003444 (-0.9926467061886) (-0.1210475784717) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_12 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4282642374437):ℝ):ℂ) + ((0.9036535524872:ℝ):ℂ) * I)‖ ≤ 0.00000015669 := by
  have hl := lg_12
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.685744386406243204 35.685744407947757565 2.0133674 0.00000005668 (-0.4282642374437) 0.9036535524872 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_13 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6494966215383:ℝ):ℂ) + ((0.7603644774779:ℝ):ℂ) * I)‖ ≤ 0.00000013179 := by
  have hl := lg_13
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.8352377113058937 36.835237732847422422 0.8638741 0.00000003178 0.6494966215383 0.7603644774779 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_14 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9799889227442:ℝ):ℂ) + (((-0.1990520316364):ℝ):ℂ) * I)‖ ≤ 0.00000014369 := by
  have hl := lg_14
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.899502299405495342 37.899502320947024064 (-0.2003905) 0.00000004368 0.9799889227442 (-0.1990520316364) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_15 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.370548255732:ℝ):ℂ) + (((-0.9288132159772):ℝ):ℂ) * I)‖ ≤ 0.00000011626 := by
  have hl := lg_15
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.890308926829598653 38.890308948371127375 (-1.1911971) 0.00000001625 0.370548255732 (-0.9288132159772) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_16 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5203309695987):ℝ):ℂ) + (((-0.8539646843221):ℝ):ℂ) * I)‖ ≤ 0.00000011794 := by
  have hl := lg_16
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.8171466251532 39.8171466538752 (-2.1180348) 0.00000001793 (-0.5203309695987) (-0.8539646843221) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_17 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9883293378557):ℝ):ℂ) + (((-0.1523322669174):ℝ):ℂ) * I)‖ ≤ 0.00000012403 := by
  have hl := lg_17
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.687776819059008674 40.687776847781023035 (-2.988665) 0.00000002402 (-0.9883293378557) (-0.1523322669174) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_18 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7851089238096):ℝ):ℂ) + ((0.6193577138541:ℝ):ℂ) * I)‖ ≤ 0.00000014632 := by
  have hl := lg_18
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.508628803947586408 41.50862882548911513 2.4736683 0.00000004631 (-0.7851089238096) 0.6193577138541 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_19 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1260762595745):ℝ):ℂ) + ((0.9920205525951:ℝ):ℂ) * I)‖ ≤ 0.00000013991 := by
  have hl := lg_19
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.285088168610005683 42.285088190151548766 1.697209 0.0000000399 (-0.1260762595745) 0.9920205525951 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_20 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5730398413687:ℝ):ℂ) + ((0.8195275103401:ℝ):ℂ) * I)‖ ≤ 0.00000014406 := by
  have hl := lg_20
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.021711165576555449 43.02171119429856981 0.960586 0.00000004405 0.5730398413687 0.8195275103401 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_21 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9664130086728:ℝ):ℂ) + ((0.2569939623183:ℝ):ℂ) * I)‖ ≤ 0.00000013333 := by
  have hl := lg_21
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.722386716946838546 43.722386738488381629 0.2599104 0.00000003332 0.9664130086728 0.2569939623183 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_22 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9178513218349:ℝ):ℂ) + (((-0.396924364339):ℝ):ℂ) * I)‖ ≤ 0.00000013623 := by
  have hl := lg_22
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.390460657746452413 44.390460686468481135 (-0.4081635) 0.00000003622 0.9178513218349 (-0.396924364339) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_23 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5005734166739:ℝ):ℂ) + (((-0.8656940883011):ℝ):ℂ) * I)‖ ≤ 0.00000013025 := by
  have hl := lg_23
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.028832420026185126 45.028832448748228209 (-1.0465353) 0.00000003024 0.5005734166739 (-0.8656940883011) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_24 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0868281001687):ℝ):ℂ) + (((-0.9962233088122):ℝ):ℂ) * I)‖ ≤ 0.00000012117 := by
  have hl := lg_24
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.640031042694543204 45.640031071416557565 (-1.6577339) 0.00000002116 (-0.0868281001687) (-0.9962233088122) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_25 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.623477173193):ℝ):ℂ) + (((-0.781841553317):ℝ):ℂ) * I)‖ ≤ 0.00000014427 := by
  have hl := lg_25
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.226275705999910898 46.22627573472193962 (-2.2439786) 0.00000004426 (-0.623477173193) (-0.781841553317) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_26 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9446187387161):ℝ):ℂ) + (((-0.328169831454):ℝ):ℂ) * I)‖ ≤ 0.00000014607 := by
  have hl := lg_26
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.7895243675941937 46.789524396316222422 (-2.8072272) 0.00000004606 (-0.9446187387161) (-0.328169831454) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_27 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9785235668116):ℝ):ℂ) + ((0.2061349773305:ℝ):ℂ) * I)‖ ≤ 0.00000013596 := by
  have hl := lg_27
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.331513221488929612 47.331513243030472695 2.9339692 0.00000003595 (-0.9785235668116) 0.2061349773305 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_28 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7452416499589):ℝ):ℂ) + ((0.6667944834309:ℝ):ℂ) * I)‖ ≤ 0.00000012699 := by
  have hl := lg_28
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.853788955693795342 47.853788984415824064 2.4116935 0.00000002698 (-0.7452416499589) 0.6667944834309 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_29 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3306107790875):ℝ):ℂ) + ((0.9437671920284:ℝ):ℂ) * I)‖ ≤ 0.00000015795 := by
  have hl := lg_29
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.357735399503443812 48.357735428225486895 1.907747 0.00000005794 (-0.3306107790875) 0.9437671920284 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_30 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1493485756951:ℝ):ℂ) + ((0.9887846089709:ℝ):ℂ) * I)‖ ≤ 0.00000015442 := by
  have hl := lg_30
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.844595583117898653 48.844595611839927375 1.4208869 0.00000005441 0.1493485756951 0.9887846089709 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_31 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5816894340871:ℝ):ℂ) + ((0.8134109676365:ℝ):ℂ) * I)‖ ≤ 0.00000012877 := by
  have hl := lg_31
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.315490228678858043 49.315490257400901126 0.9499922 0.00000002876 0.5816894340871 0.8134109676365 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_32 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8804199721073:ℝ):ℂ) + ((0.4741947624285:ℝ):ℂ) * I)‖ ≤ 0.00000015992 := by
  have hl := lg_32
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.7714332814415 49.771433317344 0.4940492 0.00000005991 0.8804199721073 0.4741947624285 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_33 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9986411536161:ℝ):ℂ) + ((0.0521137822875:ℝ):ℂ) * I)‖ ≤ 0.00000014659 := by
  have hl := lg_33
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.213345075287795617 50.2133451040098387 0.0521374 0.00000004658 0.9986411536161 0.0521137822875 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_34 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.929927382355:ℝ):ℂ) + (((-0.3677432032633):ℝ):ℂ) * I)‖ ≤ 0.00000015383 := by
  have hl := lg_34
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.642063475347308674 50.642063511249823035 (-0.376581) 0.00000005382 0.929927382355 (-0.3677432032633) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_35 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7018029222016:ℝ):ℂ) + (((-0.7123711521316):ℝ):ℂ) * I)‖ ≤ 0.00000016133 := by
  have hl := lg_35
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.058353496117150791 51.058353524839193874 (-0.7928711) 0.00000006132 0.7018029222016 (-0.7123711521316) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_36 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3647491023072:ℝ):ℂ) + (((-0.9311058438041):ℝ):ℂ) * I)‖ ≤ 0.00000013154 := by
  have hl := lg_36
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.462915460235886408 51.46291548895791513 (-1.197433) 0.00000003153 0.3647491023072 (-0.9311058438041) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_37 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0201120170958):ℝ):ℂ) + (((-0.9997977329281):ℝ):ℂ) * I)‖ ≤ 0.0000001289 := by
  have hl := lg_37
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.856392128551391562 51.856392157273434645 (-1.5909097) 0.00000002889 (-0.0201120170958) (-0.9997977329281) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_38 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3922681436004):ℝ):ℂ) + (((-0.9198509137426):ℝ):ℂ) * I)‖ ≤ 0.00000013255 := by
  have hl := lg_38
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.239374824898305683 52.239374853620348766 (-1.9738924) 0.00000003254 (-0.3922681436004) (-0.9198509137426) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_39 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7005229050847):ℝ):ℂ) + (((-0.7136299176939):ℝ):ℂ) * I)‖ ≤ 0.00000015644 := by
  have hl := lg_39
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.612408785135536904 52.612408813857579987 (-2.3469263) 0.00000005643 (-0.7005229050847) (-0.7136299176939) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p361_40 : ‖exp (-((((((14361:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9085161467388):ℝ):ℂ) + (((-0.4178497469045):ℝ):ℂ) * I)‖ ≤ 0.00000013559 := by
  have hl := lg_40
  refine (ecis_approx ((((14361:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.975997821864855449 52.97599785776736981 (-2.7105154) 0.00000003558 (-0.9085161467388) (-0.4178497469045) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_2 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8483540397566):ℝ):ℂ) + ((0.529429337264:ℝ):ℂ) * I)‖ ≤ 0.00000012369 := by
  have hl := lg_2
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.9827056906806 9.9827056978816 2.5836649 0.00000002368 (-0.8483540397566) 0.529429337264 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_3 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9934804560165):ℝ):ℂ) + ((0.1140025572617:ℝ):ℂ) * I)‖ ≤ 0.0000001439 := by
  have hl := lg_3
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.822214177654377928 15.82221418485539233 3.0273417 0.00000004389 (-0.9934804560165) 0.1140025572617 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_4 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4394091600524:ℝ):ℂ) + (((-0.8982870309996):ℝ):ℂ) * I)‖ ≤ 0.00000014019 := by
  have hl := lg_4
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.9654113813612 19.9654113957632 (-1.1158555) 0.00000004018 0.4394091600524 (-0.8982870309996) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_5 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3735378932676):ℝ):ℂ) + ((0.9276149213388:ℝ):ℂ) * I)‖ ≤ 0.00000012134 := by
  have hl := lg_5
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.179124807388438018 23.17912482179045242 1.9536164 0.00000002133 (-0.3735378932676) 0.9276149213388 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_6 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7824669267548:ℝ):ℂ) + (((-0.6226921458753):ℝ):ℂ) * I)‖ ≤ 0.00000015403 := by
  have hl := lg_6
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.804919868334977928 25.80491988273699233 (-0.6721786) 0.00000005402 0.7824669267548 (-0.6226921458753) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_7 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9690764956813):ℝ):ℂ) + (((-0.2467605018039):ℝ):ℂ) * I)‖ ≤ 0.00000014491 := by
  have hl := lg_7
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.024997959207147644 28.024997973609176448 (-2.8922567) 0.0000000449 (-0.9690764956813) (-0.2467605018039) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_8 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1028048720166:ℝ):ℂ) + ((0.9947015423179:ℝ):ℂ) * I)‖ ≤ 0.00000015776 := by
  have hl := lg_8
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.9481170720418 29.9481170936448 1.4678095 0.00000005775 0.1028048720166 0.9947015423179 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_9 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9740068580562:ℝ):ℂ) + (((-0.2265185212284):ℝ):ℂ) * I)‖ ≤ 0.00000013383 := by
  have hl := lg_9
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.644428355308755856 31.64442836971078466 (-0.2285018) 0.00000003382 0.9740068580562 (-0.2265185212284) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_10 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1742141652468):ℝ):ℂ) + (((-0.9847077864151):ℝ):ℂ) * I)‖ ≤ 0.00000013784 := by
  have hl := lg_10
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.161830498069038018 33.16183051967205242 (-1.745904) 0.00000003783 (-0.1742141652468) (-0.9847077864151) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_11 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997347874868):ℝ):ℂ) + (((-0.0230294171952):ℝ):ℂ) * I)‖ ≤ 0.0000001283 := by
  have hl := lg_11
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.534487707610912266 34.53448772921394107 (-3.1185612) 0.00000002829 (-0.9997347874868) (-0.0230294171952) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_12 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3341374881671):ℝ):ℂ) + ((0.9425243439823:ℝ):ℂ) * I)‖ ≤ 0.00000013756 := by
  have hl := lg_12
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.787625559015577928 35.78762558061859233 1.9114863 0.00000003755 (-0.3341374881671) 0.9425243439823 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_13 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7257232904754:ℝ):ℂ) + ((0.6879867045675:ℝ):ℂ) * I)‖ ≤ 0.00000011347 := by
  have hl := lg_13
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.9404006349298434 36.940400656532872204 0.7587112 0.00000001346 0.7257232904754 0.6879867045675 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_14 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.952762209064:ℝ):ℂ) + (((-0.3037172582838):ℝ):ℂ) * I)‖ ≤ 0.00000012843 := by
  have hl := lg_14
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.007703649887747644 38.007703671490776448 (-0.3085918) 0.00000002842 0.952762209064 (-0.3037172582838) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_15 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2653521301553:ℝ):ℂ) + (((-0.9641515684902):ℝ):ℂ) * I)‖ ≤ 0.00000015805 := by
  have hl := lg_15
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.001338985042815946 39.00133900664584475 (-1.3022272) 0.00000005804 0.2653521301553 (-0.9641515684902) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_16 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6138391011798):ℝ):ℂ) + (((-0.7894311609314):ℝ):ℂ) * I)‖ ≤ 0.00000014846 := by
  have hl := lg_16
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.9308227627224 39.9308227915264 (-2.2317109) 0.00000004845 (-0.6138391011798) (-0.7894311609314) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_17 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993242081668):ℝ):ℂ) + (((-0.0367576709036):ℝ):ℂ) * I)‖ ≤ 0.00000015186 := by
  have hl := lg_17
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.803938566122682468 40.80393859492669687 (-3.1048267) 0.00000005185 (-0.9993242081668) (-0.0367576709036) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_18 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7063771022154):ℝ):ℂ) + ((0.7078357079443:ℝ):ℂ) * I)‖ ≤ 0.00000011735 := by
  have hl := lg_18
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.627134045989355856 41.62713406759238466 2.3551631 0.00000001734 (-0.7063771022154) 0.7078357079443 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_19 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.005690642491):ℝ):ℂ) + ((0.9999838081628:ℝ):ℂ) * I)‖ ≤ 0.00000013808 := by
  have hl := lg_19
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.405810166723856406 42.405810188326899612 1.576487 0.00000003807 (-0.005690642491) 0.9999838081628 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_20 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6691284816733:ℝ):ℂ) + ((0.7431467385473:ℝ):ℂ) * I)‖ ≤ 0.00000016152 := by
  have hl := lg_20
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.144536188749638018 43.14453621755365242 0.8377609 0.00000006151 0.6691284816733 0.7431467385473 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_21 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9908898874485:ℝ):ℂ) + ((0.1346745371342:ℝ):ℂ) * I)‖ ≤ 0.00000011341 := by
  have hl := lg_21
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.847212136861525572 43.847212158464568778 0.135085 0.0000000134 0.9908898874485 0.1346745371342 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_22 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8603214951649:ℝ):ℂ) + (((-0.5097518268307):ℝ):ℂ) * I)‖ ≤ 0.00000015198 := by
  have hl := lg_22
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.517193398291512266 44.51719342709554107 (-0.5348963) 0.00000005197 0.8603214951649 (-0.5097518268307) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_23 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3854595686068:ℝ):ℂ) + (((-0.9227247265406):ℝ):ℂ) * I)‖ ≤ 0.0000001614 := by
  have hl := lg_23
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.157387682836649132 45.157387711640692338 (-1.1750905) 0.00000006139 0.3854595686068 (-0.9227247265406) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_24 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2155331438911):ℝ):ℂ) + (((-0.9764965252798):ℝ):ℂ) * I)‖ ≤ 0.00000012826 := by
  have hl := lg_24
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.770331249696177928 45.77033127850019233 (-1.7880341) 0.00000002825 (-0.2155331438911) (-0.9764965252798) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_25 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7209388796071):ℝ):ℂ) + (((-0.6929986521224):ℝ):ℂ) * I)‖ ≤ 0.0000001355 := by
  have hl := lg_25
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.358249614776876036 46.35824964358090484 (-2.3759525) 0.00000003549 (-0.7209388796071) (-0.6929986521224) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_26 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.979910628742):ℝ):ℂ) + (((-0.1994371062634):ℝ):ℂ) * I)‖ ≤ 0.00000012466 := by
  have hl := lg_26
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.9231063256104434 46.923106354414472204 (-2.9408092) 0.00000002465 (-0.979910628742) (-0.1994371062634) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_27 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9418330869033):ℝ):ℂ) + ((0.3360809965333:ℝ):ℂ) * I)‖ ≤ 0.00000012449 := by
  have hl := lg_27
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.466642532963133784 47.46664255456617699 2.7988399 0.00000002448 (-0.9418330869033) 0.3360809965333 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_28 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6474828422211):ℝ):ℂ) + ((0.7620800279582:ℝ):ℂ) * I)‖ ≤ 0.00000011688 := by
  have hl := lg_28
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.990409340568347644 47.990409369372376448 2.2750731 0.00000001687 (-0.6474828422211) 0.7620800279582 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_29 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1975828769184):ℝ):ℂ) + ((0.9802861861456:ℝ):ℂ) * I)‖ ≤ 0.00000012896 := by
  have hl := lg_29
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.495794528490258184 48.49579455729430139 1.7696879 0.00000002895 (-0.1975828769184) 0.9802861861456 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_30 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.285337478544:ℝ):ℂ) + ((0.9584271090376:ℝ):ℂ) * I)‖ ≤ 0.00000014711 := by
  have hl := lg_30
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.984044675723415946 48.98404470452744475 1.2814378 0.0000000471 0.285337478544 0.9584271090376 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_31 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6900785828453:ℝ):ℂ) + ((0.7237344468092:ℝ):ℂ) * I)‖ ≤ 0.00000015343 := by
  have hl := lg_31
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.456283704020117926 49.456283732824161132 0.8091987 0.00000005342 0.6900785828453 0.7237344468092 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_32 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9387008976416:ℝ):ℂ) + ((0.3447326859567:ℝ):ℂ) * I)‖ ≤ 0.00000013199 := by
  have hl := lg_32
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.913528453403 49.913528489408 0.351954 0.00000003198 0.9387008976416 0.3447326859567 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_33 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9958423946772:ℝ):ℂ) + (((-0.0910929468378):ℝ):ℂ) * I)‖ ≤ 0.00000015665 := by
  have hl := lg_33
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.356701885265290194 50.3567019140693334 (-0.0912194) 0.00000005664 0.9958423946772 (-0.0910929468378) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_34 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8672413187813:ℝ):ℂ) + (((-0.4978880346007):ℝ):ℂ) * I)‖ ≤ 0.00000013539 := by
  have hl := lg_34
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.786644256803282468 50.78664429280829687 (-0.5211618) 0.00000003538 0.8672413187813 (-0.4978880346007) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_35 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5908855162466:ℝ):ℂ) + (((-0.8067554193744):ℝ):ℂ) * I)‖ ≤ 0.00000013798 := by
  have hl := lg_35
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.204122766595585662 51.204122795399628868 (-0.9386403) 0.00000003797 0.5908855162466 (-0.8067554193744) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_36 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2245088854831:ℝ):ℂ) + (((-0.9744720418458):ℝ):ℂ) * I)‖ ≤ 0.00000012078 := by
  have hl := lg_36
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.609839736669955856 51.60983976547398466 (-1.3443573) 0.00000002077 0.2245088854831 (-0.9744720418458) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_37 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1673695472048):ℝ):ℂ) + (((-0.985894230974):ℝ):ℂ) * I)‖ ≤ 0.00000013431 := by
  have hl := lg_37
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.004439762927173684 52.00443979173121689 (-1.7389573) 0.0000000343 (-0.1673695472048) (-0.985894230974) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_38 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.524593079212):ℝ):ℂ) + (((-0.851353100209):ℝ):ℂ) * I)‖ ≤ 0.00000012879 := by
  have hl := lg_38
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.388515857404456406 52.388515886208499612 (-2.1230334) 0.00000002878 (-0.524593079212) (-0.851353100209) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_39 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7994241452168):ℝ):ℂ) + (((-0.6007670397045):ℝ):ℂ) * I)‖ ≤ 0.00000014487 := by
  have hl := lg_39
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.762614812584221328 52.762614841388264534 (-2.4971324) 0.00000004486 (-0.7994241452168) (-0.6007670397045) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p402_40 : ‖exp (-((((((14402:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9611015061737):ℝ):ℂ) + (((-0.2761953920574):ℝ):ℂ) * I)‖ ≤ 0.00000015801 := by
  have hl := lg_40
  refine (ecis_approx ((((14402:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.127241879430238018 53.12724191543525242 (-2.8617594) 0.000000058 (-0.9611015061737) (-0.2761953920574) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_2 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.832967653526):ℝ):ℂ) + ((0.5533216859254:ℝ):ℂ) * I)‖ ≤ 0.00000011795 := by
  have hl := lg_2
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.0111247250729 10.0111247322944 2.5552459 0.00000001794 (-0.832967653526) 0.5533216859254 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_3 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.987339507322):ℝ):ℂ) + ((0.158621237232:ℝ):ℂ) * I)‖ ≤ 0.00000014007 := by
  have hl := lg_3
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.867257281479112652 15.867257288700627095 2.9822986 0.00000004006 (-0.987339507322) 0.158621237232 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_4 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3876702303089:ℝ):ℂ) + (((-0.921798130033):ℝ):ℂ) * I)‖ ≤ 0.00000014307 := by
  have hl := lg_4
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.0222494501458 20.0222494645888 (-1.1726935) 0.00000004306 0.3876702303089 (-0.921798130033) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_5 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3115589241241):ℝ):ℂ) + ((0.950226834391:ℝ):ℂ) * I)‖ ≤ 0.00000014752 := by
  have hl := lg_5
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.245111761776920587 23.24511177621993503 1.8876295 0.00000004751 (-0.3115589241241) 0.950226834391 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_6 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7346533071523:ℝ):ℂ) + (((-0.6784427155554):ℝ):ℂ) * I)‖ ≤ 0.00000012218 := by
  have hl := lg_6
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.878382006552012652 25.878382020995027095 (-0.7456408) 0.00000002217 0.7346533071523 (-0.6784427155554) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_7 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.985660199384):ℝ):ℂ) + (((-0.168742321262):ℝ):ℂ) * I)‖ ≤ 0.00000015344 := by
  have hl := lg_7
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.104780275297099946 28.104780289740128832 (-2.9720391) 0.00000005343 (-0.985660199384) (-0.168742321262) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_8 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1871342315709:ℝ):ℂ) + ((0.9823343521298:ℝ):ℂ) * I)‖ ≤ 0.00000016069 := by
  have hl := lg_8
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.0333741752187 30.0333741968832 1.3825523 0.00000006068 0.1871342315709 0.9823343521298 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_9 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9496786396524:ℝ):ℂ) + (((-0.3132259270686):ℝ):ℂ) * I)‖ ≤ 0.00000014152 := by
  have hl := lg_9
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.734514562958225304 31.73451457740125419 (-0.318588) 0.00000004151 0.9496786396524 (-0.3132259270686) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_10 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2662626975536):ℝ):ℂ) + (((-0.9639005010322):ℝ):ℂ) * I)‖ ≤ 0.00000014906 := by
  have hl := lg_10
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.256236486849820587 33.25623650851433503 (-1.84031) 0.00000004905 (-0.2662626975536) (-0.9639005010322) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_11 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9971676289687):ℝ):ℂ) + ((0.0752111641657:ℝ):ℂ) * I)‖ ≤ 0.00000012933 := by
  have hl := lg_11
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.632801413763672119 34.632801435428201005 3.0663104 0.00000002932 (-0.9971676289687) 0.0752111641657 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_12 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2365453742258):ℝ):ℂ) + ((0.9716204433477:ℝ):ℂ) * I)‖ ≤ 0.00000011147 := by
  have hl := lg_12
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.889506731624912652 35.889506753289427095 1.8096051 0.00000001146 (-0.2365453742258) 0.9716204433477 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_13 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7939314086171:ℝ):ℂ) + ((0.6080073341756:ℝ):ℂ) * I)‖ ≤ 0.00000013716 := by
  have hl := lg_13
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.0455635585537931 37.045563580218321986 0.6535483 0.00000003715 0.7939314086171 0.6080073341756 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_14 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9143918493908:ℝ):ℂ) + (((-0.4048302678503):ℝ):ℂ) * I)‖ ≤ 0.00000014272 := by
  have hl := lg_14
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.115905000369999946 38.115905022034528832 (-0.4167932) 0.00000004271 0.9143918493908 (-0.4048302678503) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_15 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1568882854902:ℝ):ℂ) + (((-0.9876163556138):ℝ):ℂ) * I)‖ ≤ 0.00000012186 := by
  have hl := lg_15
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.112369043256033239 39.112369064920562125 (-1.4132572) 0.00000002185 0.1568882854902 (-0.9876163556138) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_16 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6994236565321):ℝ):ℂ) + (((-0.7147073167806):ℝ):ℂ) * I)‖ ≤ 0.0000001428 := by
  have hl := lg_16
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.0444989002916 40.0444989291776 (-2.3453871) 0.00000004279 (-0.6994236565321) (-0.7147073167806) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_17 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9968498043237):ℝ):ℂ) + ((0.07931246501:ℝ):ℂ) * I)‖ ≤ 0.00000013709 := by
  have hl := lg_17
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.920100313186356262 40.920100342072370705 3.0621968 0.00000003708 (-0.9968498043237) 0.07931246501 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_18 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6177368900357):ℝ):ℂ) + ((0.7863848515043:ℝ):ℂ) * I)‖ ≤ 0.00000015945 := by
  have hl := lg_18
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.745639288031125304 41.74563930969565419 2.2366579 0.00000005944 (-0.6177368900357) 0.7863848515043 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_19 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.114777808212:ℝ):ℂ) + ((0.9933911891808:ℝ):ℂ) * I)‖ ≤ 0.00000013626 := by
  have hl := lg_19
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.526532164837707129 42.526532186502250458 1.455765 0.00000003625 0.114777808212 0.9933911891808 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_20 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7551352647367:ℝ):ℂ) + ((0.6555690138735:ℝ):ℂ) * I)‖ ≤ 0.00000013835 := by
  have hl := lg_20
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.267361211922720587 43.26736124080873503 0.7149359 0.00000003834 0.7551352647367 0.6555690138735 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_21 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999473707656:ℝ):ℂ) + ((0.0102594200144:ℝ):ℂ) * I)‖ ≤ 0.0000001282 := by
  have hl := lg_21
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.972037556776212598 43.972037578440755927 0.0102596 0.00000002819 0.9999473707656 0.0102594200144 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_22 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7889924164096:ℝ):ℂ) + (((-0.6144029352536):ℝ):ℂ) * I)‖ ≤ 0.00000011748 := by
  have hl := lg_22
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.643926138836572119 44.643926167722601005 (-0.661629) 0.00000001747 0.7889924164096 (-0.6144029352536) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_23 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2639841181982:ℝ):ℂ) + (((-0.9645270267541):ℝ):ℂ) * I)‖ ≤ 0.00000012429 := by
  have hl := lg_23
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.285942945647113138 45.285942974533156467 (-1.3036458) 0.00000002428 0.2639841181982 (-0.9645270267541) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_24 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3405840097526):ℝ):ℂ) + (((-0.940214088545):ℝ):ℂ) * I)‖ ≤ 0.00000013534 := by
  have hl := lg_24
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.900631456697812652 45.900631485583827095 (-1.9183343) 0.00000003533 (-0.3405840097526) (-0.940214088545) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_25 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8058621285458):ℝ):ℂ) + (((-0.5921032255646):ℝ):ℂ) * I)‖ ≤ 0.00000012672 := by
  have hl := lg_25
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.490223523553841174 46.49022355243987006 (-2.5079264) 0.00000002671 (-0.8058621285458) (-0.5921032255646) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_26 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9977428249959):ℝ):ℂ) + (((-0.0671509838455):ℝ):ℂ) * I)‖ ≤ 0.00000016227 := by
  have hl := lg_26
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.0566882836266931 47.056688312512721986 (-3.0743911) 0.00000006226 (-0.9977428249959) (-0.0671509838455) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_27 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8879709561716):ℝ):ℂ) + ((0.4598995334767:ℝ):ℂ) * I)‖ ≤ 0.00000011301 := by
  have hl := lg_27
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.601771844437337956 47.601771866101881285 2.6637106 0.000000013 (-0.8879709561716) 0.4598995334767 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_28 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5376574668686):ℝ):ℂ) + ((0.8431633580229:ℝ):ℂ) * I)‖ ≤ 0.00000013201 := by
  have hl := lg_28
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.127029725442899946 48.127029754328928832 2.1384527 0.000000032 (-0.5376574668686) 0.8431633580229 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_29 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0607949608085):ℝ):ℂ) + ((0.9981502756299:ℝ):ℂ) * I)‖ ≤ 0.00000012894 := by
  have hl := lg_29
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.633853657477072556 48.633853686363115885 1.6316288 0.00000002893 (-0.0607949608085) 0.9981502756299 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_30 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.415786679938:ℝ):ℂ) + ((0.9094621689692:ℝ):ℂ) * I)‖ ≤ 0.00000013979 := by
  have hl := lg_30
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.123493768328933239 49.123493797214962125 1.1419887 0.00000003978 0.415786679938 0.9094621689692 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_31 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7848109551589:ℝ):ℂ) + ((0.6197352375511:ℝ):ℂ) * I)‖ ≤ 0.00000015083 := by
  have hl := lg_31
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.597077179361377809 49.597077208247421138 0.6684053 0.00000005082 0.7848109551589 0.6197352375511 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_32 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9780603395122:ℝ):ℂ) + ((0.2083217998033:ℝ):ℂ) * I)‖ ≤ 0.00000013209 := by
  have hl := lg_32
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.0556236253645 50.055623661472 0.2098588 0.00000003208 0.9780603395122 0.2083217998033 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_33 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9726129096089:ℝ):ℂ) + (((-0.2324309102981):ℝ):ℂ) * I)‖ ≤ 0.00000016221 := by
  have hl := lg_33
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.500058695242784771 50.5000587241288281 (-0.2345763) 0.0000000622 0.9726129096089 (-0.2324309102981) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_34 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7864583400841:ℝ):ℂ) + (((-0.6176433269389):ℝ):ℂ) * I)‖ ≤ 0.00000011919 := by
  have hl := lg_34
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.931225038259256262 50.931225074366770705 (-0.6657426) 0.00000001918 0.7864583400841 (-0.6176433269389) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_35 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4674347132503:ℝ):ℂ) + (((-0.8840275950719):ℝ):ℂ) * I)‖ ≤ 0.00000012038 := by
  have hl := lg_35
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.349892037074020533 51.349892065960063862 (-1.0844096) 0.00000002037 0.4674347132503 (-0.8840275950719) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_36 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0794309634197:ℝ):ℂ) + (((-0.9968403693923):ℝ):ℂ) * I)‖ ≤ 0.00000014435 := by
  have hl := lg_36
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.756764013104025304 51.75676404199005419 (-1.4912816) 0.00000004434 0.0794309634197 (-0.9968403693923) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_37 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3109654467506):ℝ):ℂ) + (((-0.9504212176321):ℝ):ℂ) * I)‖ ≤ 0.00000016015 := by
  have hl := lg_37
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.152487397302955806 52.152487426188999135 (-1.887005) 0.00000006014 (-0.3109654467506) (-0.9504212176321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_38 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6452710837146):ℝ):ℂ) + (((-0.7639536821728):ℝ):ℂ) * I)‖ ≤ 0.00000016137 := by
  have hl := lg_38
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.537656889910607129 52.537656918796650458 (-2.2721744) 0.00000006136 (-0.6452710837146) (-0.7639536821728) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_39 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8803227182337):ℝ):ℂ) + (((-0.4743752856812):ℝ):ℂ) * I)‖ ≤ 0.00000011742 := by
  have hl := lg_39
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.912820840032905752 52.912820868918949081 (-2.6473384) 0.00000001741 (-0.8803227182337) (-0.4743752856812) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p443_40 : ‖exp (-((((((14443:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9917438004842):ℝ):ℂ) + (((-0.1282350723238):ℝ):ℂ) * I)‖ ≤ 0.00000012046 := by
  have hl := lg_40
  refine (ecis_approx ((((14443:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.278485936995620587 53.27848597310313503 (-3.0130035) 0.00000002045 (-0.9917438004842) (-0.1282350723238) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_2 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8112731927354):ℝ):ℂ) + ((0.5846672615216:ℝ):ℂ) * I)‖ ≤ 0.00000011289 := by
  have hl := lg_2
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.0492478199894 10.0492478272384 2.5171228 0.00000001288 (-0.8112731927354) 0.5846672615216 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_3 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9759590266609):ℝ):ℂ) + ((0.2179540730944:ℝ):ℂ) * I)‖ ≤ 0.00000014307 := by
  have hl := lg_3
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.927680957341561672 15.92768096459057617 2.921875 0.00000004306 (-0.9759590266609) 0.2179540730944 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_4 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3163283933503:ℝ):ℂ) + (((-0.948649749676):ℝ):ℂ) * I)‖ ≤ 0.00000013295 := by
  have hl := lg_4
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.0984956399788 20.0984956544768 (-1.2489397) 0.00000003294 0.3163283933503 (-0.948649749676) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_5 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2263356700525):ℝ):ℂ) + ((0.9740493644887:ℝ):ℂ) * I)‖ ≤ 0.00000013273 := by
  have hl := lg_5
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.333630846932202082 23.33363086143021658 1.7991104 0.00000003272 (-0.2263356700525) 0.9740493644887 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_6 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6643387151223:ℝ):ℂ) + (((-0.7474316501123):ℝ):ℂ) * I)‖ ≤ 0.0000001514 := by
  have hl := lg_6
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.976928777330961672 25.97692879182897617 (-0.8441876) 0.00000005139 0.6643387151223 (-0.7474316501123) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_7 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9980457265972):ℝ):ℂ) + (((-0.0624878154041):ℝ):ℂ) * I)‖ ≤ 0.00000011926 := by
  have hl := lg_7
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.211805333466548156 28.211805347964577152 (-3.0790641) 0.00000001925 (-0.9980457265972) (-0.0624878154041) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_8 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.298015705685:ℝ):ℂ) + ((0.9545609667093:ℝ):ℂ) * I)‖ ≤ 0.00000014583 := by
  have hl := lg_8
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.1477434599682 30.1477434817152 1.2681831 0.00000004582 0.298015705685 0.9545609667093 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_9 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9049920044239:ℝ):ℂ) + (((-0.4254285744151):ℝ):ℂ) * I)‖ ≤ 0.00000012123 := by
  have hl := lg_9
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.855361914683123344 31.85536192918115234 (-0.4394354) 0.00000002122 0.9049920044239 (-0.4254285744151) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_10 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3858747062527):ℝ):ℂ) + (((-0.922551196992):ℝ):ℂ) * I)‖ ≤ 0.00000015279 := by
  have hl := lg_10
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.382878666921602082 33.38287868866861658 (-1.9669521) 0.00000005278 (-0.3858747062527) (-0.922551196992) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_11 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9786176683109):ℝ):ℂ) + ((0.2056877705502:ℝ):ℂ) * I)‖ ≤ 0.00000013241 := by
  have hl := lg_11
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.764685653724691434 34.76468567547172043 2.9344262 0.0000000324 (-0.9786176683109) 0.2056877705502 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_12 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1019613744145):ℝ):ℂ) + ((0.9947883584598:ℝ):ℂ) * I)‖ ≤ 0.00000014577 := by
  have hl := lg_12
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.026176597320361672 36.02617661906737617 1.6729352 0.00000004576 (-0.1019613744145) 0.9947883584598 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_13 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8715330577719:ℝ):ℂ) + ((0.4903367508261:ℝ):ℂ) * I)‖ ≤ 0.00000015186 := by
  have hl := lg_13
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.1866357731712866 37.186635794918315596 0.5124761 0.00000005185 0.8715330577719 0.4903367508261 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_14 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8462223233934:ℝ):ℂ) + (((-0.5328299723088):ℝ):ℂ) * I)‖ ≤ 0.00000013214 := by
  have hl := lg_14
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.261053153455948156 38.261053175202977152 (-0.5619413) 0.00000003213 0.8462223233934 (-0.5328299723088) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_15 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0085962209217:ℝ):ℂ) + (((-0.9999630518102):ℝ):ℂ) * I)‖ ≤ 0.00000013882 := by
  have hl := lg_15
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.261311804273763754 39.26131182602079275 (-1.5622) 0.00000003881 0.0085962209217 (-0.9999630518102) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_16 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7998727551278):ℝ):ℂ) + (((-0.6001696223195):ℝ):ℂ) * I)‖ ≤ 0.00000016313 := by
  have hl := lg_16
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.1969912799576 40.1969913089536 (-2.4978795) 0.00000006312 (-0.7998727551278) (-0.6001696223195) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_17 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.972462497095):ℝ):ℂ) + ((0.2330594161599:ℝ):ℂ) * I)‖ ≤ 0.00000012581 := by
  have hl := lg_17
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.075927047052260132 41.07592707604827463 2.9063701 0.0000000258 (-0.972462497095) 0.2330594161599 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_18 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4854615932502):ℝ):ℂ) + ((0.8742579948009:ℝ):ℂ) * I)‖ ≤ 0.0000001156 := by
  have hl := lg_18
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.904609734672523344 41.90460975641955234 2.0776874 0.00000001559 (-0.4854615932502) 0.8742579948009 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_19 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2734477026016:ℝ):ℂ) + ((0.9618868716964:ℝ):ℂ) * I)‖ ≤ 0.00000014162 := by
  have hl := lg_19
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.688476308648970294 42.688476330396013788 1.2938208 0.00000004161 0.2734477026016 0.9618868716964 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_20 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8524353392126:ℝ):ℂ) + ((0.5228326620072:ℝ):ℂ) * I)‖ ≤ 0.00000016336 := by
  have hl := lg_20
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.432126486911002082 43.43212651590701658 0.5501706 0.00000006335 0.8524353392126 0.5228326620072 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_21 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9876711945614:ℝ):ℂ) + (((-0.156542682466):ℝ):ℂ) * I)‖ ≤ 0.00000015946 := by
  have hl := lg_21
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.139486290808109828 44.139486312555153322 (-0.1571892) 0.00000005945 0.9876711945614 (-0.156542682466) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_22 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6736673800254:ℝ):ℂ) + (((-0.7390346819262):ℝ):ℂ) * I)‖ ≤ 0.00000015247 := by
  have hl := lg_22
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.813933473714091434 44.81393350271012043 (-0.8316363) 0.00000005246 0.6736673800254 (-0.7390346819262) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_23 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0945568513945:ℝ):ℂ) + (((-0.9955194633227):ℝ):ℂ) * I)‖ ≤ 0.00000012281 := by
  have hl := lg_23
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.458395127466028268 45.458395156462071762 (-1.476098) 0.0000000228 0.0945568513945 (-0.9955194633227) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_24 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4989016493838):ℝ):ℂ) + (((-0.8666586088166):ℝ):ℂ) * I)‖ ≤ 0.00000013296 := by
  have hl := lg_24
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.075424417309761672 46.07542444630577617 (-2.0931273) 0.00000003295 (-0.4989016493838) (-0.8666586088166) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_25 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8975443698175):ℝ):ℂ) + (((-0.4409241477797):ℝ):ℂ) * I)‖ ≤ 0.00000015641 := by
  have hl := lg_25
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.667261693864404164 46.66726172286043316 (-2.6849646) 0.0000000564 (-0.8975443698175) (-0.4409241477797) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_26 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9937352403261):ℝ):ℂ) + ((0.1117598840335:ℝ):ℂ) * I)‖ ≤ 0.00000016429 := by
  have hl := lg_26
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.2358835931606866 47.235883622156715596 3.0295988 0.00000006428 (-0.9937352403261) 0.1117598840335 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_27 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7905112252052):ℝ):ℂ) + ((0.6124475510432:ℝ):ℂ) * I)‖ ≤ 0.00000013635 := by
  have hl := lg_27
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.783042872024685016 47.78304289377172851 2.4824396 0.00000003634 (-0.7905112252052) 0.6124475510432 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_28 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3749892452907):ℝ):ℂ) + ((0.927029161307:ℝ):ℂ) * I)‖ ≤ 0.00000014502 := by
  have hl := lg_28
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.310300973445348156 48.310301002441377152 1.9551815 0.00000004501 (-0.3749892452907) 0.927029161307 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_29 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1240484600111:ℝ):ℂ) + ((0.9922761609395:ℝ):ℂ) * I)‖ ≤ 0.00000012938 := by
  have hl := lg_29
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.819054928069140616 48.81905495706518411 1.4464275 0.00000002937 0.1240484600111 0.9922761609395 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_30 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5776717755621:ℝ):ℂ) + ((0.8162691466171:ℝ):ℂ) * I)‖ ≤ 0.00000013319 := by
  have hl := lg_30
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.310559624263163754 49.31055965325919275 0.9549228 0.00000003318 0.5776717755621 0.8162691466171 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_31 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8872090928258:ℝ):ℂ) + ((0.4613675602025:ℝ):ℂ) * I)‖ ≤ 0.00000014713 := by
  have hl := lg_31
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.785946475550872774 49.785946504546916268 0.479536 0.00000004712 0.8872090928258 0.4613675602025 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_32 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.999814853416:ℝ):ℂ) + ((0.0192421123749:ℝ):ℂ) * I)‖ ≤ 0.0000001575 := by
  have hl := lg_32
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.246239099947 50.246239136192 0.0192433 0.00000005749 0.999814853416 0.0192421123749 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_33 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.910260221408:ℝ):ℂ) + (((-0.414036627996):ℝ):ℂ) * I)‖ ≤ 0.00000014639 := by
  have hl := lg_33
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.692366611066253106 50.6923666400622966 (-0.4268842) 0.00000004638 0.910260221408 (-0.414036627996) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_34 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6526705496666:ℝ):ℂ) + (((-0.7576418372806):ℝ):ℂ) * I)‖ ≤ 0.00000014586 := by
  have hl := lg_34
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.125174867041660132 51.12517490328667463 (-0.8596924) 0.00000004585 0.6526705496666 (-0.7576418372806) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_35 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.286759565459:ℝ):ℂ) + (((-0.9580025843482):ℝ):ℂ) * I)‖ ≤ 0.00000015197 := by
  have hl := lg_35
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.545436180398750238 51.545436209394793732 (-1.2799537) 0.00000005196 0.286759565459 (-0.9580025843482) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_36 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1173080438697):ℝ):ℂ) + (((-0.9930955758853):ℝ):ℂ) * I)‖ ≤ 0.00000012624 := by
  have hl := lg_36
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.953857554661923344 51.95385758365795234 (-1.6883751) 0.00000002623 (-0.1173080438697) (-0.9930955758853) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_37 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4923686778597):ℝ):ℂ) + (((-0.8703867445318):ℝ):ℂ) * I)‖ ≤ 0.00000015402 := by
  have hl := lg_37
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.351087882441200116 52.35108791143724361 (-2.0856054) 0.00000005401 (-0.4923686778597) (-0.8703867445318) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_38 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.784224549473):ℝ):ℂ) + (((-0.6204771196106):ℝ):ℂ) * I)‖ ≤ 0.00000012881 := by
  have hl := lg_38
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.737724128638370294 52.737724157634413788 (-2.4722417) 0.0000000288 (-0.784224549473) (-0.6204771196106) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_39 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9574514736798):ℝ):ℂ) + (((-0.2885943092363):ℝ):ℂ) * I)‖ ≤ 0.00000012694 := by
  have hl := lg_39
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.114316730512848272 53.114316759508891766 (-2.8488343) 0.00000002693 (-0.9574514736798) (-0.2885943092363) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p498_40 : ‖exp (-((((((14498:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9972410797542):ℝ):ℂ) + ((0.0742309122055:ℝ):ℂ) * I)‖ ≤ 0.00000015773 := by
  have hl := lg_40
  refine (ecis_approx ((((14498:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.481374306900402082 53.48137434314541658 3.0672934 0.00000005772 (-0.9972410797542) 0.0742309122055 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_2 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.788399794009):ℝ):ℂ) + ((0.615163201729:ℝ):ℂ) * I)‖ ≤ 0.00000010784 := by
  have hl := lg_2
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.0873709149059 10.0873709221824 2.4789997 0.00000000783 (-0.788399794009) 0.615163201729 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_3 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9610163647583):ℝ):ℂ) + ((0.2764914943179:ℝ):ℂ) * I)‖ ≤ 0.00000011896 := by
  have hl := lg_3
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.988104633204010692 15.988104640480525245 2.8614513 0.00000001895 (-0.9610163647583) 0.2764914943179 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_4 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2431484773789:ℝ):ℂ) + (((-0.9699890813552):ℝ):ℂ) * I)‖ ≤ 0.00000012284 := by
  have hl := lg_4
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.1747418298118 20.1747418443648 (-1.3251859) 0.00000002283 0.2431484773789 (-0.9699890813552) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_5 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1393400909009):ℝ):ℂ) + ((0.9902445854773:ℝ):ℂ) * I)‖ ≤ 0.00000011794 := by
  have hl := lg_5
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.422149932087483577 23.42214994664049813 1.7105913 0.00000001793 (-0.1393400909009) 0.9902445854773 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_6 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5875777169254:ℝ):ℂ) + (((-0.8091677369821):ℝ):ℂ) * I)‖ ≤ 0.00000013396 := by
  have hl := lg_6
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.075475548109910692 26.075475562662925245 (-0.9427343) 0.00000003395 0.5875777169254 (-0.8091677369821) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_7 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9990101914084):ℝ):ℂ) + ((0.0444818713348:ℝ):ℂ) * I)‖ ≤ 0.00000014428 := by
  have hl := lg_7
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.318830391635996366 28.318830406189025472 3.0970961 0.00000004427 (-0.9990101914084) 0.0444818713348 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_8 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4050033794719:ℝ):ℂ) + ((0.9143151877861:ℝ):ℂ) * I)‖ ≤ 0.00000013066 := by
  have hl := lg_8
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.2621127447177 30.2621127665472 1.1538138 0.00000003065 0.4050033794719 0.9143151877861 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_9 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8471049108213:ℝ):ℂ) + (((-0.5314256957116):ℝ):ℂ) * I)‖ ≤ 0.00000014508 := by
  have hl := lg_9
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.976209266408021384 31.97620928096105049 (-0.5602827) 0.00000004507 0.8471049108213 (-0.5314256957116) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_10 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.499306324537):ℝ):ℂ) + (((-0.8664255272504):ℝ):ℂ) * I)‖ ≤ 0.00000013294 := by
  have hl := lg_10
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.509520846993383577 33.50952086882289813 (-2.0935943) 0.00000003293 (-0.499306324537) (-0.8664255272504) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_11 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9430708020981):ℝ):ℂ) + ((0.3325920354486:ℝ):ℂ) * I)‖ ≤ 0.00000014941 := by
  have hl := lg_11
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.896569893685710749 34.896569915515239855 2.8025419 0.0000000494 (-0.9430708020981) 0.3325920354486 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_12 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0345240648447:ℝ):ℂ) + ((0.9994038667858:ℝ):ℂ) * I)‖ ≤ 0.00000014178 := by
  have hl := lg_12
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.162846463015810692 36.162846484845325245 1.5362654 0.00000004177 0.0345240648447 0.9994038667858 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_13 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.931818791382:ℝ):ℂ) + ((0.3629238763534:ℝ):ℂ) * I)‖ ≤ 0.0000001553 := by
  have hl := lg_13
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.3277079877887801 37.327708009618309206 0.3714038 0.00000005529 0.931818791382 0.3629238763534 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_14 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7602558234592:ℝ):ℂ) + (((-0.6496238010544):ℝ):ℂ) * I)‖ ≤ 0.00000013655 := by
  have hl := lg_14
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.406201306541896366 38.406201328371425472 (-0.7070895) 0.00000003654 0.7602558234592 (-0.6496238010544) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_15 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.139886090555):ℝ):ℂ) + (((-0.9901676028171):ℝ):ℂ) * I)‖ ≤ 0.00000014406 := by
  have hl := lg_15
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.410254565291494269 39.410254587121023375 (-1.7111427) 0.00000004405 (-0.139886090555) (-0.9901676028171) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_16 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8817576358697):ℝ):ℂ) + (((-0.4717027363581):ℝ):ℂ) * I)‖ ≤ 0.00000014567 := by
  have hl := lg_16
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.3494836596236 40.3494836887296 (-2.6503718) 0.00000004566 (-0.8817576358697) (-0.4717027363581) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_17 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9245096366914):ℝ):ℂ) + ((0.3811586697357:ℝ):ℂ) * I)‖ ≤ 0.00000015978 := by
  have hl := lg_17
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.231753780918164002 41.231753810024178555 2.7505434 0.00000005977 (-0.9245096366914) 0.3811586697357 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_18 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3409438047347):ℝ):ℂ) + ((0.9400836781962:ℝ):ℂ) * I)‖ ≤ 0.0000001529 := by
  have hl := lg_18
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.063580181313921384 42.06358020314345049 1.918717 0.00000005289 (-0.3409438047347) 0.9400836781962 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_19 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4249617472224:ℝ):ℂ) + ((0.9052113086996:ℝ):ℂ) * I)‖ ≤ 0.00000012405 := by
  have hl := lg_19
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.850420452460233459 42.850420474289777118 1.1318767 0.00000002404 0.4249617472224 0.9052113086996 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_20 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.926646104844:ℝ):ℂ) + ((0.3759348299604:ℝ):ℂ) * I)‖ ≤ 0.00000014076 := by
  have hl := lg_20
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.596891761899283577 43.59689179100529813 0.3854054 0.00000004075 0.926646104844 0.3759348299604 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_21 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9477662859974:ℝ):ℂ) + (((-0.3189656206032):ℝ):ℂ) * I)‖ ≤ 0.00000012543 := by
  have hl := lg_21
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.306935024840007058 44.306935046669550717 (-0.3246379) 0.00000002542 0.9477662859974 (-0.3189656206032) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_22 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5389184507526:ℝ):ℂ) + (((-0.8423579425864):ℝ):ℂ) * I)‖ ≤ 0.00000014168 := by
  have hl := lg_22
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.983940808591610749 44.983940837697639855 (-1.0016437) 0.00000004167 0.5389184507526 (-0.8423579425864) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_23 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.077675551242):ℝ):ℂ) + (((-0.996978690213):ℝ):ℂ) * I)‖ ≤ 0.00000014099 := by
  have hl := lg_23
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.630847309284943398 45.630847338390987057 (-1.6485502) 0.00000004098 (-0.077675551242) (-0.996978690213) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_24 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6420152426437):ℝ):ℂ) + (((-0.7666918730475):ℝ):ℂ) * I)‖ ≤ 0.00000015679 := by
  have hl := lg_24
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.250217377921710692 46.250217407027725245 (-2.2679202) 0.00000005678 (-0.6420152426437) (-0.7666918730475) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_25 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9611686760657):ℝ):ℂ) + (((-0.2759615478885):ℝ):ℂ) * I)‖ ≤ 0.00000014304 := by
  have hl := lg_25
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.844299864174967154 46.84429989328099626 (-2.8620027) 0.00000004303 (-0.9611686760657) (-0.2759615478885) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_26 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9579031568749):ℝ):ℂ) + ((0.287091521684:ℝ):ℂ) * I)‖ ≤ 0.00000015476 := by
  have hl := lg_26
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.4150789026946801 47.415078931800709206 2.8504035 0.00000005475 (-0.9579031568749) 0.287091521684 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_27 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6671469227558):ℝ):ℂ) + ((0.7449261597223:ℝ):ℂ) * I)‖ ≤ 0.00000015784 := by
  have hl := lg_27
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.964313899612032076 47.964313921441575735 2.3011685 0.00000005783 (-0.6671469227558) 0.7449261597223 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_28 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1997608772238):ℝ):ℂ) + ((0.9798446774514:ℝ):ℂ) * I)‖ ≤ 0.000000136 := by
  have hl := lg_28
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.493572221447796366 48.493572250553825472 1.7719102 0.00000003599 (-0.1997608772238) 0.9798446774514 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_29 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.304649225586:ℝ):ℂ) + ((0.9524646184241:ℝ):ℂ) * I)‖ ≤ 0.00000015879 := by
  have hl := lg_29
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.004256198661208676 49.004256227767252335 1.2612262 0.00000005878 0.304649225586 0.9524646184241 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_30 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.719400837802:ℝ):ℂ) + ((0.6945951587578:ℝ):ℂ) * I)‖ ≤ 0.00000015188 := by
  have hl := lg_30
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.497625480197394269 49.497625509303423375 0.767857 0.00000005187 0.719400837802 0.6945951587578 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_31 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.958053018214:ℝ):ℂ) + ((0.286591022698:ℝ):ℂ) * I)‖ ≤ 0.00000014342 := by
  have hl := lg_31
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.974815771740367739 49.974815800846411398 0.2906667 0.00000004341 0.958053018214 0.286591022698 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_32 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9853517041217:ℝ):ℂ) + (((-0.1705345102451):ℝ):ℂ) * I)‖ ≤ 0.00000015349 := by
  have hl := lg_32
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.4368545745295 50.436854610912 (-0.1713721) 0.00000005348 0.9853517041217 (-0.1705345102451) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_33 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8143476093075:ℝ):ℂ) + (((-0.5803774385822):ℝ):ℂ) * I)‖ ≤ 0.00000013056 := by
  have hl := lg_33
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.884674526889721441 50.8846745559957651 (-0.6191921) 0.00000003055 0.8143476093075 (-0.5803774385822) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_34 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4944083387908:ℝ):ℂ) + (((-0.8692297708513):ℝ):ℂ) * I)‖ ≤ 0.00000016163 := by
  have hl := lg_34
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.319124695824064002 51.319124732206578555 (-1.0536423) 0.00000006162 0.4944083387908 (-0.8692297708513) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_35 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0951542455627:ℝ):ℂ) + (((-0.9954625405063):ℝ):ℂ) * I)‖ ≤ 0.00000013373 := by
  have hl := lg_35
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.740980323723479943 51.740980352829523602 (-1.4754979) 0.00000003372 0.0951542455627 (-0.9954625405063) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_36 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3095049482353):ℝ):ℂ) + (((-0.9508978320598):ℝ):ℂ) * I)‖ ≤ 0.00000016123 := by
  have hl := lg_36
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.150951096219821384 52.15095112532585049 (-1.8854687) 0.00000006122 (-0.3095049482353) (-0.9508978320598) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_37 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6544156675001):ℝ):ℂ) + (((-0.7561349972809):ℝ):ℂ) * I)‖ ≤ 0.00000013926 := by
  have hl := lg_37
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.549688367579444426 52.549688396685488085 (-2.2842059) 0.00000003925 (-0.6544156675001) (-0.7561349972809) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_38 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8918924376218):ℝ):ℂ) + (((-0.4522475866221):ℝ):ℂ) * I)‖ ≤ 0.00000013905 := by
  have hl := lg_38
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.937791367366133459 52.937791396472177118 (-2.6723089) 0.00000003904 (-0.8918924376218) (-0.4522475866221) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_39 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9958384716501):ℝ):ℂ) + (((-0.0911358211131):ℝ):ℂ) * I)‖ ≤ 0.00000013646 := by
  have hl := lg_39
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.315812620992790792 53.315812650098834451 (-3.0503302) 0.00000003645 (-0.9958384716501) (-0.0911358211131) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p553_40 : ‖exp (-((((((14553:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9618288717462):ℝ):ℂ) + ((0.2736516421218:ℝ):ℂ) * I)‖ ≤ 0.00000014859 := by
  have hl := lg_40
  refine (ecis_approx ((((14553:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.684262676805183577 53.68426271318769813 2.8644051 0.00000004858 (-0.9618288717462) 0.2736516421218 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_2 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7558232261887):ℝ):ℂ) + ((0.654775725511:ℝ):ℂ) * I)‖ ≤ 0.00000010813 := by
  have hl := lg_2
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.1386638062481 10.1386638135616 2.4277068 0.00000000812 (-0.7558232261887) 0.654775725511 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_3 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9353890546815):ℝ):ℂ) + ((0.3536202994911:ℝ):ℂ) * I)‖ ≤ 0.00000012834 := by
  have hl := lg_3
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.069401942546214828 16.069401949859729455 2.780154 0.00000002833 (-0.9353890546815) 0.3536202994911 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_4 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1425375056171:ℝ):ℂ) + (((-0.9897894015862):ℝ):ℂ) * I)‖ ≤ 0.00000010906 := by
  have hl := lg_4
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.2773276124962 20.2773276271232 (-1.4277717) 0.00000000905 0.1425375056171 (-0.9897894015862) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_5 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0206950956803):ℝ):ℂ) + ((0.9997858335736:ℝ):ℂ) * I)‖ ≤ 0.00000012349 := by
  have hl := lg_5
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.541248337569135043 23.54124835219614967 1.5914929 0.00000002348 (-0.0206950956803) 0.9997858335736 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_6 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4754467911956:ℝ):ℂ) + (((-0.8797444792335):ℝ):ℂ) * I)‖ ≤ 0.00000013472 := by
  have hl := lg_6
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.208065748794314828 26.208065763421329455 (-1.0753245) 0.00000003471 0.4754467911956 (-0.8797444792335) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_7 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9822875701886):ℝ):ℂ) + ((0.1873796390041:ℝ):ℂ) * I)‖ ≤ 0.00000012137 := by
  have hl := lg_7
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.462827742627617594 28.462827757254646848 2.9530988 0.00000002136 (-0.9822875701886) 0.1873796390041 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_8 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5403569161971:ℝ):ℂ) + ((0.8414359174161:ℝ):ℂ) * I)‖ ≤ 0.00000011717 := by
  have hl := lg_8
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.4159914187443 30.4159914406848 0.9999351 0.00000001716 0.5403569161971 0.8414359174161 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_9 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7499053060443:ℝ):ℂ) + (((-0.6615451851284):ℝ):ℂ) * I)‖ ≤ 0.00000015082 := by
  have hl := lg_9
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.138803885092429656 32.13880389971945891 (-0.7228774) 0.00000005081 0.7499053060443 (-0.6615451851284) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_10 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6389936550462):ℝ):ℂ) + (((-0.7692120051034):ℝ):ℂ) * I)‖ ≤ 0.00000012987 := by
  have hl := lg_10
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.679912143817235043 33.67991216575774967 (-2.2639856) 0.00000002986 (-0.6389936550462) (-0.7692120051034) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_11 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8695554333061):ℝ):ℂ) + ((0.4938353453533:ℝ):ℂ) * I)‖ ≤ 0.00000012269 := by
  have hl := lg_11
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.074014143815082191 35.074014165755611445 2.6250977 0.00000002268 (-0.8695554333061) 0.4938353453533 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_12 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2166816020665:ℝ):ℂ) + ((0.9762423281777:ℝ):ℂ) * I)‖ ≤ 0.00000013392 := by
  have hl := lg_12
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.346729555042414828 36.346729576982929455 1.3523823 0.00000003391 0.2166816020665 0.9762423281777 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_13 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9835564197188:ℝ):ℂ) + ((0.18060113297:ℝ):ℂ) * I)‖ ≤ 0.00000011906 := by
  have hl := lg_13
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.5175142401832259 37.517514262123755154 0.1815976 0.00000001905 0.9835564197188 0.18060113297 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_14 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6197441269041:ℝ):ℂ) + (((-0.7848039354947):ℝ):ℂ) * I)‖ ≤ 0.00000012775 := by
  have hl := lg_14
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.601491548875717594 38.601491570816246848 (-0.9023797) 0.00000002774 0.6197441269041 (-0.7848039354947) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_15 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3341865932319):ℝ):ℂ) + (((-0.94250693414):ℝ):ℂ) * I)‖ ≤ 0.00000015899 := by
  have hl := lg_15
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.610650280115349871 39.610650302055879125 (-1.9115384) 0.00000005898 (-0.3341865932319) (-0.94250693414) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_16 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9593661188993):ℝ):ℂ) + (((-0.2821642246584):ℝ):ℂ) * I)‖ ≤ 0.0000001181 := by
  have hl := lg_16
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.5546552249924 40.5546552542464 (-2.8555434) 0.00000001809 (-0.9593661188993) (-0.2821642246584) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_17 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8249361761388):ℝ):ℂ) + ((0.565225888683:ℝ):ℂ) * I)‖ ≤ 0.00000014731 := by
  have hl := lg_17
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.441411568301380118 41.441411597555394745 2.5408856 0.0000000473 (-0.8249361761388) 0.565225888683 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_18 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1336321191911):ℝ):ℂ) + ((0.9910310069417:ℝ):ℂ) * I)‖ ≤ 0.00000015893 := by
  have hl := lg_18
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.277467691340529656 42.27746771328105891 1.7048294 0.00000005892 (-0.1336321191911) 0.9910310069417 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_19 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6105921779878:ℝ):ℂ) + ((0.7919451951872:ℝ):ℂ) * I)‖ ≤ 0.00000011341 := by
  have hl := lg_19
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.068308936860842081 43.068308958801385962 0.9139882 0.0000000134 0.6105921779878 0.7919451951872 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_20 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9866275946106:ℝ):ℂ) + ((0.1629907652382:ℝ):ℂ) * I)‖ ≤ 0.00000012908 := by
  have hl := lg_20
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.818575950065335043 43.81857597931934967 0.1637212 0.00000002907 0.9866275946106 0.1629907652382 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_21 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8525598015053:ℝ):ℂ) + (((-0.5226296823347):ℝ):ℂ) * I)‖ ≤ 0.00000015687 := by
  have hl := lg_21
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.532229685173832422 44.532229707114376303 (-0.5499325) 0.00000005686 0.8525598015053 (-0.5226296823347) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_22 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3338788031637:ℝ):ℂ) + (((-0.9426160113206):ℝ):ℂ) * I)‖ ≤ 0.00000012908 := by
  have hl := lg_22
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.212677950063182191 45.212677979317211445 (-1.2303808) 0.00000002907 0.3338788031637 (-0.9426160113206) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_23 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3048494711182):ℝ):ℂ) + (((-0.9524005459664):ℝ):ℂ) * I)‖ ≤ 0.0000001602 := by
  have hl := lg_23
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.862873881186756482 45.862873910440800363 (-1.8805767) 0.00000006019 (-0.3048494711182) (-0.9524005459664) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_24 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8029927619681):ℝ):ℂ) + (((-0.5959887785658):ℝ):ℂ) * I)‖ ≤ 0.0000001403 := by
  have hl := lg_24
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.485393361290514828 46.485393390544529455 (-2.5030962) 0.00000004029 (-0.8029927619681) (-0.5959887785658) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_25 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9991434254477):ℝ):ℂ) + (((-0.0413813338757):ℝ):ℂ) * I)‖ ≤ 0.00000015415 := by
  have hl := lg_25
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.082496675138270086 47.08249670439229934 (-3.1001995) 0.00000005414 (-0.9991434254477) (-0.0413813338757) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_26 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8616480241476):ℝ):ℂ) + ((0.5075063373013:ℝ):ℂ) * I)‖ ≤ 0.00000011826 := by
  have hl := lg_26
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.6561780464313259 47.656178075685355154 2.6093044 0.00000001825 (-0.8616480241476) 0.5075063373013 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_27 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4675174088129):ℝ):ℂ) + ((0.8839838643616:ℝ):ℂ) * I)‖ ≤ 0.00000012981 := by
  have hl := lg_27
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.208205827638644484 48.208205849579188365 2.0572766 0.0000000298 (-0.4675174088129) 0.8839838643616 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_28 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0454535608511:ℝ):ℂ) + ((0.998966452793:ℝ):ℂ) * I)‖ ≤ 0.00000012696 := by
  have hl := lg_28
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.740155355123817594 48.740155384377846848 1.5253271 0.00000002695 0.0454535608511 0.998966452793 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_29 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5301266522468:ℝ):ℂ) + ((0.8479184704779:ℝ):ℂ) * I)‖ ≤ 0.00000016184 := by
  have hl := lg_29
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.253436090003263884 49.253436119257307765 1.0120464 0.00000006183 0.5301266522468 0.8479184704779 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_30 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8697166506677:ℝ):ℂ) + ((0.4935513626274:ℝ):ℂ) * I)‖ ≤ 0.0000001582 := by
  have hl := lg_30
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.749314086363449871 49.749314115617479125 0.5161684 0.00000005819 0.8697166506677 0.4935513626274 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_31 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9993320646382:ℝ):ℂ) + ((0.0365434616022:ℝ):ℂ) * I)‖ ≤ 0.00000013266 := by
  have hl := lg_31
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.228930824795324601 50.228930854049368482 0.0365516 0.00000003265 0.9993320646382 0.0365434616022 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_32 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9098654801502:ℝ):ℂ) + (((-0.4149033719206):ℝ):ℂ) * I)‖ ≤ 0.00000012621 := by
  have hl := lg_32
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.6933190312405 50.693319067808 (-0.4278366) 0.0000000262 0.9098654801502 (-0.4149033719206) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_33 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6387424375644:ℝ):ℂ) + (((-0.7694206251812):ℝ):ℂ) * I)‖ ≤ 0.00000015819 := by
  have hl := lg_33
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.143416086361297019 51.1434161156153409 (-0.8779336) 0.00000005818 0.6387424375644 (-0.7694206251812) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_34 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2534097376363:ℝ):ℂ) + (((-0.9673590361758):ℝ):ℂ) * I)‖ ≤ 0.0000001537 := by
  have hl := lg_34
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.580075374549480118 51.580075411116994745 (-1.3145929) 0.00000005369 0.2534097376363 (-0.9673590361758) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_35 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1670109664113):ℝ):ℂ) + (((-0.985955038071):ℝ):ℂ) * I)‖ ≤ 0.00000015203 := by
  have hl := lg_35
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.004076080196752637 52.004076109450796518 (-1.7385936) 0.00000005202 (-0.1670109664113) (-0.985955038071) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_36 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5479007811375):ℝ):ℂ) + (((-0.8365433246523):ℝ):ℂ) * I)‖ ≤ 0.00000015986 := by
  have hl := lg_36
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.416131497588629656 52.41613152684265891 (-2.1506491) 0.00000005985 (-0.5479007811375) (-0.8365433246523) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_37 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8308412142807):ℝ):ℂ) + (((-0.5565095476177):ℝ):ℂ) * I)‖ ≤ 0.00000016441 := by
  have hl := lg_37
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.816896293038173134 52.816896322292217015 (-2.5514139) 0.0000000644 (-0.8308412142807) (-0.5565095476177) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_38 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9800462380553):ℝ):ℂ) + (((-0.1987696429261):ℝ):ℂ) * I)‖ ≤ 0.00000011494 := by
  have hl := lg_38
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.206972743108942081 53.206972772362985962 (-2.9414903) 0.00000001493 (-0.9800462380553) (-0.1987696429261) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_39 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.983872136321):ℝ):ℂ) + ((0.1788731925697:ℝ):ℂ) * I)‖ ≤ 0.00000014738 := by
  have hl := lg_39
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.586916182729440728 53.586916211983484609 2.9617516 0.00000004737 (-0.983872136321) 0.1788731925697 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p627_40 : ‖exp (-((((((14627:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8524384481563):ℝ):ℂ) + ((0.5228275930261:ℝ):ℂ) * I)‖ ≤ 0.00000012828 := by
  have hl := lg_40
  refine (ecis_approx ((((14627:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.957239756313435043 53.95723979288094967 2.591428 0.00000002827 (-0.8524384481563) 0.5228275930261 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_2 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7212585524335):ℝ):ℂ) + ((0.6926659371689:ℝ):ℂ) * I)‖ ≤ 0.00000011678 := by
  have hl := lg_2
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.1899566975903 10.1899567049408 2.3764139 0.00000001677 (-0.7212585524335) 0.6926659371689 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_3 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9035829277984):ℝ):ℂ) + ((0.4284132263021:ℝ):ℂ) * I)‖ ≤ 0.00000013772 := by
  have hl := lg_3
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.150699251888418964 16.150699259238933665 2.6988567 0.00000003771 (-0.9035829277984) 0.4284132263021 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_4 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0404278061024:ℝ):ℂ) + (((-0.9991824620627):ℝ):ℂ) * I)‖ ≤ 0.00000012637 := by
  have hl := lg_4
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.3799133951806 20.3799134098816 (-1.5303575) 0.00000002636 0.0404278061024 (-0.9991824620627) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p701_5 : ‖exp (-((((((14701:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0982431008327:ℝ):ℂ) + ((0.9951624456031:ℝ):ℂ) * I)‖ ≤ 0.00000012905 := by
  have hl := lg_5
  refine (ecis_approx ((((14701:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.660346743050786509 23.66034675775180121 1.4723945 0.00000002904 0.0982431008327 0.9951624456031 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
