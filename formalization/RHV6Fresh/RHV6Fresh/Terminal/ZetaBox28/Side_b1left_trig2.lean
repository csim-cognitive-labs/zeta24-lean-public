/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
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
namespace H28

open Complex Set

lemma cs_b1left_v13p988_16 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4679212112117:ℝ):ℂ) + (((-0.883770185115):ℝ):ℂ) * I)‖ ≤ 0.00000011706 := by
  have hl := lg_16
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.7829710321456 38.7829710601216 (-1.0838592) 0.00000001705 0.4679212112117 (-0.883770185115) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_17 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3532848646865):ℝ):ℂ) + (((-0.9355157959014):ℝ):ℂ) * I)‖ ≤ 0.00000012703 := by
  have hl := lg_17
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.630988242113878792 39.63098827008989278 (-1.9318764) 0.00000002702 (-0.3532848646865) (-0.9355157959014) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_18 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9170473221284):ℝ):ℂ) + (((-0.3987783956519):ℝ):ℂ) * I)‖ ≤ 0.00000011646 := by
  have hl := lg_18
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.430520138543196064 40.43052015952522404 (-2.7314083) 0.00000001645 (-0.9170473221284) (-0.3987783956519) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_19 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9407001687848):ℝ):ℂ) + ((0.3392391372872:ℝ):ℂ) * I)‖ ≤ 0.0000001206 := by
  have hl := lg_19
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.186812429671802764 41.186812450653844728 2.7954847 0.00000002059 (-0.9407001687848) 0.3392391372872 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_20 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4857297053405):ℝ):ℂ) + ((0.8741090626141:ℝ):ℂ) * I)‖ ≤ 0.00000012234 := by
  have hl := lg_20
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.904303027928755492 41.90430305590476948 2.0779941 0.00000002233 (-0.4857297053405) 0.8741090626141 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_21 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1743828959023:ℝ):ℂ) + ((0.9846779197365:ℝ):ℂ) * I)‖ ≤ 0.00000011871 := by
  have hl := lg_21
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.586779847966880968 42.586779868948922932 1.3955173 0.0000000187 0.1743828959023 0.9846779197365 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_22 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7352266678091:ℝ):ℂ) + ((0.6778213237589:ℝ):ℂ) * I)‖ ≤ 0.00000012724 := by
  have hl := lg_22
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.237501823031639604 43.23750185100766758 0.7447953 0.00000002723 0.7352266678091 0.6778213237589 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_23 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9924445290975:ℝ):ℂ) + ((0.1226941590479:ℝ):ℂ) * I)‖ ≤ 0.00000015561 := by
  have hl := lg_23
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.859293077872451608 43.859293105848493572 0.1230041 0.0000000556 0.9924445290975 0.1226941590479 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_24 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.890515284559:ℝ):ℂ) + (((-0.4549533250421):ℝ):ℂ) * I)‖ ≤ 0.0000001421 := by
  have hl := lg_24
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.454616964362598032 44.45461699233861202 (-0.4723198) 0.00000004209 0.890515284559 (-0.4549533250421) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_25 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5033388234648:ℝ):ℂ) + (((-0.8640891324354):ℝ):ℂ) * I)‖ ≤ 0.00000012656 := by
  have hl := lg_25
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.025635023711910984 45.02563505168793896 (-1.0433379) 0.00000002655 0.5033388234648 (-0.8640891324354) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_26 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0211592939955):ℝ):ℂ) + (((-0.9997761170769):ℝ):ℂ) * I)‖ ≤ 0.00000013703 := by
  have hl := lg_26
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.5742543593000196 45.574254387276047576 (-1.5919572) 0.00000003702 (-0.0211592939955) (-0.9997761170769) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_27 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5218963501717):ℝ):ℂ) + (((-0.8530089094905):ℝ):ℂ) * I)‖ ≤ 0.0000001415 := by
  have hl := lg_27
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.102166070760194096 46.10216609174223606 (-2.1198689) 0.00000004149 (-0.5218963501717) (-0.8530089094905) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_28 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8712695949621):ℝ):ℂ) + (((-0.4908047399992):ℝ):ℂ) * I)‖ ≤ 0.00000015152 := by
  have hl := lg_28
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.610876673786282936 46.610876701762310912 (-2.6285795) 0.00000005151 (-0.8712695949621) (-0.4908047399992) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_29 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997545710203):ℝ):ℂ) + (((-0.0221539407226):ℝ):ℂ) * I)‖ ≤ 0.00000013304 := by
  have hl := lg_29
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.101734055306327696 47.10173408328236966 (-3.1194369) 0.00000003303 (-0.9997545710203) (-0.0221539407226) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_30 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8995495331123):ℝ):ℂ) + ((0.4368187694703:ℝ):ℂ) * I)‖ ≤ 0.0000001307 := by
  have hl := lg_30
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.575948960145753524 47.5759489881217815 2.6895335 0.00000003069 (-0.8995495331123) 0.4368187694703 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_31 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6131745775997):ℝ):ℂ) + ((0.7899474269673:ℝ):ℂ) * I)‖ ≤ 0.00000015566 := by
  have hl := lg_31
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.034613001793737644 48.034613029769779608 2.2308694 0.00000005565 (-0.6131745775997) 0.7899474269673 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_32 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2142972152811):ℝ):ℂ) + ((0.9767685004758:ℝ):ℂ) * I)‖ ≤ 0.00000016727 := by
  have hl := lg_32
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.478713790182 48.478713825152 1.7867686 0.00000006726 (-0.2142972152811) 0.9767685004758 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_33 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2128214194946:ℝ):ℂ) + ((0.9770911131539:ℝ):ℂ) * I)‖ ≤ 0.0000001258 := by
  have hl := lg_33
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.909147755248637636 48.9091477832246796 1.3563347 0.00000002579 0.2128214194946 0.9770911131539 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_34 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.590795882073:ℝ):ℂ) + ((0.8068210617762:ℝ):ℂ) * I)‖ ≤ 0.0000001573 := by
  have hl := lg_34
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.326731000150278792 49.32673103512029278 0.9387514 0.00000005729 0.590795882073 0.8068210617762 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_35 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8611474347405:ℝ):ℂ) + ((0.5083552848549:ℝ):ℂ) * I)‖ ≤ 0.00000014012 := by
  have hl := lg_35
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.732208669569438428 49.732208697545480392 0.5332738 0.00000004011 0.8611474347405 0.5083552848549 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_36 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9903246079926:ℝ):ℂ) + ((0.1387702086342:ℝ):ℂ) * I)‖ ≤ 0.00000016087 := by
  have hl := lg_36
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.126262896579596064 50.12626292455562404 0.1392195 0.00000006086 0.9903246079926 0.1387702086342 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_37 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9703703843531:ℝ):ℂ) + (((-0.2416222613305):ℝ):ℂ) * I)‖ ≤ 0.00000011808 := by
  have hl := lg_37
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.509519747522934696 50.50951977549897666 (-0.2440373) 0.00000001807 0.9703703843531 (-0.2416222613305) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_38 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8155758313644:ℝ):ℂ) + (((-0.5786502080656):ℝ):ℂ) * I)‖ ≤ 0.00000015826 := by
  have hl := lg_38
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.882555187708202764 50.882555215684244728 (-0.6170727) 0.00000005825 0.8155758313644 (-0.5786502080656) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_39 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5566755163589:ℝ):ℂ) + (((-0.8307300220207):ℝ):ℂ) * I)‖ ≤ 0.00000016207 := by
  have hl := lg_39
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.245900291517017632 51.245900319493059596 (-0.9804178) 0.00000006206 0.5566755163589 (-0.8307300220207) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v13p988_40 : ‖exp (-((((((13988:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2340419444479:ℝ):ℂ) + (((-0.9722265004818):ℝ):ℂ) * I)‖ ≤ 0.00000016351 := by
  have hl := lg_40
  refine (ecis_approx ((((13988:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.600045785965155492 51.60004582093516948 (-1.3345633) 0.0000000635 0.2340419444479 (-0.9722265004818) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_2 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9577393303415):ℝ):ℂ) + ((0.28763757559:ℝ):ℂ) * I)‖ ≤ 0.00000014093 := by
  have hl := lg_2
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.7165371734454 9.7165371804544 2.8498334 0.00000004092 (-0.9577393303415) 0.28763757559 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_3 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9530580458543):ℝ):ℂ) + (((-0.3027876500465):ℝ):ℂ) * I)‖ ≤ 0.00000015157 := by
  have hl := lg_3
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.400347058905642952 15.40034706591465697 (-2.8339764) 0.00000005156 (-0.9530580458543) (-0.3027876500465) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_4 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.834529309136:ℝ):ℂ) + (((-0.5509635488787):ℝ):ℂ) * I)‖ ≤ 0.00000013939 := by
  have hl := lg_4
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.4330743468908 19.4330743609088 (-0.5835184) 0.00000003938 0.834529309136 (-0.5509635488787) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_5 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8419268475976):ℝ):ℂ) + ((0.539591681946:ℝ):ℂ) * I)‖ ≤ 0.00000013453 := by
  have hl := lg_5
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.561100649213381762 22.56110066323139578 2.5716406 0.00000003452 (-0.8419268475976) 0.539591681946 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_6 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9998742804098:ℝ):ℂ) + ((0.0158563354826:ℝ):ℂ) * I)‖ ≤ 0.00000011767 := by
  have hl := lg_6
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.116884232351042952 25.11688424636905697 0.015857 0.00000001766 0.9998742804098 0.0158563354826 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_7 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5431891846067):ℝ):ℂ) + (((-0.8396103320696):ℝ):ℂ) * I)‖ ≤ 0.00000014748 := by
  have hl := lg_7
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.277768462169545596 27.277768476187573632 (-2.1450272) 0.00000004747 (-0.5431891846067) (-0.8396103320696) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_8 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6407837222481):ℝ):ℂ) + ((0.7677214477179:ℝ):ℂ) * I)‖ ≤ 0.00000011558 := by
  have hl := lg_8
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.1496115203362 29.1496115413632 2.266315 0.00000001557 (-0.6407837222481) 0.7677214477179 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_9 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8166393396846:ℝ):ℂ) + ((0.5771483248521:ℝ):ℂ) * I)‖ ≤ 0.0000001181 := by
  have hl := lg_9
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.800694117811285904 30.80069413182931394 0.6152324 0.00000001809 0.8166393396846 0.5771483248521 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_10 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6511396174723:ℝ):ℂ) + (((-0.7589579689008):ℝ):ℂ) * I)‖ ≤ 0.00000011325 := by
  have hl := lg_10
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.277637822658781762 32.27763784368579578 (-0.8617113) 0.00000001324 0.6511396174723 (-0.7589579689008) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_11 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5866962226062):ℝ):ℂ) + (((-0.8098071019499):ℝ):ℂ) * I)‖ ≤ 0.00000011276 := by
  have hl := lg_11
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.613695923155795594 33.61369594418282363 (-2.1977694) 0.00000001275 (-0.5866962226062) (-0.8098071019499) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_12 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9621798016359):ℝ):ℂ) + ((0.2724151777769:ℝ):ℂ) * I)‖ ≤ 0.0000001373 := by
  have hl := lg_12
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.833421405796442952 34.83342142682345697 2.8656904 0.00000003729 (-0.9621798016359) 0.2724151777769 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_13 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1719959664029):ℝ):ℂ) + ((0.9850976538092:ℝ):ℂ) * I)‖ ≤ 0.00000015993 := by
  have hl := lg_13
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.9554600819640706 35.955460102991098636 1.7436518 0.00000005992 (-0.1719959664029) 0.9850976538092 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_14 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.761737126415:ℝ):ℂ) + ((0.6478862170482:ℝ):ℂ) * I)‖ ≤ 0.00000011358 := by
  have hl := lg_14
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.994305635614945596 36.994305656641973632 0.7048062 0.00000001357 0.761737126415 0.6478862170482 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_15 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9657868277016:ℝ):ℂ) + (((-0.2593372388187):ℝ):ℂ) * I)‖ ≤ 0.00000013497 := by
  have hl := lg_15
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.961447708119024714 37.96144772914605275 (-0.2623359) 0.00000003496 0.9657868277016 (-0.2593372388187) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_16 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3928782436549:ℝ):ℂ) + (((-0.9195904988976):ℝ):ℂ) * I)‖ ≤ 0.00000014931 := by
  have hl := lg_16
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.8661486937816 38.8661487218176 (-1.1670369) 0.0000000493 0.3928782436549 (-0.9195904988976) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_17 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4314292669031):ℝ):ℂ) + (((-0.9021467661392):ℝ):ℂ) * I)‖ ≤ 0.00000012738 := by
  have hl := lg_17
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.715984642404371812 39.71598467044038583 (-2.0168728) 0.00000002737 (-0.4314292669031) (-0.9021467661392) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_18 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9481371570188):ℝ):ℂ) + (((-0.3178614970105):ℝ):ℂ) * I)‖ ≤ 0.00000015184 := by
  have hl := lg_18
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.517231291256685904 40.51723131228371394 (-2.8181195) 0.00000005183 (-0.9481371570188) (-0.3178614970105) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_19 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9071054043274):ℝ):ℂ) + ((0.420903534453:ℝ):ℂ) * I)‖ ≤ 0.00000015125 := by
  have hl := lg_19
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.275145599023400854 41.275145620050442908 2.7071515 0.00000005124 (-0.9071054043274) 0.420903534453 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_20 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4053171910134):ℝ):ℂ) + ((0.9141761179694:ℝ):ℂ) * I)‖ ≤ 0.00000015417 := by
  have hl := lg_20
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.994174996104181762 41.99417502414019578 1.9881221 0.00000005416 (-0.4053171910134) 0.9141761179694 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_21 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2634672867495:ℝ):ℂ) + ((0.9646683309889:ℝ):ℂ) * I)‖ ≤ 0.0000001292 := by
  have hl := lg_21
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.678115521075188548 42.678115542102230602 1.3041816 0.00000002919 0.2634672867495 0.9646683309889 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_22 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7948329989984:ℝ):ℂ) + ((0.606828232454:ℝ):ℂ) * I)‖ ≤ 0.00000015367 := by
  have hl := lg_22
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.330233096601195594 43.33023312463722363 0.652064 0.00000005366 0.7948329989984 0.606828232454 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_23 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9995812905745:ℝ):ℂ) + ((0.0289351608486:ℝ):ℂ) * I)‖ ≤ 0.00000014595 := by
  have hl := lg_23
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.953357904319132588 43.953357932355174642 0.0289392 0.00000004594 0.9995812905745 0.0289351608486 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_24 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8431606553229:ℝ):ℂ) + (((-0.5376617052715):ℝ):ℂ) * I)‖ ≤ 0.00000015704 := by
  have hl := lg_24
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.549958579241842952 44.54995860727785697 (-0.5676614) 0.00000005703 0.8431606553229 (-0.5376617052715) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_25 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4176815491309:ℝ):ℂ) + (((-0.9085934863929):ℝ):ℂ) * I)‖ ≤ 0.00000015185 := by
  have hl := lg_25
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.122201298426763524 45.12220132646279156 (-1.1399042) 0.00000005184 0.4176815491309 (-0.9085934863929) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_26 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1186237921483):ℝ):ℂ) + (((-0.9929392710211):ℝ):ℂ) * I)‖ ≤ 0.0000001332 := by
  have hl := lg_26
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.6719972554094706 45.671997283445498636 (-1.6897001) 0.00000003319 (-0.1186237921483) (-0.9929392710211) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_27 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6035513082355):ℝ):ℂ) + (((-0.7973241613766):ℝ):ℂ) * I)‖ ≤ 0.0000001475 := by
  have hl := lg_27
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.201041176716928856 46.20104119774397091 (-2.218744) 0.00000004749 (-0.6035513082355) (-0.7973241613766) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_28 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9159020232927):ℝ):ℂ) + (((-0.4014018978424):ℝ):ℂ) * I)‖ ≤ 0.00000014121 := by
  have hl := lg_28
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.710842809060345596 46.710842837096373632 (-2.7285457) 0.0000000412 (-0.9159020232927) (-0.4014018978424) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_29 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9968919126336):ℝ):ℂ) + ((0.0787814318906:ℝ):ℂ) * I)‖ ≤ 0.00000012728 := by
  have hl := lg_29
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.202752930174728456 47.20275295821077051 3.0627295 0.00000002727 (-0.9968919126336) 0.0787814318906 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_30 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8503769476308):ℝ):ℂ) + ((0.5261739701506:ℝ):ℂ) * I)‖ ≤ 0.00000015218 := by
  have hl := lg_30
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.677984881564424714 47.67798490960045275 2.5874976 0.00000005217 (-0.8503769476308) 0.5261739701506 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_31 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5286874357633):ℝ):ℂ) + ((0.8488165851693:ℝ):ℂ) * I)‖ ≤ 0.00000013955 := by
  have hl := lg_31
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.137632617897098534 48.137632645933140588 2.1278498 0.00000003954 (-0.5286874357633) 0.8488165851693 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_32 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1117662636447):ℝ):ℂ) + ((0.9937345230545:ℝ):ℂ) * I)‖ ≤ 0.00000014485 := by
  have hl := lg_32
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.582685867227 48.582685902272 1.6827966 0.00000004484 (-0.1117662636447) 0.9937345230545 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_33 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3139559728083:ℝ):ℂ) + ((0.9494375425156:ℝ):ℂ) * I)‖ ≤ 0.00000015268 := by
  have hl := lg_33
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.014042982061438546 49.0140430100974806 1.2514395 0.00000005267 0.3139559728083 0.9494375425156 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_34 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6726880859533:ℝ):ℂ) + ((0.7399261713283:ℝ):ℂ) * I)‖ ≤ 0.0000001416 := by
  have hl := lg_34
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.432521815849771812 49.43252185089478583 0.8329606 0.00000004159 0.6726880859533 0.7399261713283 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_35 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9103723505286:ℝ):ℂ) + ((0.4137900233126:ℝ):ℂ) * I)‖ ≤ 0.00000014607 := by
  have hl := lg_35
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.838869111382927358 49.838869139418969412 0.4266133 0.00000004606 0.9103723505286 0.4137900233126 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_36 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9994971532501:ℝ):ℂ) + ((0.0317086840612:ℝ):ℂ) * I)‖ ≤ 0.00000013532 := by
  have hl := lg_36
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.233768464702085904 50.23376849273811394 0.031714 0.00000003531 0.9994971532501 0.0317086840612 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_37 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9385592022521:ℝ):ℂ) + (((-0.3451182751867):ℝ):ℂ) * I)‖ ≤ 0.00000015549 := by
  have hl := lg_37
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.617847284871067956 50.61784731290711001 (-0.3523648) 0.00000005548 0.9385592022521 (-0.3451182751867) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_38 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7477029214964:ℝ):ℂ) + (((-0.6640333886076):ℝ):ℂ) * I)‖ ≤ 0.00000014308 := by
  have hl := lg_38
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.991682772468800854 50.991682800504842908 (-0.7262003) 0.00000004307 0.7477029214964 (-0.6640333886076) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_39 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4621974547413:ℝ):ℂ) + (((-0.8867770367069):ℝ):ℂ) * I)‖ ≤ 0.00000011658 := by
  have hl := lg_39
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.355807140869713552 51.355807168905755606 (-1.0903247) 0.00000001657 0.4621974547413 (-0.8867770367069) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p018_40 : ‖exp (-((((((14018:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1252369191248:ℝ):ℂ) + (((-0.9921268639081):ℝ):ℂ) * I)‖ ≤ 0.00000014717 := by
  have hl := lg_40
  refine (ecis_approx ((((14018:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.710712169549581762 51.71071220459459578 (-1.4452297) 0.00000004716 0.1252369191248 (-0.9921268639081) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_2 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9515514514242):ℝ):ℂ) + ((0.3074895690668:ℝ):ℂ) * I)‖ ≤ 0.00000012552 := by
  have hl := lg_2
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.7373315888544 9.7373315958784 2.829039 0.00000002551 (-0.9515514514242) 0.3074895690668 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_3 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9625180500125):ℝ):ℂ) + (((-0.2712176306184):ℝ):ℂ) * I)‖ ≤ 0.00000012024 := by
  have hl := lg_3
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.433305427557887872 15.43330543458190192 (-2.8669348) 0.00000002023 (-0.9625180500125) (-0.2712176306184) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_4 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8109003338995:ℝ):ℂ) + (((-0.5851842859148):ℝ):ℂ) * I)‖ ≤ 0.00000014384 := by
  have hl := lg_4
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.4746631777088 19.4746631917568 (-0.6251073) 0.00000004383 0.8109003338995 (-0.5851842859148) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_5 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8149025684894):ℝ):ℂ) + ((0.5795979673998:ℝ):ℂ) * I)‖ ≤ 0.00000014216 := by
  have hl := lg_5
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.609383786570808032 22.60938380061882208 2.5233574 0.00000004215 (-0.8149025684894) 0.5795979673998 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_6 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9992820400987:ℝ):ℂ) + (((-0.0378867303442):ℝ):ℂ) * I)‖ ≤ 0.00000011232 := by
  have hl := lg_6
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.170637016412287872 25.17063703046030192 (-0.0378958) 0.00000001231 0.9992820400987 (-0.0378867303442) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_7 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5912502274009):ℝ):ℂ) + (((-0.806488170147):ℝ):ℂ) * I)‖ ≤ 0.00000015197 := by
  have hl := lg_7
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.336145766625608256 27.336145780673636352 (-2.2034045) 0.00000005196 (-0.5912502274009) (-0.806488170147) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_8 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5916754063962):ℝ):ℂ) + ((0.8061762917964:ℝ):ℂ) * I)‖ ≤ 0.00000015175 := by
  have hl := lg_8
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.2119947665632 29.2119947876352 2.2039318 0.00000005174 (-0.5916754063962) 0.8061762917964 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_9 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.852881997298:ℝ):ℂ) + ((0.5221037240673:ℝ):ℂ) * I)‖ ≤ 0.00000013328 := by
  have hl := lg_9
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.866610855115775744 30.86661086916380384 0.5493157 0.00000003327 0.852881997298 0.5221037240673 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_10 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5972013983466:ℝ):ℂ) + (((-0.8020913226141):ℝ):ℂ) * I)‖ ≤ 0.00000016049 := by
  have hl := lg_10
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.346715375425208032 32.34671539649722208 (-0.9307889) 0.00000006048 0.5972013983466 (-0.8020913226141) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_11 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6433836062069):ℝ):ℂ) + (((-0.7655439473003):ℝ):ℂ) * I)‖ ≤ 0.0000001546 := by
  have hl := lg_11
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.685632781316351584 33.68563280238837968 (-2.2697063) 0.00000005459 (-0.6433836062069) (-0.7655439473003) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_12 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9392185012609):ℝ):ℂ) + ((0.3433199771518:ℝ):ℂ) * I)‖ ≤ 0.00000013783 := by
  have hl := lg_12
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.907968605266687872 34.90796862633870192 2.7911432 0.00000003782 (-0.9392185012609) 0.3433199771518 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_13 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0957600130617):ℝ):ℂ) + ((0.995404450411:ℝ):ℂ) * I)‖ ≤ 0.00000014067 := by
  have hl := lg_13
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.0324085626645216 36.032408583736549696 1.6667033 0.00000004066 (-0.0957600130617) 0.995404450411 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_14 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8105917120675:ℝ):ℂ) + ((0.585611711228:ℝ):ℂ) * I)‖ ≤ 0.00000013349 := by
  have hl := lg_14
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.073477355480008256 37.073477376552036352 0.6256345 0.00000003348 0.8105917120675 0.585611711228 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_15 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9415556187675:ℝ):ℂ) + (((-0.3368575615409):ℝ):ℂ) * I)‖ ≤ 0.00000012896 := by
  have hl := lg_15
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.042689214128695904 38.042689235200724 (-0.3435774) 0.00000002895 0.9415556187675 (-0.3368575615409) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_16 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3151187979419:ℝ):ℂ) + (((-0.9490522341703):ℝ):ℂ) * I)‖ ≤ 0.00000014045 := by
  have hl := lg_16
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.9493263554176 38.9493263835136 (-1.2502145) 0.00000004044 0.3151187979419 (-0.9490522341703) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_17 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5064587326654):ℝ):ℂ) + (((-0.8622642008691):ℝ):ℂ) * I)‖ ≤ 0.00000012773 := by
  have hl := lg_17
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.800981042694864832 39.80098107079087888 (-2.1018692) 0.00000002772 (-0.5064587326654) (-0.8622642008691) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_18 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9721025498691):ℝ):ℂ) + (((-0.2345562454014):ℝ):ℂ) * I)‖ ≤ 0.00000012198 := by
  have hl := lg_18
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.603942443970175744 40.60394246504220384 (-2.9048306) 0.00000002197 (-0.9721025498691) (-0.2345562454014) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_19 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8664373703419):ℝ):ℂ) + ((0.4992857730697:ℝ):ℂ) * I)‖ ≤ 0.0000001392 := by
  have hl := lg_19
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.363478768374998944 41.363478789447041088 2.6188184 0.00000003919 (-0.8664373703419) 0.4992857730697 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_20 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3216332368913):ℝ):ℂ) + ((0.9468643307913:ℝ):ℂ) * I)‖ ≤ 0.00000014213 := by
  have hl := lg_20
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.084046964279608032 42.08404699237562208 1.8982502 0.00000004212 (-0.3216332368913) 0.9468643307913 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_21 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3503553056577:ℝ):ℂ) + ((0.936616869268:ℝ):ℂ) * I)‖ ≤ 0.00000015609 := by
  have hl := lg_21
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.769451194183496128 42.769451215255538272 1.2128459 0.00000005608 0.3503553056577 0.936616869268 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_22 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8476093298381:ℝ):ℂ) + ((0.5306207911224:ℝ):ℂ) * I)‖ ≤ 0.00000014802 := by
  have hl := lg_22
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.422964370170751584 43.42296439826677968 0.5593328 0.00000004801 0.8476093298381 0.5306207911224 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_23 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9978800775479:ℝ):ℂ) + (((-0.0650795730855):ℝ):ℂ) * I)‖ ≤ 0.00000011951 := by
  have hl := lg_23
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.047422730765813568 44.047422758861855712 (-0.0651256) 0.0000000195 0.9978800775479 (-0.0650795730855) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_24 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7881474207337:ℝ):ℂ) + (((-0.6154865093492):ℝ):ℂ) * I)‖ ≤ 0.00000015615 := by
  have hl := lg_24
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.645300194121087872 44.64530022221710192 (-0.6630031) 0.00000005614 0.7881474207337 (-0.6154865093492) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_25 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3281324935456:ℝ):ℂ) + (((-0.9446317095459):ℝ):ℂ) * I)‖ ≤ 0.000000151 := by
  have hl := lg_25
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.218767573141616064 45.21876760123764416 (-1.2364704) 0.00000005099 0.3281324935456 (-0.9446317095459) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_26 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.214955899175):ℝ):ℂ) + (((-0.9766237563202):ℝ):ℂ) * I)‖ ≤ 0.00000012937 := by
  have hl := lg_26
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.7697401515189216 45.769740179614949696 (-1.787443) 0.00000002936 (-0.214955899175) (-0.9766237563202) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_27 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.679310581962):ℝ):ℂ) + (((-0.7338508930388):ℝ):ℂ) * I)‖ ≤ 0.0000001535 := by
  have hl := lg_27
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.299916282673663616 46.29991630374570576 (-2.3176191) 0.00000005349 (-0.679310581962) (-0.7338508930388) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_28 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9513892106941):ℝ):ℂ) + (((-0.3079911842372):ℝ):ℂ) * I)‖ ≤ 0.00000012219 := by
  have hl := lg_28
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.810808944334408256 46.810808972430436352 (-2.8285118) 0.00000002218 (-0.9513892106941) (-0.3079911842372) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_29 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9838648016931):ℝ):ℂ) + ((0.178913531177:ℝ):ℂ) * I)‖ ≤ 0.00000015241 := by
  have hl := lg_29
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.303771805043129216 47.30377183313917136 2.9617106 0.0000000524 (-0.9838648016931) 0.178913531177 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_30 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7923584292244):ℝ):ℂ) + ((0.6100558331748:ℝ):ℂ) * I)‖ ≤ 0.00000015447 := by
  have hl := lg_30
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.780020802983095904 47.780020831079124 2.4854616 0.00000005446 (-0.7923584292244) 0.6100558331748 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_31 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4385942747955):ℝ):ℂ) + ((0.898685185208:ℝ):ℂ) * I)‖ ≤ 0.00000012345 := by
  have hl := lg_31
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.240652234000459424 48.240652262096501568 2.0248302 0.00000002344 (-0.4385942747955) 0.898685185208 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_32 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0080280869674):ℝ):ℂ) + ((0.9999677743905:ℝ):ℂ) * I)‖ ≤ 0.00000012197 := by
  have hl := lg_32
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.686657944272 48.686657979392 1.5788245 0.00000002196 (-0.0080280869674) 0.9999677743905 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_33 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4116393250413:ℝ):ℂ) + ((0.9113468418114:ℝ):ℂ) * I)‖ ≤ 0.00000014858 := by
  have hl := lg_33
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.118938208874239456 49.1189382369702816 1.1465442 0.00000004857 0.4116393250413 0.9113468418114 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_34 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7470587898328:ℝ):ℂ) + ((0.6647579744039:ℝ):ℂ) * I)‖ ≤ 0.0000001259 := by
  have hl := lg_34
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.538312631549264832 49.53831266666927888 0.7271698 0.00000002589 0.7470587898328 0.6647579744039 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_35 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9492502331145:ℝ):ℂ) + ((0.314521851279:ℝ):ℂ) * I)‖ ≤ 0.00000012387 := by
  have hl := lg_35
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.945529553196416288 49.945529581292458432 0.3199529 0.00000002386 0.9492502331145 0.314521851279 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_36 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9971291913276:ℝ):ℂ) + (((-0.0757190583821):ℝ):ℂ) * I)‖ ≤ 0.00000012463 := by
  have hl := lg_36
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.341274032824575744 50.34127406092060384 (-0.0757916) 0.00000002462 0.9971291913276 (-0.0757190583821) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_37 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8957448930891:ℝ):ℂ) + (((-0.4445684272469):ℝ):ℂ) * I)‖ ≤ 0.00000013523 := by
  have hl := lg_37
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.726174822219201216 50.72617485031524336 (-0.4606924) 0.00000003522 0.8957448930891 (-0.4445684272469) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_38 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.670934575456:ℝ):ℂ) + (((-0.7415165510342):ℝ):ℂ) * I)‖ ≤ 0.0000001279 := by
  have hl := lg_38
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.100810357229398944 51.100810385325441088 (-0.8353279) 0.00000002789 0.670934575456 (-0.7415165510342) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_39 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3621419777204:ℝ):ℂ) + (((-0.9321229468116):ℝ):ℂ) * I)‖ ≤ 0.0000001609 := by
  have hl := lg_39
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.465713990222409472 51.465714018318451616 (-1.2002315) 0.00000006089 0.3621419777204 (-0.9321229468116) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p048_40 : ‖exp (-((((((14048:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.014899675451:ℝ):ℂ) + (((-0.9998889936744):ℝ):ℂ) * I)‖ ≤ 0.00000013083 := by
  have hl := lg_40
  refine (ecis_approx ((((14048:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.821378553134008032 51.82137858825402208 (-1.5558961) 0.00000003082 0.014899675451 (-0.9998889936744) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_2 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.944952129756):ℝ):ℂ) + ((0.3272086066699:ℝ):ℂ) * I)‖ ≤ 0.00000011011 := by
  have hl := lg_2
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.7581260042634 9.7581260113024 2.8082446 0.0000000101 (-0.944952129756) 0.3272086066699 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_3 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.970932607676):ℝ):ℂ) + (((-0.2393530260425):ℝ):ℂ) * I)‖ ≤ 0.00000011816 := by
  have hl := lg_3
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.466263796210132792 15.46626380324914687 (-2.8998932) 0.00000001815 (-0.970932607676) (-0.2393530260425) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_4 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.785869059752:ℝ):ℂ) + (((-0.6183929340836):ℝ):ℂ) * I)‖ ≤ 0.00000011303 := by
  have hl := lg_4
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.5162520085268 19.5162520226048 (-0.6666961) 0.00000001302 0.785869059752 (-0.6183929340836) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_5 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7859789644527):ℝ):ℂ) + ((0.6182532388865:ℝ):ℂ) * I)‖ ≤ 0.0000001093 := by
  have hl := lg_5
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.657666923928234302 22.65766693800624838 2.4750743 0.00000000929 (-0.7859789644527) 0.6182532388865 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_6 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9958032058622:ℝ):ℂ) + (((-0.0915203539903):ℝ):ℂ) * I)‖ ≤ 0.00000012826 := by
  have hl := lg_6
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.224389800473532792 25.22438981455154687 (-0.0916486) 0.00000002825 0.9958032058622 (-0.0915203539903) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_7 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6372969152909):ℝ):ℂ) + (((-0.7706183502521):ℝ):ℂ) * I)‖ ≤ 0.00000015646 := by
  have hl := lg_7
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.394523071081670916 27.394523085159699072 (-2.2617818) 0.00000005645 (-0.6372969152909) (-0.7706183502521) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_8 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5402651513764):ℝ):ℂ) + ((0.8414948402694:ℝ):ℂ) * I)‖ ≤ 0.00000012312 := by
  have hl := lg_8
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.2743780127902 29.2743780339072 2.1415485 0.00000002311 (-0.5402651513764) 0.8414948402694 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_9 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8854202610527:ℝ):ℂ) + ((0.4647913094255:ℝ):ℂ) * I)‖ ≤ 0.00000014349 := by
  have hl := lg_9
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.932527592420265584 30.93252760649829374 0.4833989 0.00000004348 0.8854202610527 0.4647913094255 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_10 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5404147215695:ℝ):ℂ) + (((-0.8413987929104):ℝ):ℂ) * I)‖ ≤ 0.00000011343 := by
  have hl := lg_10
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.415792928191634302 32.41579294930864838 (-0.9998664) 0.00000001342 0.5404147215695 (-0.8413987929104) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_11 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6967428964972):ℝ):ℂ) + (((-0.7173209436211):ℝ):ℂ) * I)‖ ≤ 0.00000012471 := by
  have hl := lg_11
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.757569639476907574 33.75756966059393573 (-2.3416431) 0.0000000247 (-0.6967428964972) (-0.7173209436211) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_12 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9110401127036):ℝ):ℂ) + ((0.4123177329621:ℝ):ℂ) * I)‖ ≤ 0.00000013836 := by
  have hl := lg_12
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.982515804736932792 34.98251582585394687 2.716596 0.00000003835 (-0.9110401127036) 0.4123177329621 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_13 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0189573375381):ℝ):ℂ) + ((0.9998202935294:ℝ):ℂ) * I)‖ ≤ 0.00000012142 := by
  have hl := lg_13
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.1093570433649726 36.109357064482000756 1.5897548 0.00000002141 (-0.0189573375381) 0.9998202935294 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_14 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8543680341746:ℝ):ℂ) + ((0.5196684156081:ℝ):ℂ) * I)‖ ≤ 0.0000001534 := by
  have hl := lg_14
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.152649075345070916 37.152649096462099072 0.5464628 0.00000005339 0.8543680341746 0.5196684156081 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_15 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9111133893074:ℝ):ℂ) + (((-0.4121557858683):ℝ):ℂ) * I)‖ ≤ 0.00000012295 := by
  have hl := lg_15
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.123930720138367094 38.12393074125539525 (-0.4248189) 0.00000002294 0.9111133893074 (-0.4121557858683) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_16 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.235180358151:ℝ):ℂ) + (((-0.9719517473311):ℝ):ℂ) * I)‖ ≤ 0.00000012604 := by
  have hl := lg_16
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.0325040170536 39.0325040452096 (-1.3333922) 0.00000002603 0.235180358151 (-0.9719517473311) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_17 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5778315462484):ℝ):ℂ) + (((-0.8161560537972):ℝ):ℂ) * I)‖ ≤ 0.00000012808 := by
  have hl := lg_17
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.885977442985357852 39.88597747114137193 (-2.1868656) 0.00000002807 (-0.5778315462484) (-0.8161560537972) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_18 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9887634770217):ℝ):ℂ) + (((-0.1494884146489):ℝ):ℂ) * I)‖ ≤ 0.00000014641 := by
  have hl := lg_18
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.690653596683665584 40.69065361780069374 (-2.9915418) 0.0000000464 (-0.9887634770217) (-0.1494884146489) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_19 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8190130912074):ℝ):ℂ) + ((0.5737748307252:ℝ):ℂ) * I)‖ ≤ 0.00000011255 := by
  have hl := lg_19
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.451811937726597034 41.451811958843639268 2.5304852 0.00000001254 (-0.8190130912074) 0.5737748307252 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_20 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.235353115369):ℝ):ℂ) + ((0.9719099295125:ℝ):ℂ) * I)‖ ≤ 0.00000011782 := by
  have hl := lg_20
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.173918932455034302 42.17391896061104838 1.8083782 0.00000001781 (-0.235353115369) 0.9719099295125 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_21 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4343225281986:ℝ):ℂ) + ((0.9007574265579:ℝ):ℂ) * I)‖ ≤ 0.00000013817 := by
  have hl := lg_21
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.860786867291803708 42.860786888408845942 1.1215103 0.00000003816 0.4343225281986 0.9007574265579 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_22 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8931022705597:ℝ):ℂ) + ((0.4498536810133:ℝ):ℂ) * I)‖ ≤ 0.00000012165 := by
  have hl := lg_22
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.515695643740307574 43.51569567189633573 0.4666015 0.00000002164 0.8931022705597 0.4498536810133 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_23 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9873559438415:ℝ):ℂ) + (((-0.1585188952802):ℝ):ℂ) * I)‖ ≤ 0.00000013513 := by
  have hl := lg_23
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.141487557212494548 44.141487585368536782 (-0.1591904) 0.00000003512 0.9873559438415 (-0.1585188952802) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_24 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7259753888566:ℝ):ℂ) + (((-0.6877206807815):ℝ):ℂ) * I)‖ ≤ 0.00000014127 := by
  have hl := lg_24
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.740641809000332792 44.74064183715634687 (-0.7583447) 0.00000004126 0.7259753888566 (-0.6877206807815) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_25 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2355258721288:ℝ):ℂ) + (((-0.9718680792978):ℝ):ℂ) * I)‖ ≤ 0.00000012577 := by
  have hl := lg_25
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.315333847856468604 45.31533387601249676 (-1.3330367) 0.00000002576 0.2355258721288 (-0.9718680792978) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_26 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3092360219555):ℝ):ℂ) + (((-0.9509853220336):ℝ):ℂ) * I)‖ ≤ 0.00000012554 := by
  have hl := lg_26
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.8674830476283726 45.867483075784400756 (-1.8851859) 0.00000002553 (-0.3092360219555) (-0.9509853220336) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_27 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7484341302682):ℝ):ℂ) + (((-0.6632091318855):ℝ):ℂ) * I)‖ ≤ 0.00000015951 := by
  have hl := lg_27
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.398791388630398376 46.39879140974744061 (-2.4164942) 0.0000000595 (-0.7484341302682) (-0.6632091318855) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_28 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9773768701555):ℝ):ℂ) + (((-0.2115052088635):ℝ):ℂ) * I)‖ ≤ 0.00000015752 := by
  have hl := lg_28
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.910775079608470916 46.910775107764499072 (-2.9284779) 0.00000005751 (-0.9773768701555) (-0.2115052088635) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_29 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9608060923124):ℝ):ℂ) + ((0.2772213064315:ℝ):ℂ) * I)‖ ≤ 0.00000015065 := by
  have hl := lg_29
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.404790679911529976 47.40479070806757221 2.8606918 0.00000005064 (-0.9608060923124) 0.2772213064315 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_30 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7260976172657):ℝ):ℂ) + ((0.6875916303829:ℝ):ℂ) * I)‖ ≤ 0.00000013305 := by
  have hl := lg_30
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.882056724401767094 47.88205675255779525 2.3834257 0.00000003304 (-0.7260976172657) 0.6875916303829 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_31 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3438504114864):ℝ):ℂ) + ((0.9390244376577:ℝ):ℂ) * I)‖ ≤ 0.00000012084 := by
  have hl := lg_31
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.343671850103820314 48.343671878259862548 1.9218106 0.00000002083 (-0.3438504114864) 0.9390244376577 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_32 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.095796796764:ℝ):ℂ) + ((0.9954009110553:ℝ):ℂ) * I)‖ ≤ 0.00000013613 := by
  have hl := lg_32
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.790630021317 48.790630056512 1.4748524 0.00000003612 0.095796796764 0.9954009110553 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_33 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5047974650494:ℝ):ℂ) + ((0.8632378115442:ℝ):ℂ) * I)‖ ≤ 0.00000012176 := by
  have hl := lg_33
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.223833435687040366 49.2238334638430826 1.041649 0.00000002175 0.5047974650494 0.8632378115442 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_34 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8130764355779:ℝ):ℂ) + ((0.5821569461133:ℝ):ℂ) * I)‖ ≤ 0.00000012502 := by
  have hl := lg_34
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.644103447248757852 49.64410348244377193 0.621379 0.00000002501 0.8130764355779 0.5821569461133 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_35 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9773392817171:ℝ):ℂ) + ((0.2116788331712:ℝ):ℂ) * I)‖ ≤ 0.00000016244 := by
  have hl := lg_35
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.052189995009905218 50.052190023165947452 0.2132924 0.00000006243 0.9773392817171 0.2116788331712 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_36 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.983248049611:ℝ):ℂ) + (((-0.1822725238103):ℝ):ℂ) * I)‖ ≤ 0.0000001565 := by
  have hl := lg_36
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.448779600947065584 50.44877962910309374 (-0.1832972) 0.00000005649 0.983248049611 (-0.1822725238103) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_37 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8424294640852:ℝ):ℂ) + (((-0.5388066425361):ℝ):ℂ) * I)‖ ≤ 0.0000001303 := by
  have hl := lg_37
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.834502359567334476 50.83450238772337671 (-0.5690199) 0.00000003029 0.8424294640852 (-0.5388066425361) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_38 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5861841077463:ℝ):ℂ) + (((-0.8101778766578):ℝ):ℂ) * I)‖ ≤ 0.00000011546 := by
  have hl := lg_38
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.209937941989997034 51.209937970146039268 (-0.9444555) 0.00000001545 0.5861841077463 (-0.8101778766578) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_39 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2577163100663:ℝ):ℂ) + (((-0.9662206288037):ℝ):ℂ) * I)‖ ≤ 0.00000011788 := by
  have hl := lg_39
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.575620839575105392 51.575620867731147626 (-1.3101384) 0.00000001787 0.2577163100663 (-0.9662206288037) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p078_40 : ‖exp (-((((((14078:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0956198591664):ℝ):ℂ) + (((-0.995417923554):ℝ):ℂ) * I)‖ ≤ 0.00000012073 := by
  have hl := lg_40
  refine (ecis_approx ((((14078:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.932044936718434302 51.93204497191344838 (-1.6665625) 0.00000002072 (-0.0956198591664) (-0.995417923554) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_2 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9352728753381):ℝ):ℂ) + ((0.3539274621829:ℝ):ℂ) * I)‖ ≤ 0.00000013137 := by
  have hl := lg_2
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.7865450386557 9.7865450457152 2.7798256 0.00000003136 (-0.9352728753381) 0.3539274621829 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_3 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9807253779098):ℝ):ℂ) + (((-0.1953912300862):ℝ):ℂ) * I)‖ ≤ 0.00000011434 := by
  have hl := lg_3
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.511306900034867516 15.511306907094381635 (-2.9449363) 0.00000001433 (-0.9807253779098) (-0.1953912300862) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_4 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7494706414485:ℝ):ℂ) + (((-0.6620375802073):ℝ):ℂ) * I)‖ ≤ 0.00000014424 := by
  have hl := lg_4
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.5730900773114 19.5730900914304 (-0.7235342) 0.00000004423 0.7494706414485 (-0.6620375802073) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_5 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7435013212006):ℝ):ℂ) + ((0.6687344654949:ℝ):ℂ) * I)‖ ≤ 0.00000015042 := by
  have hl := lg_5
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.723653878316716871 22.72365389243573099 2.4090873 0.00000005041 (-0.7435013212006) 0.6687344654949 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_6 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9864001665693:ℝ):ℂ) + (((-0.1643615264958):ℝ):ℂ) * I)‖ ≤ 0.00000012411 := by
  have hl := lg_6
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.297851938690567516 25.297851952809581635 (-0.1651107) 0.0000000241 0.9864001665693 (-0.1643615264958) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_7 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6966862977061):ℝ):ℂ) + (((-0.7173759144029):ℝ):ℂ) * I)‖ ≤ 0.00000014156 := by
  have hl := lg_7
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.474305387171623218 27.474305401290651456 (-2.3415642) 0.00000004155 (-0.6966862977061) (-0.7173759144029) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_8 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.46664628116):ℝ):ℂ) + ((0.8844440334326:ℝ):ℂ) * I)‖ ≤ 0.00000011995 := by
  have hl := lg_8
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.3596351159671 29.3596351371456 2.0562914 0.00000001994 (-0.46664628116) 0.8844440334326 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_9 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9236445370353:ℝ):ℂ) + ((0.3832502696734:ℝ):ℂ) * I)‖ ≤ 0.00000013584 := by
  have hl := lg_9
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.022613800069735032 31.02261381418876327 0.3933127 0.00000003583 0.9236445370353 0.3832502696734 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_10 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4586931326109:ℝ):ℂ) + (((-0.8885947389534):ℝ):ℂ) * I)‖ ≤ 0.00000011894 := by
  have hl := lg_10
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.510198916972416871 32.51019893815093099 (-1.0942724) 0.00000001893 0.4586931326109 (-0.8885947389534) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_11 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7637873185665):ℝ):ℂ) + (((-0.6454679945277):ℝ):ℂ) * I)‖ ≤ 0.00000013093 := by
  have hl := lg_11
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.855883345629667427 33.855883366808195665 (-2.4399568) 0.00000003092 (-0.7637873185665) (-0.6454679945277) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_12 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8643812620879):ℝ):ℂ) + ((0.5028369851828:ℝ):ℂ) * I)‖ ≤ 0.00000015546 := by
  have hl := lg_12
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.084396977346267516 35.084396998524781635 2.6147149 0.00000005545 (-0.8643812620879) 0.5028369851828 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_13 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0860976993562:ℝ):ℂ) + ((0.9962866987798:ℝ):ℂ) * I)‖ ≤ 0.0000001451 := by
  have hl := lg_13
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.2145199669889223 36.214519988167450538 1.4845919 0.00000004509 0.0860976993562 0.9962866987798 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_14 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9054908337912:ℝ):ℂ) + ((0.424365820867:ℝ):ℂ) * I)‖ ≤ 0.00000011727 := by
  have hl := lg_14
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.260850425827323218 37.260850447005851456 0.4382614 0.00000001726 0.9054908337912 0.424365820867 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_15 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8598355153002:ℝ):ℂ) + (((-0.5105711376767):ℝ):ℂ) * I)‖ ≤ 0.00000015647 := by
  have hl := lg_15
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.234960778351584387 38.234960799530112625 (-0.5358489) 0.00000005646 0.8598355153002 (-0.5105711376767) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_16 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.123412584022:ℝ):ℂ) + (((-0.9923554474607):ℝ):ℂ) * I)‖ ≤ 0.0000001398 := by
  have hl := lg_16
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.1461801546228 39.1461801828608 (-1.4470683) 0.00000003979 0.123412584022 (-0.9923554474607) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_17 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6685305125307):ℝ):ℂ) + (((-0.7436847139725):ℝ):ℂ) * I)‖ ≤ 0.00000015304 := by
  have hl := lg_17
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.002139190049031646 40.002139218287045765 (-2.3030274) 0.00000005303 (-0.6685305125307) (-0.7436847139725) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_18 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9995024768321):ℝ):ℂ) + (((-0.0315404215777):ℝ):ℂ) * I)‖ ≤ 0.00000011684 := by
  have hl := lg_18
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.809158838725435032 40.80915885990396327 (-3.110047) 0.00000001683 (-0.9995024768321) (-0.0315404215777) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_19 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7439531489605):ℝ):ℂ) + ((0.6682317802375:ℝ):ℂ) * I)‖ ≤ 0.00000011443 := by
  have hl := lg_19
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.572533935840447757 41.572533957018990114 2.4097632 0.00000001442 (-0.7439531489605) 0.6682317802375 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_20 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1145051641148):ℝ):ℂ) + ((0.9934226529482:ℝ):ℂ) * I)‖ ≤ 0.00000013362 := by
  have hl := lg_20
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.296743955628116871 42.29674398386613099 1.6855532 0.00000003361 (-0.1145051641148) 0.9934226529482 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_21 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5430888922922:ℝ):ℂ) + ((0.8396752080828:ℝ):ℂ) * I)‖ ≤ 0.00000015814 := by
  have hl := lg_21
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.985612287206490734 42.985612308385033091 0.9966849 0.00000005813 0.5430888922922 0.8396752080828 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_22 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9427984109207:ℝ):ℂ) + ((0.3333633998588:ℝ):ℂ) * I)‖ ≤ 0.00000016228 := by
  have hl := lg_22
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.642428384285367427 43.642428412523395665 0.3398688 0.00000006227 0.9427984109207 0.3333633998588 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_23 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9588860622341:ℝ):ℂ) + (((-0.2837913311804):ℝ):ℂ) * I)‖ ≤ 0.00000013025 := by
  have hl := lg_23
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.270042820022958554 44.270042848261000911 (-0.2877457) 0.00000003024 0.9588860622341 (-0.2837913311804) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_24 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6304644582832:ℝ):ℂ) + (((-0.7762181180839):ℝ):ℂ) * I)‖ ≤ 0.00000013427 := by
  have hl := lg_24
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.870942016001967516 44.870942044239981635 (-0.8886449) 0.00000003426 0.6304644582832 (-0.7762181180839) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_25 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1055885358501:ℝ):ℂ) + (((-0.9944099059729):ℝ):ℂ) * I)‖ ≤ 0.00000013463 := by
  have hl := lg_25
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.447307756633433742 45.44730778487146198 (-1.4650106) 0.00000003462 0.1055885358501 (-0.9944099059729) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_26 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4331381494981):ℝ):ℂ) + (((-0.9013275450386):ℝ):ℂ) * I)‖ ≤ 0.00000014463 := by
  have hl := lg_26
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.0010650056446223 46.001065033882650538 (-2.0187679) 0.00000004462 (-0.4331381494981) (-0.9013275450386) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_27 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8309578960642):ℝ):ℂ) + (((-0.5563353079803):ℝ):ℂ) * I)‖ ≤ 0.00000015017 := by
  have hl := lg_27
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.533920700104602548 46.533920721283144905 (-2.5516236) 0.00000005016 (-0.8309578960642) (-0.5563353079803) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_28 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9970757330275):ℝ):ℂ) + (((-0.0764197755044):ℝ):ℂ) * I)‖ ≤ 0.00000014248 := by
  have hl := lg_28
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.047395464483023218 47.047395492721051456 (-3.0650983) 0.00000004247 (-0.9970757330275) (-0.0764197755044) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_29 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9135124954665):ℝ):ℂ) + ((0.4068106690995:ℝ):ℂ) * I)‖ ≤ 0.00000014855 := by
  have hl := lg_29
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.542849808898344348 47.542849837136386705 2.7226326 0.00000004854 (-0.9135124954665) 0.4068106690995 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_30 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6234756095086):ℝ):ℂ) + ((0.7818428002698:ℝ):ℂ) * I)‖ ≤ 0.00000014044 := by
  have hl := lg_30
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.021505817007284387 48.021505845245312625 2.2439766 0.00000004043 (-0.6234756095086) 0.7818428002698 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_31 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2086758177839):ℝ):ℂ) + ((0.9779848685288:ℝ):ℂ) * I)‖ ≤ 0.00000013201 := by
  have hl := lg_31
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.484465325445080197 48.484465353683122554 1.7810171 0.000000032 (-0.2086758177839) 0.9779848685288 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_32 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2357975000538:ℝ):ℂ) + ((0.9718022118561:ℝ):ℂ) * I)‖ ≤ 0.00000016417 := by
  have hl := lg_32
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.9327251932785 48.932725228576 1.3327572 0.00000006416 0.2357975000538 0.9718022118561 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_33 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.622946826829:ℝ):ℂ) + ((0.7822641823219:ℝ):ℂ) * I)‖ ≤ 0.00000011648 := by
  have hl := lg_33
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.367190245664534943 49.3671902739025773 0.8982922 0.00000001647 0.622946826829 0.7822641823219 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_34 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8884688982967:ℝ):ℂ) + ((0.4589368330821:ℝ):ℂ) * I)‖ ≤ 0.00000012875 := by
  have hl := lg_34
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.788684228704731646 49.788684264002245765 0.4767982 0.00000002874 0.8884688982967 0.4589368330821 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_35 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9977211747646:ℝ):ℂ) + ((0.0674719010128:ℝ):ℂ) * I)‖ ≤ 0.0000001363 := by
  have hl := lg_35
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.197959265488340089 50.197959293726382446 0.0675232 0.00000003629 0.9977211747646 0.0674719010128 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_36 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.945970577216:ℝ):ℂ) + (((-0.3242524742261):ℝ):ℂ) * I)‖ ≤ 0.0000001482 := by
  have hl := lg_36
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.595703877381135032 50.59570390561916327 (-0.3302214) 0.00000004819 0.945970577216 (-0.3242524742261) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_37 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7537360736068:ℝ):ℂ) + (((-0.6571772449985):ℝ):ℂ) * I)‖ ≤ 0.00000016351 := by
  have hl := lg_37
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.982549993943116598 50.982550022181158955 (-0.7170676) 0.0000000635 0.7537360736068 (-0.6571772449985) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_38 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4592936289743:ℝ):ℂ) + (((-0.8882845053155):ℝ):ℂ) * I)‖ ≤ 0.00000014531 := by
  have hl := lg_38
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.359078974496147757 51.359079002734190114 (-1.0935965) 0.0000000453 0.4592936289743 (-0.8882845053155) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_39 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.110227485005:ℝ):ℂ) + (((-0.993906384701):ℝ):ℂ) * I)‖ ≤ 0.00000013784 := by
  have hl := lg_39
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.725826867023789816 51.725826895261832173 (-1.4603444) 0.00000003783 0.110227485005 (-0.993906384701) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p119_40 : ‖exp (-((((((14119:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2445060744358):ℝ):ℂ) + (((-0.9696477605619):ℝ):ℂ) * I)‖ ≤ 0.00000016317 := by
  have hl := lg_40
  refine (ecis_approx ((((14119:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.083288994283816871 52.08328902958133099 (-1.8178066) 0.00000006316 (-0.2445060744358) (-0.9696477605619) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_2 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9248382703454):ℝ):ℂ) + ((0.3803605835965:ℝ):ℂ) * I)‖ ≤ 0.00000014133 := by
  have hl := lg_2
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.814964073048 9.814964080128 2.7514065 0.00000004132 (-0.9248382703454) 0.3803605835965 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_3 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9885287095867):ℝ):ℂ) + (((-0.1510330756206):ℝ):ℂ) * I)‖ ≤ 0.00000011051 := by
  have hl := lg_3
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.55635000385960224 15.5563500109396164 (-2.9899794) 0.0000000105 (-0.9885287095867) (-0.1510330756206) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_4 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7106517281761:ℝ):ℂ) + (((-0.7035439724995):ℝ):ℂ) * I)‖ ≤ 0.00000013873 := by
  have hl := lg_4
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.629928146096 19.629928160256 (-0.7803722) 0.00000003872 0.7106517281761 (-0.7035439724995) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_5 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6977875080939):ℝ):ℂ) + ((0.7163048188619:ℝ):ℂ) * I)‖ ≤ 0.00000011816 := by
  have hl := lg_5
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.78964083270519944 22.7896408468652136 2.3431004 0.00000001815 (-0.6977875080939) 0.7163048188619 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_6 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9716762110348:ℝ):ℂ) + (((-0.2363161884195):ℝ):ℂ) * I)‖ ≤ 0.00000015183 := by
  have hl := lg_6
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.37131407690760224 25.3713140910676164 (-0.2385729) 0.00000005182 0.9716762110348 (-0.2363161884195) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_7 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7516433964561):ℝ):ℂ) + (((-0.6595697116527):ℝ):ℂ) * I)‖ ≤ 0.00000012547 := by
  have hl := lg_7
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.55408770326157552 27.55408771742160384 (-2.4213465) 0.00000002546 (-0.7516433964561) (-0.6595697116527) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_8 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3896375191169):ℝ):ℂ) + ((0.9209682967906:ℝ):ℂ) * I)‖ ≤ 0.00000011677 := by
  have hl := lg_8
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.444892219144 29.444892240384 1.9710343 0.00000001676 (-0.3896375191169) 0.9209682967906 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_9 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9543780221667:ℝ):ℂ) + ((0.2986010562694:ℝ):ℂ) * I)‖ ≤ 0.00000012819 := by
  have hl := lg_9
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.11270000771920448 31.1127000218792328 0.3032265 0.00000002818 0.9543780221667 0.2986010562694 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_10 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.372886479755:ℝ):ℂ) + (((-0.9278769709481):ℝ):ℂ) * I)‖ ≤ 0.00000013016 := by
  have hl := lg_10
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.60460490575319944 32.6046049269932136 (-1.1886784) 0.00000003015 0.372886479755 (-0.9278769709481) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_11 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8234552348385):ℝ):ℂ) + (((-0.5673812441011):ℝ):ℂ) * I)‖ ≤ 0.00000013714 := by
  have hl := lg_11
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.95419705178242728 33.9541970730224556 (-2.5382705) 0.00000003713 (-0.8234552348385) (-0.5673812441011) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_12 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8087580418399):ℝ):ℂ) + ((0.5881415048325:ℝ):ℂ) * I)‖ ≤ 0.00000012813 := by
  have hl := lg_12
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.18627814995560224 35.1862781711956164 2.5128337 0.00000002812 (-0.8087580418399) 0.5881415048325 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_13 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1902015368924:ℝ):ℂ) + ((0.9817450663812:ℝ):ℂ) * I)‖ ≤ 0.00000015248 := by
  have hl := lg_13
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.319682890612872 36.31968291185290032 1.3794289 0.00000005247 0.1902015368924 0.9817450663812 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_14 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9460228668338:ℝ):ℂ) + ((0.3240998849545:ℝ):ℂ) * I)‖ ≤ 0.00000015449 := by
  have hl := lg_14
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.36905177630957552 37.36905179754960384 0.3300601 0.00000005448 0.9460228668338 0.3240998849545 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_15 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7979687050749:ℝ):ℂ) + (((-0.602698884785):ℝ):ℂ) * I)‖ ≤ 0.00000011474 := by
  have hl := lg_15
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.34599083656480168 38.34599085780483 (-0.646879) 0.00000001473 0.7979687050749 (-0.602698884785) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_16 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0100516575243:ℝ):ℂ) + (((-0.9999494808143):ℝ):ℂ) * I)‖ ≤ 0.0000001509 := by
  have hl := lg_16
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.259856292192 39.259856320512 (-1.5607445) 0.00000005089 0.0100516575243 (-0.9999494808143) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_17 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7502186926497):ℝ):ℂ) + (((-0.6611897709168):ℝ):ℂ) * I)‖ ≤ 0.00000012237 := by
  have hl := lg_17
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.11830093711270544 40.1183009654327196 (-2.4191891) 0.00000002236 (-0.7502186926497) (-0.6611897709168) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_18 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9962213998263):ℝ):ℂ) + ((0.0868499972858:ℝ):ℂ) * I)‖ ≤ 0.00000015177 := by
  have hl := lg_18
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.92766408076720448 40.9276641020072328 3.0546331 0.00000005176 (-0.9962213998263) 0.0868499972858 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_19 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6580641426601):ℝ):ℂ) + ((0.7529618742853:ℝ):ℂ) * I)‖ ≤ 0.00000011632 := by
  have hl := lg_19
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.69325593395429848 41.69325595519434096 2.2890412 0.00000001631 (-0.6580641426601) 0.7529618742853 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_20 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0080680392631:ℝ):ℂ) + ((0.9999674528415:ℝ):ℂ) * I)‖ ≤ 0.00000015688 := by
  have hl := lg_20
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.41956897880119944 42.4195690071212136 1.5627282 0.00000005687 0.0080680392631 0.9999674528415 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_21 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6434042401323:ℝ):ℂ) + ((0.7655266055336:ℝ):ℂ) * I)‖ ≤ 0.00000014315 := by
  have hl := lg_21
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.11043770712117776 43.11043772836122024 0.8718594 0.00000004314 0.6434042401323 0.7655266055336 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_22 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9773723763331:ℝ):ℂ) + ((0.2115259747193:ℝ):ℂ) * I)‖ ≤ 0.00000012544 := by
  have hl := lg_22
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.76916112483042728 43.7691611531504556 0.213136 0.00000002543 0.9773723763331 0.2115259747193 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_23 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9145910365179:ℝ):ℂ) + (((-0.4043800637038):ℝ):ℂ) * I)‖ ≤ 0.00000016091 := by
  have hl := lg_23
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.39859808283342256 44.39859811115346504 (-0.4163009) 0.0000000609 0.9145910365179 (-0.4043800637038) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_24 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5242645486328:ℝ):ℂ) + (((-0.851555449191):ℝ):ℂ) * I)‖ ≤ 0.00000012727 := by
  have hl := lg_24
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.00124222300360224 45.0012422513236164 (-1.0189451) 0.00000002726 0.5242645486328 (-0.851555449191) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_25 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0261851799105):ℝ):ℂ) + (((-0.9996571093894):ℝ):ℂ) * I)‖ ≤ 0.00000014349 := by
  have hl := lg_25
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.57928166541039888 45.5792816937304272 (-1.5969845) 0.00000004348 (-0.0261851799105) (-0.9996571093894) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_26 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5493226973153):ℝ):ℂ) + (((-0.8356103004425):ℝ):ℂ) * I)‖ ≤ 0.00000014174 := by
  have hl := lg_26
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.134646963660872 46.13464699198090032 (-2.1523498) 0.00000004173 (-0.5493226973153) (-0.8356103004425) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_27 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8983314388698):ℝ):ℂ) + (((-0.4393183649969):ℝ):ℂ) * I)‖ ≤ 0.00000013869 := by
  have hl := lg_27
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.66905001157880672 46.6690500328188492 (-2.6867529) 0.00000003868 (-0.8983314388698) (-0.4393183649969) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_28 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9981929730653):ℝ):ℂ) + ((0.0600898325102:ℝ):ℂ) * I)‖ ≤ 0.00000012026 := by
  have hl := lg_28
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.18401584935757552 47.18401587767760384 3.0814666 0.00000002025 (-0.9981929730653) 0.0600898325102 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_29 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8488347290052):ℝ):ℂ) + ((0.5286583043532:ℝ):ℂ) * I)‖ ≤ 0.00000011957 := by
  have hl := lg_29
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.68090893788515872 47.6809089662052012 2.5845735 0.00000001956 (-0.8488347290052) 0.5286583043532 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_30 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5087490974318):ℝ):ℂ) + ((0.860914836587:ℝ):ℂ) * I)‖ ≤ 0.00000014784 := by
  have hl := lg_30
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.16095490961280168 48.16095493793283 2.1045275 0.00000004783 (-0.5087490974318) 0.860914836587 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_31 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0693715117105):ℝ):ℂ) + ((0.9975908947874:ℝ):ℂ) * I)‖ ≤ 0.00000015667 := by
  have hl := lg_31
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.62525880078634008 48.62525882910638256 1.6402236 0.00000005666 (-0.0693715117105) 0.9975908947874 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_32 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3710451177488:ℝ):ℂ) + ((0.9286148397451:ℝ):ℂ) * I)‖ ≤ 0.00000014322 := by
  have hl := lg_32
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.07482036524 49.07482040064 1.1906621 0.00000004321 0.3710451177488 0.9286148397451 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_33 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7283158113111:ℝ):ℂ) + ((0.6852416208859:ℝ):ℂ) * I)‖ ≤ 0.00000012654 := by
  have hl := lg_33
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.51054705564202952 49.510547083962072 0.7549354 0.00000002653 0.7283158113111 0.6852416208859 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_34 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9453214853268:ℝ):ℂ) + ((0.3261399843311:ℝ):ℂ) * I)‖ ≤ 0.00000014729 := by
  have hl := lg_34
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.93326501016070544 49.9332650455607196 0.3322174 0.00000004728 0.9453214853268 0.3261399843311 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_35 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9969403354495:ℝ):ℂ) + (((-0.0781662814375):ℝ):ℂ) * I)‖ ≤ 0.00000012148 := by
  have hl := lg_35
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.34372853596677496 50.34372856428681744 (-0.0782461) 0.00000002147 0.9969403354495 (-0.0781662814375) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_36 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8883093641063:ℝ):ℂ) + (((-0.4592455483083):ℝ):ℂ) * I)‖ ≤ 0.00000012471 := by
  have hl := lg_36
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.74262815381520448 50.7426281821352328 (-0.4771457) 0.0000000247 0.8883093641063 (-0.4592455483083) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_37 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6485524332083:ℝ):ℂ) + (((-0.7611699819223):ℝ):ℂ) * I)‖ ≤ 0.00000012913 := by
  have hl := lg_37
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.13059762831889872 51.1305976566389412 (-0.8651152) 0.00000002912 0.6485524332083 (-0.7611699819223) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_38 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3222058923114:ℝ):ℂ) + (((-0.9466696165822):ℝ):ℂ) * I)‖ ≤ 0.00000015045 := by
  have hl := lg_38
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.50822000700229848 51.50822003532234096 (-1.2427376) 0.00000005044 0.3222058923114 (-0.9466696165822) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_39 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0397437028212):ℝ):ℂ) + (((-0.9992099069194):ℝ):ℂ) * I)‖ ≤ 0.00000016298 := by
  have hl := lg_39
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.87603289447247424 51.87603292279251672 (-1.6105505) 0.00000006297 (-0.0397437028212) (-0.9992099069194) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p16_40 : ‖exp (-((((((14160:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3878098288804):ℝ):ℂ) + (((-0.9217394081956):ℝ):ℂ) * I)‖ ≤ 0.00000012983 := by
  have hl := lg_40
  refine (ecis_approx ((((14160:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.23453305184919944 52.2345330872492136 (-1.9690506) 0.00000002982 (-0.3878098288804) (-0.9217394081956) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_2 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9136568150396):ℝ):ℂ) + ((0.4064864379018:ℝ):ℂ) * I)‖ ≤ 0.00000010693 := by
  have hl := lg_2
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.8433831074403 9.8433831145408 2.7229875 0.00000000692 (-0.9136568150396) 0.4064864379018 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_3 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9943267733518):ℝ):ℂ) + (((-0.1063685448406):ℝ):ℂ) * I)‖ ≤ 0.00000010669 := by
  have hl := lg_3
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.601393107684336964 15.601393114784851165 (-3.0350225) 0.00000000668 (-0.9943267733518) (-0.1063685448406) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_4 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6695375568203:ℝ):ℂ) + (((-0.7427782037776):ℝ):ℂ) * I)‖ ≤ 0.00000010756 := by
  have hl := lg_4
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.6867662148806 19.6867662290816 (-0.8372103) 0.00000000755 0.6695375568203 (-0.7427782037776) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_5 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6490363653452):ℝ):ℂ) + ((0.7607573834297:ℝ):ℂ) * I)‖ ≤ 0.00000014164 := by
  have hl := lg_5
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.855627787093682009 22.85562780129469621 2.2771134 0.00000004163 (-0.6490363653452) 0.7607573834297 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_6 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9517108040759:ℝ):ℂ) + (((-0.3069960022625):ℝ):ℂ) * I)‖ ≤ 0.00000011361 := by
  have hl := lg_6
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.444776215124636964 25.444776229325651165 (-0.312035) 0.0000000136 0.9517108040759 (-0.3069960022625) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_7 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8018186603451):ℝ):ℂ) + (((-0.5975674320714):ℝ):ℂ) * I)‖ ≤ 0.00000010938 := by
  have hl := lg_7
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.633870019351527822 27.633870033552556224 (-2.5011288) 0.00000000937 (-0.8018186603451) (-0.5975674320714) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_8 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3097982854837):ℝ):ℂ) + ((0.9508023045352:ℝ):ℂ) * I)‖ ≤ 0.00000011359 := by
  have hl := lg_8
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.5301493223209 29.5301493436224 1.8857772 0.00000001358 (-0.3097982854837) 0.9508023045352 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_9 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9773714667624:ℝ):ℂ) + ((0.2115301774185:ℝ):ℂ) * I)‖ ≤ 0.00000012054 := by
  have hl := lg_9
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.202786215368673928 31.20278622956970233 0.2131403 0.00000002053 0.9773714667624 0.2115301774185 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_10 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2837589463629:ℝ):ℂ) + (((-0.9588956462301):ℝ):ℂ) * I)‖ ≤ 0.00000014138 := by
  have hl := lg_10
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.699010894533982009 32.69901091583549621 (-1.2830844) 0.00000004137 0.2837589463629 (-0.9588956462301) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_11 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8751703844605):ℝ):ℂ) + (((-0.4838148386223):ℝ):ℂ) * I)‖ ≤ 0.00000014335 := by
  have hl := lg_11
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.052510757935187133 34.052510779236715535 (-2.6365842) 0.00000004334 (-0.8751703844605) (-0.4838148386223) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_12 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7447473506929):ℝ):ℂ) + ((0.6673465243809:ℝ):ℂ) * I)‖ ≤ 0.00000012053 := by
  have hl := lg_12
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.288159322564936964 35.288159343866451165 2.4109525 0.00000002052 (-0.7447473506929) 0.6673465243809 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_13 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2922037290662:ℝ):ℂ) + ((0.9563560951444:ℝ):ℂ) * I)‖ ≤ 0.00000012886 := by
  have hl := lg_13
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.4248458142368217 36.424845835538350102 1.274266 0.00000002885 0.2922037290662 0.9563560951444 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_14 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9754901404157:ℝ):ℂ) + ((0.2200431456595:ℝ):ℂ) * I)‖ ≤ 0.0000001163 := by
  have hl := lg_14
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.477253126791827822 37.477253148093356224 0.2218587 0.00000001629 0.9754901404157 0.2200431456595 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_15 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7262748910997:ℝ):ℂ) + (((-0.6874043806655):ℝ):ℂ) * I)‖ ≤ 0.00000014831 := by
  have hl := lg_15
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.457020894778018973 38.457020916079547375 (-0.7579091) 0.0000000483 0.7262748910997 (-0.6874043806655) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_16 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1034389200143):ℝ):ℂ) + (((-0.994635807633):ℝ):ℂ) * I)‖ ≤ 0.0000001151 := by
  have hl := lg_16
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.3735324297612 39.3735324581632 (-1.6744206) 0.00000001509 (-0.1034389200143) (-0.994635807633) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_17 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8217952013217):ℝ):ℂ) + (((-0.5697829823943):ℝ):ℂ) * I)‖ ≤ 0.00000015892 := by
  have hl := lg_17
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.234462684176379234 40.234462712578393435 (-2.5353509) 0.00000005891 (-0.8217952013217) (-0.5697829823943) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_18 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9789662496863):ℝ):ℂ) + ((0.2040222577497:ℝ):ℂ) * I)‖ ≤ 0.00000012746 := by
  have hl := lg_18
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.046169322808973928 41.04616934411050233 2.9361278 0.00000002745 (-0.9789662496863) 0.2040222577497 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_19 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5625962821523):ℝ):ℂ) + ((0.8267317722811:ℝ):ℂ) * I)‖ ≤ 0.0000001182 := by
  have hl := lg_19
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.813977932068149203 41.813977953369691806 2.1683192 0.00000001819 (-0.5625962821523) 0.8267317722811 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_20 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1305197804396:ℝ):ℂ) + ((0.9914457054796:ℝ):ℂ) * I)‖ ≤ 0.0000001483 := by
  have hl := lg_20
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.542394001974282009 42.54239403037629621 1.4399031 0.00000004829 0.1305197804396 0.9914457054796 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_21 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7337073880836:ℝ):ℂ) + ((0.6794655757811:ℝ):ℂ) * I)‖ ≤ 0.00000012324 := by
  have hl := lg_21
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.235263127035864786 43.235263148337407389 0.747034 0.00000002323 0.7337073880836 0.6794655757811 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_22 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9962695565526:ℝ):ℂ) + ((0.0862958323813:ℝ):ℂ) * I)‖ ≤ 0.00000014354 := by
  have hl := lg_22
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.895893865375487133 43.895893893777515535 0.0864033 0.00000004353 0.9962695565526 0.0862958323813 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_23 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8552018304603:ℝ):ℂ) + (((-0.5182951178405):ℝ):ℂ) * I)‖ ≤ 0.0000001238 := by
  have hl := lg_23
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.527153345643886566 44.527153374045929169 (-0.5448562) 0.00000002379 0.8552018304603 (-0.5182951178405) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_24 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.409176187433:ℝ):ℂ) + (((-0.9124553948757):ℝ):ℂ) * I)‖ ≤ 0.00000012027 := by
  have hl := lg_24
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.131542430005236964 45.131542458407251165 (-1.1492453) 0.00000002026 0.409176187433 (-0.9124553948757) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_25 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1575034870727):ℝ):ℂ) + (((-0.9875184309973):ℝ):ℂ) * I)‖ ≤ 0.00000015235 := by
  have hl := lg_25
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.711255574187364018 45.71125560258939242 (-1.7289584) 0.00000005234 (-0.1575034870727) (-0.9875184309973) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_26 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6557197055802):ℝ):ℂ) + (((-0.75500441568):ℝ):ℂ) * I)‖ ≤ 0.00000012859 := by
  have hl := lg_26
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.2682289216771217 46.268228950079150102 (-2.2859318) 0.00000002858 (-0.6557197055802) (-0.75500441568) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_27 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9493264598374):ℝ):ℂ) + (((-0.3142916996214):ℝ):ℂ) * I)‖ ≤ 0.00000012722 := by
  have hl := lg_27
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.804179323053010892 46.804179344354553495 (-2.8218822) 0.00000002721 (-0.9493264598374) (-0.3142916996214) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_28 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9807077691793):ℝ):ℂ) + ((0.1954795926496:ℝ):ℂ) * I)‖ ≤ 0.00000012322 := by
  have hl := lg_28
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.320636234232127822 47.320636262634156224 2.9448462 0.00000002321 (-0.9807077691793) 0.1954795926496 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_29 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.768003586974):ℝ):ℂ) + ((0.6404455405079:ℝ):ℂ) * I)‖ ≤ 0.00000013785 := by
  have hl := lg_29
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.818968066871973092 47.818968095274015695 2.4465144 0.00000003784 (-0.768003586974) 0.6404455405079 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_30 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3841454457314):ℝ):ℂ) + ((0.9232725905825:ℝ):ℂ) * I)‖ ≤ 0.00000015523 := by
  have hl := lg_30
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.300404002218318973 48.300404030620347375 1.9650784 0.00000005522 (-0.3841454457314) 0.9232725905825 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_31 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0713055627971:ℝ):ℂ) + ((0.9974545186193:ℝ):ℂ) * I)‖ ≤ 0.00000014711 := by
  have hl := lg_31
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.766052276127599963 48.766052304529642566 1.4994302 0.0000000471 0.0713055627971 0.9974545186193 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_32 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4988136407413:ℝ):ℂ) + ((0.8667092660232:ℝ):ℂ) * I)‖ ≤ 0.00000012025 := by
  have hl := lg_32
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.2169155372015 49.216915572704 1.0485669 0.00000002024 0.4988136407413 0.8667092660232 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_33 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8187426683764:ℝ):ℂ) + ((0.5741606421377:ℝ):ℂ) * I)‖ ≤ 0.0000001366 := by
  have hl := lg_33
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.653903865619524097 49.6539038940215667 0.6115786 0.00000003659 0.8187426683764 0.5741606421377 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_34 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9824478412447:ℝ):ℂ) + ((0.1865375008773:ℝ):ℂ) * I)‖ ≤ 0.00000016584 := by
  have hl := lg_34
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.077845791616679234 50.077845827119193435 0.1876366 0.00000006583 0.9824478412447 0.1865375008773 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_35 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9750133050568:ℝ):ℂ) + (((-0.2221464718652):ℝ):ℂ) * I)‖ ≤ 0.00000015101 := by
  have hl := lg_35
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.489497806445209831 50.489497834847252434 (-0.2240154) 0.000000051 0.9750133050568 (-0.2221464718652) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_36 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8115069091896:ℝ):ℂ) + (((-0.5843428243227):ℝ):ℂ) * I)‖ ≤ 0.0000001272 := by
  have hl := lg_36
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.889552430249273928 50.88955245865130233 (-0.62407) 0.00000002719 0.8115069091896 (-0.5843428243227) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_37 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5291797059016:ℝ):ℂ) + (((-0.8485097753484):ℝ):ℂ) * I)‖ ≤ 0.00000013368 := by
  have hl := lg_37
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.278645262694680842 51.278645291096723445 (-1.0131628) 0.00000003367 0.5291797059016 (-0.8485097753484) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_38 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1779646811169:ℝ):ℂ) + (((-0.984036875465):ℝ):ℂ) * I)‖ ≤ 0.00000011794 := by
  have hl := lg_38
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.657361039508449203 51.657361067910491806 (-1.3918786) 0.00000001793 0.1779646811169 (-0.984036875465) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_39 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1888197847456):ℝ):ℂ) + (((-0.9820117559825):ℝ):ℂ) * I)‖ ≤ 0.00000013553 := by
  have hl := lg_39
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.026238921921158664 52.026238950323201267 (-1.7607565) 0.00000003552 (-0.1888197847456) (-0.9820117559825) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p201_40 : ‖exp (-((((((14201:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.522259514043):ℝ):ℂ) + (((-0.8527866087037):ℝ):ℂ) * I)‖ ≤ 0.00000014804 := by
  have hl := lg_40
  refine (ecis_approx ((((14201:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.385777109414582009 52.38577714491709621 (-2.1202947) 0.00000004803 (-0.522259514043) (-0.8527866087037) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_2 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9017375040058):ℝ):ℂ) + ((0.4322840197728:ℝ):ℂ) * I)‖ ≤ 0.00000013461 := by
  have hl := lg_2
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.8718021418326 9.8718021489536 2.6945685 0.0000000346 (-0.9017375040058) 0.4322840197728 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_3 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9981078076119):ℝ):ℂ) + (((-0.0614882414372):ℝ):ℂ) * I)‖ ≤ 0.00000010429 := by
  have hl := lg_3
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.646436211509071688 15.64643621863008593 (-3.0800656) 0.00000000428 (-0.9981078076119) (-0.0614882414372) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_4 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6262609800238:ℝ):ℂ) + (((-0.7796134842983):ℝ):ℂ) * I)‖ ≤ 0.00000013789 := by
  have hl := lg_4
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.7436042836652 19.7436042979072 (-0.8940484) 0.00000003788 0.6262609800238 (-0.7796134842983) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_5 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5974602393324):ℝ):ℂ) + ((0.8018985362282:ℝ):ℂ) * I)‖ ≤ 0.00000012702 := by
  have hl := lg_5
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.921614741482164578 22.92161475572417882 2.2111265 0.00000002701 (-0.5974602393324) 0.8018985362282 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_6 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9266116277242:ℝ):ℂ) + (((-0.3760198018275):ℝ):ℂ) * I)‖ ≤ 0.00000013888 := by
  have hl := lg_6
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.518238353341671688 25.51823836758368593 (-0.3854971) 0.00000003887 0.9266116277242 (-0.3760198018275) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_7 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8468928823824):ℝ):ℂ) + (((-0.5317635242268):ℝ):ℂ) * I)‖ ≤ 0.00000012098 := by
  have hl := lg_7
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.713652335441480124 27.713652349683508608 (-2.5809111) 0.00000002097 (-0.8468928823824) (-0.5317635242268) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_8 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2277085620936):ℝ):ℂ) + ((0.9737293313587:ℝ):ℂ) * I)‖ ≤ 0.00000011098 := by
  have hl := lg_8
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.6154064254978 29.6154064468608 1.8005201 0.00000001097 (-0.2277085620936) 0.9737293313587 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_9 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.992438393149:ℝ):ℂ) + ((0.122743781121:ℝ):ℂ) * I)‖ ≤ 0.00000011289 := by
  have hl := lg_9
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.292872423018143376 31.29287243726017186 0.1230541 0.00000001288 0.992438393149 0.122743781121 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_10 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1921042911438:ℝ):ℂ) + (((-0.9813745163413):ℝ):ℂ) * I)‖ ≤ 0.0000001526 := by
  have hl := lg_10
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.793416883314764578 32.79341690467777882 (-1.3774904) 0.00000005259 0.1921042911438 (-0.9813745163413) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_11 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9184333128147):ℝ):ℂ) + (((-0.395575845789):ℝ):ℂ) * I)‖ ≤ 0.00000014957 := by
  have hl := lg_11
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.150824464087946986 34.15082448545097547 (-2.7348979) 0.00000004956 (-0.9184333128147) (-0.395575845789) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_12 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6730130309617):ℝ):ℂ) + ((0.7396306241199:ℝ):ℂ) * I)‖ ≤ 0.00000014792 := by
  have hl := lg_12
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.390040495174271688 35.39004051653728593 2.3090713 0.00000004791 (-0.6730130309617) 0.7396306241199 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_13 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3909773484838:ℝ):ℂ) + ((0.9204003003979:ℝ):ℂ) * I)‖ ≤ 0.00000011616 := by
  have hl := lg_13
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.5300087378607714 36.530008759223799884 1.1691031 0.00000001615 0.3909773484838 0.9204003003979 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_14 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9935479478377:ℝ):ℂ) + ((0.1134128535372:ℝ):ℂ) * I)‖ ≤ 0.00000015557 := by
  have hl := lg_14
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.585454477274080124 37.585454498637108608 0.1136574 0.00000005556 0.9935479478377 0.1134128535372 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_15 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6456370607782:ℝ):ℂ) + (((-0.7636444105404):ℝ):ℂ) * I)‖ ≤ 0.00000013129 := by
  have hl := lg_15
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.568050952991236266 38.56805097435426475 (-0.8689391) 0.00000003128 0.6456370607782 (-0.7636444105404) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_16 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2155942721512):ℝ):ℂ) + (((-0.9764830309916):ℝ):ℂ) * I)‖ ≤ 0.00000015275 := by
  have hl := lg_16
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.4872085673304 39.4872085958144 (-1.7880967) 0.00000005274 (-0.2155942721512) (-0.9764830309916) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_17 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.882295180464):ℝ):ℂ) + (((-0.4706965205222):ℝ):ℂ) * I)‖ ≤ 0.00000011666 := by
  have hl := lg_17
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.350624431240053028 40.35062445972406727 (-2.6515126) 0.00000001665 (-0.882295180464) (-0.4706965205222) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_18 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9479790945955):ℝ):ℂ) + ((0.3183325871031:ℝ):ℂ) * I)‖ ≤ 0.00000013597 := by
  have hl := lg_18
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.164674564850743376 41.16467458621377186 2.8176226 0.00000003596 (-0.9479790945955) 0.3183325871031 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_19 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4589392081401):ℝ):ℂ) + ((0.8884676714585:ℝ):ℂ) * I)‖ ≤ 0.00000012009 := by
  have hl := lg_19
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.934699930181999926 41.934699951545042652 2.0475972 0.00000002008 (-0.4589392081401) 0.8884676714585 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_20 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2510048768777:ℝ):ℂ) + ((0.9679858220984:ℝ):ℂ) * I)‖ ≤ 0.00000012512 := by
  have hl := lg_20
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.665219025147364578 42.66521905363137882 1.3170781 0.00000002511 0.2510048768777 0.9679858220984 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_21 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8125931984365:ℝ):ℂ) + ((0.5828312739161:ℝ):ℂ) * I)‖ ≤ 0.00000011807 := by
  have hl := lg_21
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.360088546950551812 43.360088568313594538 0.6222086 0.00000001806 0.8125931984365 0.5828312739161 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_22 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9991868759339:ℝ):ℂ) + (((-0.040318568445):ℝ):ℂ) * I)‖ ≤ 0.00000014435 := by
  have hl := lg_22
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.022626605920546986 44.02262663440457547 (-0.0403295) 0.00000004434 0.9991868759339 (-0.040318568445) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_23 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7816986151113:ℝ):ℂ) + (((-0.6236563758458):ℝ):ℂ) * I)‖ ≤ 0.00000014182 := by
  have hl := lg_23
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.655708608454350572 44.655708636938393298 (-0.6734115) 0.00000004181 0.7816986151113 (-0.6236563758458) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_24 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.287150598212:ℝ):ℂ) + (((-0.9578854492821):ℝ):ℂ) * I)‖ ≤ 0.00000011525 := by
  have hl := lg_24
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.261842637006871688 45.26184266549088593 (-1.2795455) 0.00000001524 0.287150598212 (-0.9578854492821) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_25 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2860825179521):ℝ):ℂ) + (((-0.9582049848131):ℝ):ℂ) * I)‖ ≤ 0.00000016121 := by
  have hl := lg_25
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.843229482964329156 45.84322951144835764 (-1.8609323) 0.0000000612 (-0.2860825179521) (-0.9582049848131) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_26 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7504332753221):ℝ):ℂ) + (((-0.6609462151003):ℝ):ℂ) * I)‖ ≤ 0.00000015794 := by
  have hl := lg_26
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.4018108796933714 46.401810908177399884 (-2.4195137) 0.00000005793 (-0.7504332753221) (-0.6609462151003) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_27 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9830132096101):ℝ):ℂ) + (((-0.1835348179156):ℝ):ℂ) * I)‖ ≤ 0.00000011574 := by
  have hl := lg_27
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.939308634527215064 46.93930865589025779 (-2.9570115) 0.00000001573 (-0.9830132096101) (-0.1835348179156) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_28 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9449459780672):ℝ):ℂ) + ((0.3272263717121:ℝ):ℂ) * I)‖ ≤ 0.00000013835 := by
  have hl := lg_28
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.457256619106680124 47.457256647590708608 2.8082258 0.00000003834 (-0.9449459780672) 0.3272263717121 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_29 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6725572168321):ℝ):ℂ) + ((0.7400451270479:ℝ):ℂ) * I)‖ ≤ 0.00000016159 := by
  have hl := lg_29
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.957027195858787464 47.95702722434283019 2.3084552 0.00000006158 (-0.6725572168321) 0.7400451270479 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_30 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2520837794179):ℝ):ℂ) + ((0.9677054139319:ℝ):ℂ) * I)‖ ≤ 0.00000016263 := by
  have hl := lg_30
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.439853094823836266 48.43985312330786475 1.8256293 0.00000006262 (-0.2520837794179) 0.9677054139319 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_31 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2105715938469:ℝ):ℂ) + ((0.9775784387274:ℝ):ℂ) * I)‖ ≤ 0.00000012253 := by
  have hl := lg_31
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.906845751468859846 48.906845779952902572 1.3586367 0.00000002252 0.2105715938469 0.9775784387274 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_32 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6165275295279:ℝ):ℂ) + ((0.7873333508332:ℝ):ℂ) * I)‖ ≤ 0.00000014829 := by
  have hl := lg_32
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.359010709163 49.359010744768 0.9064717 0.00000004828 0.6165275295279 0.7873333508332 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_33 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8923722005966:ℝ):ℂ) + ((0.4513001834725:ℝ):ℂ) * I)‖ ≤ 0.00000014666 := by
  have hl := lg_33
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.797260675597018674 49.7972607040810614 0.4682218 0.00000004665 0.8923722005966 0.4513001834725 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_34 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.999073237921:ℝ):ℂ) + ((0.0430425983196:ℝ):ℂ) * I)‖ ≤ 0.00000015126 := by
  have hl := lg_34
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.222426573072653028 50.22242660867766727 0.0430559 0.00000005125 0.999073237921 0.0430425983196 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_35 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9324052159408:ℝ):ℂ) + (((-0.3614146002673):ℝ):ℂ) * I)‖ ≤ 0.00000014799 := by
  have hl := lg_35
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.635267076923644702 50.635267105407687428 (-0.3697846) 0.00000004798 0.9324052159408 (-0.3614146002673) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_36 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7172181475823:ℝ):ℂ) + (((-0.6968487129776):ℝ):ℂ) * I)‖ ≤ 0.00000015077 := by
  have hl := lg_36
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.036476706683343376 51.03647673516737186 (-0.7709943) 0.00000005076 0.7172181475823 (-0.6968487129776) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_37 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.398229446936:ℝ):ℂ) + (((-0.9172858374536):ℝ):ℂ) * I)‖ ≤ 0.00000016038 := by
  have hl := lg_37
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.426692897070462964 51.42669292555450569 (-1.1612105) 0.00000006037 0.398229446936 (-0.9172858374536) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_38 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.029772326717:ℝ):ℂ) + (((-0.9995567060261):ℝ):ℂ) * I)‖ ≤ 0.00000014308 := by
  have hl := lg_38
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.806502072014599926 51.806502100498642652 (-1.5410196) 0.00000004307 0.029772326717 (-0.9995567060261) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_39 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3336437481002):ℝ):ℂ) + (((-0.9426992358921):ℝ):ℂ) * I)‖ ≤ 0.00000012043 := by
  have hl := lg_39
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.176444949369843088 52.176444977853885814 (-1.9109625) 0.00000002042 (-0.3336437481002) (-0.9426992358921) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p242_40 : ‖exp (-((((((14242:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6447853080099):ℝ):ℂ) + (((-0.7643637266108):ℝ):ℂ) * I)‖ ≤ 0.00000014516 := by
  have hl := lg_40
  refine (ecis_approx ((((14242:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.537021166979964578 52.53702120258497882 (-2.2715387) 0.00000004515 (-0.6447853080099) (-0.7643637266108) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_2 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8890899173304):ℝ):ℂ) + ((0.4577325843729:ℝ):ℂ) * I)‖ ≤ 0.00000013815 := by
  have hl := lg_2
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.9002211762249 9.9002211833664 2.6661494 0.00000003814 (-0.8890899173304) 0.4577325843729 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_3 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998641423942):ℝ):ℂ) + (((-0.0164832068046):ℝ):ℂ) * I)‖ ≤ 0.00000010813 := by
  have hl := lg_3
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.691479315333806412 15.691479322475320695 (-3.1251087) 0.00000000812 (-0.9998641423942) (-0.0164832068046) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
